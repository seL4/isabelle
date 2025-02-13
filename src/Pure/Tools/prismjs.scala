/*  Title:      Pure/Tools/prismjs.scala
    Author:     Makarius

Support for the Prism.js syntax highlighter -- via external Node.js process.
*/

package isabelle


object Prismjs {
  /* component resources */

  val HOME: Path = Path.explode("$ISABELLE_PRISMJS_HOME")

  sealed case class Language(names: List[String]) {
    require(names.nonEmpty)

    def name: String = names.head
    def alias: List[String] = names.tail
    override def toString: String = name
  }

  lazy val languages: List[Language] = {
    val components_path = HOME + Path.explode("components.json")
    val components_json = JSON.parse(File.read(components_path))
    JSON.value(components_json, "languages") match {
      case Some(JSON.Object(langs)) =>
        (for (case (name, JSON.Object(info)) <- langs.iterator if name != "meta") yield {
          val alias =
            JSON.Value.List.unapply(info.getOrElse("alias", Nil), JSON.Value.String.unapply)
              .getOrElse(Nil)
          Language(name :: alias)
        }).toList.sortBy(_.name)
      case _ => error("Failed to determine languages from " + components_path)
    }
  }

  def check_language(name: String): Unit =
    if (!languages.exists(_.names.contains(name))) error("Unknown language " + quote(name))


  /* generate JavaScript */

  def prelude(lang: JS.Source): JS.Source =
    cat_lines(List(
      Nodejs.require_fs,
      Nodejs.require_path("const prismjs", HOME),
      Nodejs.require_path("prismjs.load", HOME + Path.explode("components"), dir = true),
      JS.function("prismjs.load", lang),
      """
function prismjs_encode(t) {
  if (t instanceof prismjs.Token) {
    var types = [t.type]
    if (Array.isArray(t.alias)) { for (a of t.alias) { types.push(a) } }
    else if (t.alias !== undefined) { types.push(t.alias) }
    return {"types": types, "content": prismjs_encode(t.content) }
  }
  else if (Array.isArray(t)) { return t.map(prismjs_encode) }
  else { return t }
}

function prismjs_tokenize(text, lang) {
  return prismjs.tokenize(text, prismjs.languages[lang]).map(prismjs_encode)
}
"""))

  def main(lang: JS.Source, input: Path, output: Path): JS.Source =
    Nodejs.write_file(output,
      JS.json_print(JS.function("prismjs_tokenize", Nodejs.read_file(input), lang)))


  /* tokenize */

  sealed case class Token(types: List[String], content: Content) {
    def string: String = content.string
    def yxml: String = YXML.string_of_body(Encode.token(this))
  }
  sealed abstract class Content { def string: String }
  case class Atom(string: String) extends Content
  case class Nested(tokens: List[Token]) extends Content {
    def string: String = tokens.map(_.string).mkString
  }

  object Encode {
    import XML.Encode._
    def token(tok: Token): XML.Body =
      pair(list(string), content)(tok.types, tok.content)
    def content: T[Content] = {
      variant[Content](List(
        { case Atom(a) => (List(a), Nil) },
        { case Nested(a) => (Nil, list(token)(a)) }
      ))
    }
  }

  def decode(json: JSON.T): Option[Token] =
    JSON.Value.String.unapply(json).map(string => Token(Nil, Atom(string))) orElse
      (for {
        types <- JSON.strings(json, "types")
        content_json <- JSON.value(json, "content")
        content <-
          JSON.Value.String.unapply(content_json).map(Atom.apply) orElse
          JSON.Value.List.unapply(content_json, decode).map(Nested.apply)
      } yield Token(types, content))

  def tokenize(text: String, language: String): List[Token] = {
    check_language(language)

    val json =
      Isabelle_System.with_tmp_file("input", ext = "json") { input =>
        Isabelle_System.with_tmp_file("output", ext = "json") { output =>
          File.write(input, text)
          val lang = JS.value(language)
          Nodejs.execute(prelude(lang) + "\n" + main(lang, input, output))
          JSON.parse(File.read(output))
        }
      }

    JSON.Value.List.unapply(json, decode).getOrElse(error("Malformed JSON: " + json))
  }


  /* Scala functions in ML */

  object Languages extends Scala.Fun_Strings("Prismjs.languages") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] =
      languages.map(language => cat_lines(language.names))
  }

  object Tokenize extends Scala.Fun_Strings("Prismjs.tokenize", thread = true) {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] =
      args match {
        case List(text, language) => tokenize(text, language).map(_.yxml)
        case _ => error("Bad arguments")
      }
  }
}