/*  Title:      Pure/Tools/prismjs.scala
    Author:     Makarius

Support for the Prism.js syntax highlighter -- via external Node.js process.
*/

package isabelle

import scala.collection.mutable


object Prismjs {
  /* component resources */

  val HOME: Path = Path.explode("$ISABELLE_PRISMJS_HOME")

  lazy val available_languages: List[String] = {
    val components_path = HOME + Path.explode("components.json")
    val components_json = JSON.parse(File.read(components_path))
    JSON.value(components_json, "languages") match {
      case Some(JSON.Object(langs)) =>
        (for ((lang, JSON.Object(info)) <- langs.iterator if lang != "meta") yield {
          val alias =
            JSON.Value.List.unapply(info.getOrElse("alias", Nil), JSON.Value.String.unapply)
              .getOrElse(Nil)
          lang :: alias
        }).toList.flatten.sorted
      case _ => error("Failed to determine languages from " + components_path)
    }
  }


  /* JavaScript prelude */

  def prelude(lang: JS.Source): JS.Source =
    cat_lines(List(
      Nodejs.require_fs,
      Nodejs.require_path("prismjs", HOME),
      Nodejs.require_path("prismjs_load", HOME + Path.explode("components"), dir = true),
      JS.function("prismjs_load", lang),
      """
function prismjs_content(t) {
  if (Array.isArray(t)) { return t.map(prismjs_content).join() }
  else if (t instanceof prismjs.Token) { return prismjs_content(t.content) }
  else { return t }
}

function prismjs_tokenize(text, lang) {
  return prismjs.tokenize(text, prismjs.languages[lang]).map(function (t) {
    if (t instanceof prismjs.Token) {
      return {"kind": t.type, "content": prismjs_content(t)}
    }
    else { return {"kind": "", "content": t} }
  })
}
"""))


  /* tokenize */

  sealed case class Token(
    kind: String,
    content: String,
    range: Text.Range = Text.Range.zero)

  def tokenize(text: String, language: String): List[Token] = {
    if (!available_languages.contains(language)) {
      error("Unknown language " + quote(language))
    }

    val json =
      Isabelle_System.with_tmp_file("input", ext = "json") { input =>
        Isabelle_System.with_tmp_file("output", ext = "json") { output =>
          File.write(input, text)
          val lang = JS.value(language)
          Nodejs.execute(
            prelude(lang) + "\n" +
            Nodejs.write_file(output,
              JS.json_print(JS.function("prismjs_tokenize", Nodejs.read_file(input), lang))))
          JSON.parse(File.read(output))
        }
      }

    def parse_token(t: JSON.T): Token =
      (for {
        kind <- JSON.string(t, "kind")
        content <- JSON.string(t, "content")
      } yield Token(kind, content)).getOrElse(error("Malformed JSON token: " + t))

    val tokens0 =
      JSON.Value.List.unapply(json, t => Some(parse_token(t)))
        .getOrElse(error("Malformed JSON: array expected"))

    var stop = 0
    val tokens = new mutable.ListBuffer[Token]
    for (tok <- tokens0) {
      val start = stop
      stop += tok.content.length
      if (tok.kind.nonEmpty) {
        tokens += tok.copy(range = Text.Range(start, stop))
      }
    }
    tokens.toList
  }
}
