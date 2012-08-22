/*  Title:      Pure/Thy/thy_header.scala
    Author:     Makarius

Static theory header information.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.parsing.input.{Reader, CharSequenceReader}
import scala.util.matching.Regex

import java.io.{File => JFile}


object Thy_Header extends Parse.Parser
{
  val HEADER = "header"
  val THEORY = "theory"
  val IMPORTS = "imports"
  val KEYWORDS = "keywords"
  val AND = "and"
  val USES = "uses"
  val BEGIN = "begin"

  private val lexicon =
    Scan.Lexicon("%", "(", ")", ",", "::", ";", AND, BEGIN, HEADER, IMPORTS, KEYWORDS, THEORY, USES)


  /* theory file name */

  private val Base_Name = new Regex(""".*?([^/\\:]+)""")
  private val Thy_Name = new Regex(""".*?([^/\\:]+)\.thy""")

  def base_name(s: String): String =
    s match { case Base_Name(name) => name case _ => error("Malformed import: " + quote(s)) }

  def thy_name(s: String): Option[String] =
    s match { case Thy_Name(name) => Some(name) case _ => None }


  /* header */

  val header: Parser[Thy_Header] =
  {
    val file_name = atom("file name", _.is_name)

    val opt_files =
      keyword("(") ~! (rep1sep(name, keyword(",")) <~ keyword(")")) ^^ { case _ ~ x => x } |
      success(Nil)
    val keyword_spec =
      atom("outer syntax keyword specification", _.is_name) ~ opt_files ~ tags ^^
      { case x ~ y ~ z => ((x, y), z) }

    val keyword_decl =
      rep1(string) ~ opt(keyword("::") ~! keyword_spec ^^ { case _ ~ x => x }) ^^
      { case xs ~ y => xs.map((_, y)) }
    val keyword_decls =
      keyword_decl ~ rep(keyword(AND) ~! keyword_decl ^^ { case _ ~ x => x }) ^^
      { case xs ~ yss => (xs :: yss).flatten }

    val file =
      keyword("(") ~! (file_name ~ keyword(")")) ^^ { case _ ~ (x ~ _) => (x, false) } |
      file_name ^^ (x => (x, true))

    val args =
      theory_name ~
      (opt(keyword(IMPORTS) ~! (rep1(theory_name))) ^^ { case None => Nil case Some(_ ~ xs) => xs }) ~
      (opt(keyword(KEYWORDS) ~! keyword_decls) ^^ { case None => Nil case Some(_ ~ xs) => xs }) ~
      (opt(keyword(USES) ~! (rep1(file))) ^^ { case None => Nil case Some(_ ~ xs) => xs }) ~
      keyword(BEGIN) ^^
      { case x ~ ys ~ zs ~ ws ~ _ => Thy_Header(x, ys, zs, ws) }

    (keyword(HEADER) ~ tags) ~!
      ((doc_source ~ rep(keyword(";")) ~ keyword(THEORY) ~ tags) ~> args) ^^ { case _ ~ x => x } |
    (keyword(THEORY) ~ tags) ~! args ^^ { case _ ~ x => x }
  }


  /* read -- lazy scanning */

  def read(reader: Reader[Char]): Thy_Header =
  {
    val token = lexicon.token(_ => false)
    val toks = new mutable.ListBuffer[Token]

    @tailrec def scan_to_begin(in: Reader[Char])
    {
      token(in) match {
        case lexicon.Success(tok, rest) =>
          toks += tok
          if (!tok.is_begin) scan_to_begin(rest)
        case _ =>
      }
    }
    scan_to_begin(reader)

    parse(commit(header), Token.reader(toks.toList)) match {
      case Success(result, _) => result
      case bad => error(bad.toString)
    }
  }

  def read(source: CharSequence): Thy_Header =
    read(new CharSequenceReader(source))


  /* keywords */

  type Keywords = List[(String, Option[((String, List[String]), List[String])])]
}


sealed case class Thy_Header(
  name: String, imports: List[String],
  keywords: Thy_Header.Keywords,
  uses: List[(String, Boolean)])
{
  def map(f: String => String): Thy_Header =
    Thy_Header(f(name), imports.map(f), keywords, uses.map(p => (f(p._1), p._2)))
}

