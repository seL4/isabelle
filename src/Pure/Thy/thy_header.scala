/*  Title:      Pure/Thy/thy_header.scala
    Author:     Makarius

Theory headers -- independent of outer syntax.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.parsing.input.{Reader, CharSequenceReader}
import scala.util.matching.Regex

import java.io.File


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
    Scan.Lexicon("%", "(", ")", "::", ";", AND, BEGIN, HEADER, IMPORTS, KEYWORDS, THEORY, USES)


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
    val theory_name = atom("theory name", _.is_name)

    val keyword_kind =
      atom("outer syntax keyword kind", _.is_name) ~ tags ^^ { case x ~ y => (x, y) }
    val keyword_decl =
      name ~ opt(keyword("::") ~! keyword_kind ^^ { case _ ~ x => x }) ^^
      { case x ~ y => (x, y) }
    val keywords =
      keyword_decl ~ rep(keyword(AND) ~! keyword_decl ^^ { case _ ~ x => x }) ^^
      { case x ~ ys => x :: ys }

    val file =
      keyword("(") ~! (file_name ~ keyword(")")) ^^ { case _ ~ (x ~ _) => (x, false) } |
      file_name ^^ (x => (x, true))

    val args =
      theory_name ~
      (keyword(IMPORTS) ~! (rep1(theory_name)) ^^ { case _ ~ xs => xs }) ~
      (opt(keyword(KEYWORDS) ~! keywords) ^^ { case None => Nil case Some(_ ~ xs) => xs }) ~
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

  def read(file: File): Thy_Header =
  {
    val reader = Scan.byte_reader(file)
    try { read(reader).map(Standard_System.decode_permissive_utf8) }
    finally { reader.close }
  }
}


sealed case class Thy_Header(
  name: String, imports: List[String],
  keywords: List[(String, Option[(String, List[String])])],
  uses: List[(String, Boolean)])
{
  def map(f: String => String): Thy_Header =
    Thy_Header(f(name), imports.map(f), keywords, uses.map(p => (f(p._1), p._2)))
}

