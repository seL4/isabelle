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


object Thy_Header
{
  val HEADER = "header"
  val THEORY = "theory"
  val IMPORTS = "imports"
  val USES = "uses"
  val BEGIN = "begin"

  val lexicon = Scan.Lexicon("%", "(", ")", ";", BEGIN, HEADER, IMPORTS, THEORY, USES)

  final case class Header(val name: String, val imports: List[String], val uses: List[String])
  {
    def decode_permissive_utf8: Header =
      Header(Standard_System.decode_permissive_utf8(name),
        imports.map(Standard_System.decode_permissive_utf8),
        uses.map(Standard_System.decode_permissive_utf8))
  }


  /* file name */

  def thy_path(name: String): Path = Path.basic(name).ext("thy")

  private val Thy_Path1 = new Regex("([^/]*)\\.thy")
  private val Thy_Path2 = new Regex("(.*)/([^/]*)\\.thy")

  def split_thy_path(path: String): Option[(String, String)] =
    path match {
      case Thy_Path1(name) => Some(("", name))
      case Thy_Path2(dir, name) => Some((dir, name))
      case _ => None
    }
}


class Thy_Header(symbols: Symbol.Interpretation) extends Parse.Parser
{
  import Thy_Header._


  /* header */

  val header: Parser[Header] =
  {
    val file_name = atom("file name", _.is_name)
    val theory_name = atom("theory name", _.is_name)

    val file =
      keyword("(") ~! (file_name ~ keyword(")")) ^^ { case _ ~ (x ~ _) => x } | file_name

    val uses = opt(keyword(USES) ~! (rep1(file))) ^^ { case None => Nil case Some(_ ~ xs) => xs }

    val args =
      theory_name ~ (keyword(IMPORTS) ~! (rep1(theory_name) ~ uses ~ keyword(BEGIN))) ^^
        { case x ~ (_ ~ (ys ~ zs ~ _)) => Header(x, ys, zs) }

    (keyword(HEADER) ~ tags) ~!
      ((doc_source ~ rep(keyword(";")) ~ keyword(THEORY) ~ tags) ~> args) ^^ { case _ ~ x => x } |
    (keyword(THEORY) ~ tags) ~! args ^^ { case _ ~ x => x }
  }


  /* read -- lazy scanning */

  def read(reader: Reader[Char]): Header =
  {
    val token = lexicon.token(symbols, _ => false)
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

  def read(source: CharSequence): Header =
    read(new CharSequenceReader(source))

  def read(file: File): Header =
  {
    val reader = Scan.byte_reader(file)
    try { read(reader).decode_permissive_utf8 }
    finally { reader.close }
  }


  /* check */

  def check(name: String, source: CharSequence): Header =
  {
    val header = read(source)
    val name1 = header.name
    if (name == name1) header
    else error("Bad file name " + Thy_Header.thy_path(name) + " for theory " + quote(name1))
  }
}
