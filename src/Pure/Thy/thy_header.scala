/*  Title:      Pure/Thy/thy_header.scala
    Author:     Makarius

Theory headers -- independent of outer syntax.
*/

package isabelle


import scala.collection.mutable
import scala.util.parsing.input.{Reader, CharSequenceReader}

import java.io.File


object Thy_Header
{
  val HEADER = "header"
  val THEORY = "theory"
  val IMPORTS = "imports"
  val USES = "uses"
  val BEGIN = "begin"

  val lexicon = Scan.Lexicon("%", "(", ")", ";", BEGIN, HEADER, IMPORTS, THEORY, USES)

  sealed case class Header(val name: String, val imports: List[String], val uses: List[String])
}


class Thy_Header(symbols: Symbol.Interpretation) extends Outer_Parse.Parser
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

  def read(file: File): Header =
  {
    val token = lexicon.token(symbols, _ => false)
    val toks = new mutable.ListBuffer[Outer_Lex.Token]

    def scan_to_begin(in: Reader[Char])
    {
      token(in) match {
        case lexicon.Success(tok, rest) =>
          toks += tok
          if (!(tok.kind == Outer_Lex.Token_Kind.KEYWORD && tok.content == BEGIN))
            scan_to_begin(rest)
        case _ =>
      }
    }
    val reader = Scan.byte_reader(file)
    try { scan_to_begin(reader) } finally { reader.close }

    parse(commit(header), Outer_Lex.reader(toks.toList)) match {
      case Success(result, _) => result
      case bad => error(bad.toString)
    }
  }
}
