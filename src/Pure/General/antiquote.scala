/*  Title:      Pure/ML/antiquote.scala
    Author:     Makarius

Antiquotations within plain text.
*/

package isabelle


import scala.util.parsing.input.CharSequenceReader


object Antiquote
{
  sealed abstract class Antiquote
  case class Text(source: String) extends Antiquote
  case class Antiq(source: String) extends Antiquote


  /* parsers */

  object Parsers extends Parsers

  trait Parsers extends Scan.Parsers
  {
    private val txt: Parser[String] =
      rep1("@" ~ guard(one(s => s != "{")) | many1(s => s != "@")) ^^ (x => x.mkString)

    private val ant: Parser[String] =
      quoted("\"") | (quoted("`") | (cartouche | one(s => s != "}")))

    val antiq: Parser[String] =
      "@{" ~ rep(ant) ~ "}" ^^ { case x ~ y ~ z => x + y.mkString + z }

    val text: Parser[Antiquote] =
      antiq ^^ (x => Antiq(x)) | txt ^^ (x => Text(x))
  }


  /* read */

  def read(input: CharSequence): List[Antiquote] =
  {
    Parsers.parseAll(Parsers.rep(Parsers.text), new CharSequenceReader(input)) match {
      case Parsers.Success(xs, _) => xs
      case Parsers.NoSuccess(_, next) =>
        error("Malformed quotation/antiquotation source" +
          Position.here(Position.Line(next.pos.line)))
    }
  }
}

