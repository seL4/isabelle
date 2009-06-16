/*  Title:      Pure/General/scan.scala
    Author:     Makarius

Efficient scanning of literals.
*/

package isabelle

import scala.util.parsing.combinator.RegexParsers


object Scan
{

  /* class Lexicon -- position tree */

  case class Lexicon(val tab: Map[Char, (Boolean, Lexicon)])

  val empty_lexicon = Lexicon(Map())

  def is_literal(lx: Lexicon, str: CharSequence): Boolean =
  {
    val len = str.length
    def is_lit(lexicon: Lexicon, i: Int): Boolean =
      i < len && {
        lexicon.tab.get(str.charAt(i)) match {
          case Some((tip, lex)) => tip && i + 1 == len || is_lit(lex, i + 1)
          case None => false
        }
      }
    is_lit(lx, 0)
  }

  def extend_lexicon(lx: Lexicon, str: CharSequence): Lexicon =
  {
    val len = str.length
    def ext(lexicon: Lexicon, i: Int): Lexicon =
      if (i == len) lexicon
      else {
        val c = str.charAt(i)
        val is_last = (i + 1 == len)
        lexicon.tab.get(c) match {
          case Some((tip, lex)) => Lexicon(lexicon.tab + (c -> (tip || is_last, ext(lex, i + 1))))
          case None => Lexicon(lexicon.tab + (c -> (is_last, ext(empty_lexicon, i + 1))))
        }
      }
    if (is_literal(lx, str)) lx else ext(lx, 0)
  }

}


class Scan extends RegexParsers
{
  override val whiteSpace = "".r

  def keyword(lx: Scan.Lexicon): Parser[String] = new Parser[String] {
    def apply(in: Input) =
    {
      val source = in.source
      val offset = in.offset
      val len = source.length - offset

      def scan(lexicon: Scan.Lexicon, i: Int, res: Int): Int =
      {
        if (i < len) {
          lexicon.tab.get(source.charAt(offset + i)) match {
            case Some((tip, lex)) => scan(lex, i + 1, if (tip) i + 1 else res)
            case None => res
          }
        } else res
      }
      scan(lx, 0, 0) match {
        case res if res > 0 =>
          Success(source.subSequence(offset, res).toString, in.drop(res))
        case _ => Failure("keyword expected", in)
      }
    }
  }.named("keyword")

}

