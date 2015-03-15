/*  Title:      Pure/PIDE/command_span.scala
    Author:     Makarius

Syntactic representation of command spans.
*/

package isabelle


import scala.collection.mutable


object Command_Span
{
  sealed abstract class Kind {
    override def toString: String =
      this match {
        case Command_Span(name, _) => if (name != "") name else "<command>"
        case Ignored_Span => "<ignored>"
        case Malformed_Span => "<malformed>"
      }
  }
  case class Command_Span(name: String, pos: Position.T) extends Kind
  case object Ignored_Span extends Kind
  case object Malformed_Span extends Kind

  sealed case class Span(kind: Kind, content: List[Token])
  {
    def length: Int = (0 /: content)(_ + _.source.length)

    def source: String =
      content match {
        case List(tok) => tok.source
        case toks => toks.map(_.source).mkString
      }

    def compact_source: (String, Span) =
    {
      val src = source
      val content1 = new mutable.ListBuffer[Token]
      var i = 0
      for (Token(kind, s) <- content) {
        val n = s.length
        val s1 = src.substring(i, i + n)
        content1 += Token(kind, s1)
        i += n
      }
      (src, Span(kind, content1.toList))
    }
  }

  val empty: Span = Span(Ignored_Span, Nil)

  def unparsed(source: String): Span =
    Span(Malformed_Span, List(Token(Token.Kind.UNPARSED, source)))
}
