/*  Title:      Pure/Thy/thy_element.ML
    Author:     Makarius

Theory elements: statements with optional proof.
*/

package isabelle

import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input


object Thy_Element
{
  /* datatype element */

  type Proof[A] = (List[Element[A]], A)
  sealed case class Element[A](head: A, proof: Option[Proof[A]])
  {
    def iterator: Iterator[A] =
      Iterator(head) ++
        (for {
          (prf, qed) <- proof.iterator
          b <- (for (elem <- prf.iterator; a <- elem.iterator) yield a) ++ Iterator(qed)
        } yield b)

    def outline_iterator: Iterator[A] =
      proof match {
        case None => Iterator(head)
        case Some((_, qed)) => Iterator(head, qed)
      }

    def proof_start: Option[A] =
      proof match {
        case None => None
        case Some((Nil, qed)) => Some(qed)
        case Some((start :: _, _)) => Some(start.head)
      }

    def last: A =
      proof match {
        case None => head
        case Some((_, qed)) => qed
      }
  }

  def element[A](a: A, b: Proof[A]): Element[A] = Element(a, Some(b))
  def atom[A](a: A): Element[A] = Element(a, None)


  /* parse elements */

  type Element_Command = Element[Command]

  def parse_elements(keywords: Keyword.Keywords, commands: List[Command]): List[Element_Command] =
  {
    case class Reader(in: List[Command]) extends input.Reader[Command]
    {
      def first: Command = in.head
      def rest: Reader = Reader(in.tail)
      def pos: input.Position = input.NoPosition
      def atEnd: Boolean = in.isEmpty
    }

    object Parser extends Parsers
    {
      type Elem = Command

      def command(pred: Command => Boolean): Parser[Command] =
        new Parser[Elem] {
          def apply(in: Input) =
          {
            if (in.atEnd) Failure("end of input", in)
            else {
              val command = in.first
              if (pred(command)) Success(command, in.rest)
              else Failure("bad input", in)
            }
          }
        }

      def category(pred: String => Boolean, other: Boolean): Parser[Command] =
        command(_.span.is_kind(keywords, pred, other))

      def theory_element: Parser[Element_Command] =
        category(Keyword.theory_goal, false) ~ proof ^^ { case a ~ b => element(a, b) }
      def proof_element: Parser[Element_Command] =
        category(Keyword.proof_goal, false) ~ proof ^^ { case a ~ b => element(a, b) } |
        category(Keyword.proof_body, true) ^^ { case a => atom(a) }
      def proof: Parser[Proof[Command]] =
        rep(proof_element) ~ category(Keyword.qed, false) ^^ { case a ~ b => (a, b) }

      val default_element: Parser[Element_Command] = command(_ => true) ^^ { case a => atom(a) }

      def apply: List[Element_Command] =
        rep(theory_element | default_element)(Reader(commands)) match {
          case Success(result, rest) if rest.atEnd => result
          case bad => error(bad.toString)
        }
    }
    Parser.apply
  }
}
