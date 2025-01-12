/*  Title:      Tools/Find_Facts/src/thy_blocks.scala
    Author:     Fabian Huch, TU Muenchen

Block structure for Isabelle theories, read from build database.
*/

package isabelle.find_facts


import isabelle._

import scala.annotation.tailrec


object Thy_Blocks {
  /** spans **/

  val keyword_elements =
    Markup.Elements(Markup.KEYWORD, Markup.KEYWORD1, Markup.KEYWORD2, Markup.KEYWORD3)

  object Span {
    def read_build(snapshot: Document.Snapshot): List[Span] = {
      def is_begin(markup: Text.Markup): Boolean = markup.info match {
        case XML.Elem(Markup(_, Markup.Kind(Markup.KEYWORD)), Nil) =>
          XML.content(snapshot.xml_markup(markup.range)) == "begin"
        case _ => false
      }

      def has_begin(range: Text.Range): Boolean =
        snapshot
          .select(range, keyword_elements, _ => markup => Some(is_begin(markup)))
          .exists(_.info)

      snapshot.select(Text.Range.full, Markup.Elements(Markup.COMMAND_SPAN), _ =>
        {
          case Text.Info(range, XML.Elem(Markup.Command_Span(arg), _)) =>
            Some(Span(range, arg.name, arg.kind, has_begin(range)))
          case _ => None
        }).map(_.info)
    }
  }

  case class Span(
    override val range: Text.Range,
    override val command: String,
    kind: String,
    has_begin: Boolean
  ) extends Block {
    def spans: List[Span] = List(this)

    def is_of_kind(kinds: Set[String]): Boolean = kinds.contains(kind)
  }


  /** block structure **/

  sealed trait Block {
    def spans: List[Span]

    def command: String = spans.head.command
    def range: Text.Range = Text.Range(spans.head.range.start, spans.last.range.stop)
  }

  case class Single(span: Span) extends Block { def spans = List(span) }
  case class Thy(inner: List[Block]) extends Block { def spans = inner.flatMap(_.spans) }
  case class Prf(inner: List[Block]) extends Block { def spans = inner.flatMap(_.spans) }
  case class Decl(inner: List[Block]) extends Block { def spans = inner.flatMap(_.spans) }


  /** parser **/

  object Parser {
    object Blocks {
      def empty: Blocks = new Blocks(Nil, Nil)
    }

    case class Blocks(private val stack: List[Block], private val out: List[Block]) {
      def top: Option[Block] = stack.headOption
      def push(block: Block): Blocks = copy(stack = block :: stack)
      def add(block: Block): Blocks =
        stack match {
          case Nil => copy(out = block :: out)
          case head :: rest =>
            val head1 =
              head match {
                case Thy(inner) => Thy(inner :+ block)
                case Prf(inner) => Prf(inner :+ block)
                case Decl(inner) => Decl(inner :+ block)
                case _ => error("Cannot add to " + head)
              }
            copy(stack = head1 :: rest)
        }

      def pop: Blocks =
        stack match {
          case Nil => error("Nothing to pop")
          case head :: rest => copy(stack = rest).add(head)
        }

      def pop_prfs: Blocks = {
        val blocks1 = pop
        blocks1.stack match {
          case Prf(_) :: _ => blocks1.pop_prfs
          case _ => blocks1
        }
      }

      def output: List[Block] = if (stack.nonEmpty) error("Nonempty stack") else out.reverse
    }

    def parse(spans: List[Span]): List[Block] = {
      def parse1(blocks: Blocks, span: Span): Blocks =
        blocks.top match {
          case _ if span.is_of_kind(Keyword.document) => blocks.add(span)
          case None if span.is_of_kind(Keyword.theory_begin) => blocks.push(Thy(List(span)))
          case Some(_) if span.is_of_kind(Keyword.diag) => blocks.add(span)
          case Some(Thy(_)) if span.is_of_kind(Keyword.theory_goal) => blocks.push(Prf(List(span)))
          case Some(Thy(_)) if span.is_of_kind(Keyword.theory_block) =>
            (if (span.has_begin) blocks.push else blocks.add)(Decl(List(span)))
          case Some(Thy(_)) if span.is_of_kind(Keyword.theory_end) => blocks.add(span).pop
          case Some(Thy(_)) if span.is_of_kind(Keyword.theory_body) => blocks.add(span)
          case Some(Prf(_)) if span.is_of_kind(Keyword.proof_open) => blocks.push(Prf(List(span)))
          case Some(Prf(_)) if span.is_of_kind(Keyword.proof_close) => blocks.add(span).pop
          case Some(Prf(_)) if span.is_of_kind(Keyword.qed_global) => blocks.add(span).pop_prfs
          case Some(Prf(_)) if span.is_of_kind(Keyword.proof_body) => blocks.add(span)
          case Some(Decl(_)) if span.is_of_kind(Keyword.proof_open) => blocks.push(Prf(List(span)))
          case Some(Decl(_)) if span.is_of_kind(Keyword.proof_body) => blocks.add(span)
          case Some(Decl(_)) if span.is_of_kind(Keyword.theory_goal) => blocks.push(Prf(List(span)))
          case Some(Decl(_)) if span.is_of_kind(Keyword.theory_block) =>
            (if (span.has_begin) blocks.push else blocks.add)(Decl(List(span)))
          case Some(Decl(_)) if span.is_of_kind(Keyword.theory_end) => blocks.add(span).pop
          case Some(Decl(_)) if span.is_of_kind(Keyword.theory_body) => blocks.add(span)
          case e => error("Unexpected span " + span + " at " + e)
        }

      spans.foldLeft(Blocks.empty)(parse1).output
    }
  }

  def read_blocks(snapshot: Document.Snapshot): List[Block] =
    Parser.parse(Span.read_build(snapshot))
}
