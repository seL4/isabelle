/*  Title:      Tools/Find_Facts/src/thy_blocks.scala
    Author:     Fabian Huch, TU Muenchen

Block structure for Isabelle theories, read from build database.
*/

package isabelle.find_facts


import isabelle._


object Thy_Blocks {
  /** spans **/

  case class Span(
    override val range: Text.Range,
    override val command: String,
    kind: String,
    is_begin: Boolean
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
            (if (span.is_begin) blocks.push else blocks.add)(Decl(List(span)))
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
            (if (span.is_begin) blocks.push else blocks.add)(Decl(List(span)))
          case Some(Decl(_)) if span.is_of_kind(Keyword.theory_end) => blocks.add(span).pop
          case Some(Decl(_)) if span.is_of_kind(Keyword.theory_body) => blocks.add(span)
          case e => error("Unexpected span " + span + " at " + e)
        }

      spans.foldLeft(Blocks.empty)(parse1).output
    }
  }

  def read_blocks(snapshot: Document.Snapshot): List[Block] = {
    val spans =
      for (Text.Info(range, arg) <- snapshot.command_spans(Text.Range.full))
        yield Span(range, arg.name, arg.kind, arg.is_begin)
    Parser.parse(spans)
  }
}
