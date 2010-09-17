/*  Title:      Pure/PIDE/command.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Prover commands with semantic state.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Command
{
  /** accumulated results from prover **/

  case class State(
    val command: Command,
    val status: List[Markup] = Nil,
    val results: SortedMap[Long, XML.Tree] = SortedMap.empty,
    val markup: Markup_Tree = Markup_Tree.empty)
  {
    /* content */

    def add_status(st: Markup): State = copy(status = st :: status)
    def add_markup(info: Text.Info[Any]): State = copy(markup = markup + info)
    def add_result(serial: Long, result: XML.Tree): State =
      copy(results = results + (serial -> result))

    def root_info: Text.Info[Any] =
      new Text.Info(command.range,
        XML.Elem(Markup(Markup.STATUS, Nil), status.reverse.map(XML.Elem(_, Nil))))
    def root_markup: Markup_Tree = markup + root_info


    /* message dispatch */

    def accumulate(message: XML.Elem): Command.State =
      message match {
        case XML.Elem(Markup(Markup.STATUS, _), msgs) =>
          (this /: msgs)((state, msg) =>
            msg match {
              case XML.Elem(markup, Nil) => state.add_status(markup)
              case _ => System.err.println("Ignored status message: " + msg); state
            })

        case XML.Elem(Markup(Markup.REPORT, _), msgs) =>
          (this /: msgs)((state, msg) =>
            msg match {
              case XML.Elem(Markup(name, atts @ Position.Id_Range(id, raw_range)), args)
              if id == command.id && command.range.contains(command.decode(raw_range)) =>
                val range = command.decode(raw_range)
                val props = Position.purge(atts)
                val info = Text.Info[Any](range, XML.Elem(Markup(name, props), args))
                state.add_markup(info)
              case _ => System.err.println("Ignored report message: " + msg); state
            })
        case XML.Elem(Markup(name, atts), body) =>
          atts match {
            case Markup.Serial(i) =>
              val result = XML.Elem(Markup(name, Position.purge(atts)), body)
              val st1 =
                (add_result(i, result) /: Isar_Document.message_positions(command, message))(
                  (st, range) => st.add_markup(Text.Info(range, result)))
              (st1 /: Isar_Document.message_reports(message))(_ accumulate _)
            case _ => System.err.println("Ignored message without serial number: " + message); this
          }
      }
  }


  /* unparsed dummy commands */

  def unparsed(source: String) =
    new Command(Document.NO_ID, List(Token(Token.Kind.UNPARSED, source)))
}


class Command(
    val id: Document.Command_ID,
    val span: List[Token])
{
  /* classification */

  def is_command: Boolean = !span.isEmpty && span.head.is_command
  def is_ignored: Boolean = span.forall(_.is_ignored)
  def is_malformed: Boolean = !is_command && !is_ignored

  def is_unparsed = id == Document.NO_ID

  def name: String = if (is_command) span.head.content else ""
  override def toString =
    id + "/" + (if (is_command) name else if (is_ignored) "IGNORED" else "MALFORMED")


  /* source text */

  val source: String = span.map(_.source).mkString
  def source(range: Text.Range): String = source.substring(range.start, range.stop)
  def length: Int = source.length

  val newlines =
    (0 /: Symbol.iterator(source)) {
      case (n, s) => if (Symbol.is_physical_newline(s)) n + 1 else n }

  val range: Text.Range = Text.Range(0, length)

  lazy val symbol_index = new Symbol.Index(source)
  def decode(i: Text.Offset): Text.Offset = symbol_index.decode(i)
  def decode(r: Text.Range): Text.Range = symbol_index.decode(r)


  /* accumulated results */

  val empty_state: Command.State = Command.State(this)
}
