/*
 * Accumulating results from prover
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.prover


class State(
  val command: Command,
  val status: Command.Status.Value,
  rev_results: List[XML.Tree],
  val markup_root: MarkupNode)
{
  def this(command: Command) =
    this(command, Command.Status.UNPROCESSED, Nil, command.empty_root_node)


  /* content */

  private def set_status(st: Command.Status.Value): State =
    new State(command, st, rev_results, markup_root)

  private def add_result(res: XML.Tree): State =
    new State(command, status, res :: rev_results, markup_root)

  private def add_markup(markup: MarkupNode): State =
    new State(command, status, rev_results, markup_root + markup)

  lazy val results = rev_results.reverse


  /* markup */

  lazy val highlight_node: MarkupNode =
  {
    markup_root.filter(_.info match {
      case Command.RootInfo | Command.HighlightInfo(_) => true
      case _ => false
    }).head
  }

  private lazy val types =
    markup_root.filter(_.info match {
      case Command.TypeInfo(_) => true
      case _ => false }).flatten(_.flatten)

  def type_at(pos: Int): String =
  {
    types.find(t => t.start <= pos && pos < t.stop).map(t =>
      t.content + ": " + (t.info match {
        case Command.TypeInfo(i) => i
        case _ => "" })).
      getOrElse(null)
  }

  private lazy val refs =
    markup_root.filter(_.info match {
      case Command.RefInfo(_, _, _, _) => true
      case _ => false }).flatten(_.flatten)

  def ref_at(pos: Int): Option[MarkupNode] =
    refs.find(t => t.start <= pos && pos < t.stop)


  /* message dispatch */

  def + (message: XML.Tree): State =
  {
    val changed: State =
      message match {
        case XML.Elem(Markup.MESSAGE, (Markup.CLASS, Markup.STATUS) :: _, elems) =>
          (this /: elems)((state, elem) =>
            elem match {
              case XML.Elem(Markup.UNPROCESSED, _, _) => state.set_status(Command.Status.UNPROCESSED)
              case XML.Elem(Markup.FINISHED, _, _) => state.set_status(Command.Status.FINISHED)
              case XML.Elem(Markup.FAILED, _, _) => state.set_status(Command.Status.FAILED)
              case XML.Elem(kind, atts, body) =>
                val (begin, end) = Position.offsets_of(atts)
                if (begin.isEmpty || end.isEmpty) state
                else if (kind == Markup.ML_TYPING) {
                  val info = body.first.asInstanceOf[XML.Text].content   // FIXME proper match!?
                  state.add_markup(
                    command.markup_node(begin.get - 1, end.get - 1, Command.TypeInfo(info)))
                }
                else if (kind == Markup.ML_REF) {
                  body match {
                    case List(XML.Elem(Markup.ML_DEF, atts, _)) =>
                      state.add_markup(command.markup_node(
                        begin.get - 1, end.get - 1,
                        Command.RefInfo(
                          Position.file_of(atts),
                          Position.line_of(atts),
                          Position.id_of(atts),
                          Position.offset_of(atts))))
                    case _ => state
                  }
                }
                else {
                  state.add_markup(
                    command.markup_node(begin.get - 1, end.get - 1, Command.HighlightInfo(kind)))
                }
              case _ =>
                System.err.println("ignored status report: " + elem)
                state
            })
        case _ => add_result(message)
      }
    if (!(this eq changed)) command.changed()
    changed
  }
}
