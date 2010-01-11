/*
 * Accumulating results from prover
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle


class State(
  val command: Command,
  val status: Command.Status.Value,
  val rev_results: List[XML.Tree],
  val markup_root: Markup_Text)
{
  def this(command: Command) =
    this(command, Command.Status.UNPROCESSED, Nil, command.empty_markup)


  /* content */

  private def set_status(st: Command.Status.Value): State =
    new State(command, st, rev_results, markup_root)

  private def add_result(res: XML.Tree): State =
    new State(command, status, res :: rev_results, markup_root)

  private def add_markup(node: Markup_Tree): State =
    new State(command, status, rev_results, markup_root + node)

  lazy val results = rev_results.reverse


  /* markup */

  lazy val highlight: Markup_Text =
  {
    markup_root.filter(_.info match {
      case Command.HighlightInfo(_) => true
      case _ => false
    })
  }

  private lazy val types: List[Markup_Node] =
    markup_root.filter(_.info match {
      case Command.TypeInfo(_) => true
      case _ => false }).flatten

  def type_at(pos: Int): Option[String] =
  {
    types.find(t => t.start <= pos && pos < t.stop) match {
      case Some(t) =>
        t.info match {
          case Command.TypeInfo(ty) => Some(command.source(t.start, t.stop) + ": " + ty)
          case _ => None
        }
      case None => None
    }
  }

  private lazy val refs: List[Markup_Node] =
    markup_root.filter(_.info match {
      case Command.RefInfo(_, _, _, _) => true
      case _ => false }).flatten

  def ref_at(pos: Int): Option[Markup_Node] =
    refs.find(t => t.start <= pos && pos < t.stop)


  /* message dispatch */

  def + (session: Session, message: XML.Tree): State =
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
                val (begin, end) = Position.get_offsets(atts)
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
                          Position.get_file(atts),
                          Position.get_line(atts),
                          Position.get_id(atts),
                          Position.get_offset(atts))))
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
    if (!(this eq changed)) session.command_change.event(command)
    changed
  }
}
