/*  Title:      Pure/PIDE/state.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Accumulating results from prover.
*/

package isabelle


class State(
  val command: Command,
  val status: Command.Status.Value,
  val forks: Int,
  val reverse_results: List[XML.Tree],
  val markup_root: Markup_Text)
{
  def this(command: Command) =
    this(command, Command.Status.UNPROCESSED, 0, Nil, command.empty_markup)


  /* content */

  private def set_status(st: Command.Status.Value): State =
    new State(command, st, forks, reverse_results, markup_root)

  private def add_forks(i: Int): State =
    new State(command, status, forks + i, reverse_results, markup_root)

  private def add_result(res: XML.Tree): State =
    new State(command, status, forks, res :: reverse_results, markup_root)

  private def add_markup(node: Markup_Tree): State =
    new State(command, status, forks, reverse_results, markup_root + node)

  lazy val results = reverse_results.reverse


  /* markup */

  lazy val highlight: Markup_Text =
  {
    markup_root.filter(_.info match {
      case Command.HighlightInfo(_, _) => true
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

  def accumulate(message: XML.Tree): State =
    message match {
      case XML.Elem(Markup.STATUS, _, elems) =>
        (this /: elems)((state, elem) =>
          elem match {
            case XML.Elem(Markup.UNPROCESSED, _, _) => state.set_status(Command.Status.UNPROCESSED)
            case XML.Elem(Markup.FINISHED, _, _) => state.set_status(Command.Status.FINISHED)
            case XML.Elem(Markup.FAILED, _, _) => state.set_status(Command.Status.FAILED)
            case XML.Elem(Markup.FORKED, _, _) => state.add_forks(1)
            case XML.Elem(Markup.JOINED, _, _) => state.add_forks(-1)
            case XML.Elem(kind, atts, body) if Position.get_id(atts) == Some(command.id) =>
              atts match {
                case Position.Range(begin, end) =>
                  if (kind == Markup.ML_TYPING) {
                    val info = Pretty.string_of(body, margin = 40)
                    state.add_markup(
                      command.markup_node(begin - 1, end - 1, Command.TypeInfo(info)))
                  }
                  else if (kind == Markup.ML_REF) {
                    body match {
                      case List(XML.Elem(Markup.ML_DEF, atts, _)) =>
                        state.add_markup(command.markup_node(
                          begin - 1, end - 1,
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
                      command.markup_node(begin - 1, end - 1,
                        Command.HighlightInfo(kind, Markup.get_string(Markup.KIND, atts))))
                  }
                case _ => state
              }
            case _ =>
              System.err.println("Ignored status report: " + elem)
              state
          })
      case _ => add_result(message)
    }
}
