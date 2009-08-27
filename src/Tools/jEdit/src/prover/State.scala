/*
 * Accumulating results from prover
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover

import scala.collection.mutable

object State
{
  def empty(cmd: Command) = State(cmd, Command.Status.UNPROCESSED,
    new mutable.ListBuffer, cmd.empty_root_node)
}

case class State(
  cmd: Command,
  status: Command.Status.Value,
  results: mutable.Buffer[XML.Tree],
  markup_root: MarkupNode
)
{

  private def set_status(st: Command.Status.Value):State =
    State(cmd, st, results, markup_root)
  private def add_result(res: XML.Tree):State =
    State(cmd, status, results + res, markup_root)
  private def add_markup(markup: MarkupNode):State =
    State(cmd, status, results, markup_root + markup)
  /* markup */

  def type_at(pos: Int): String =
  {
    val types = markup_root.filter(_.info match { case TypeInfo(_) => true case _ => false })
    types.flatten(_.flatten).
      find(t => t.start <= pos && t.stop > pos).
      map(t => t.content + ": " + (t.info match { case TypeInfo(i) => i case _ => "" })).
      getOrElse(null)
  }

  def ref_at(pos: Int): Option[MarkupNode] =
    markup_root.filter(_.info match { case RefInfo(_, _, _, _) => true case _ => false }).
      flatten(_.flatten).
      find(t => t.start <= pos && t.stop > pos)

  def +(message: XML.Tree) = {
    val changed: State =
    message match {
      case XML.Elem(Markup.MESSAGE, (Markup.CLASS, Markup.WRITELN) :: _, _)
      | XML.Elem(Markup.MESSAGE, (Markup.CLASS, Markup.PRIORITY) :: _, _)
      | XML.Elem(Markup.MESSAGE, (Markup.CLASS, Markup.WARNING) :: _, _) =>
        add_result(message)
      case XML.Elem(Markup.MESSAGE, (Markup.CLASS, Markup.ERROR) :: _, _) =>
        set_status(Command.Status.FAILED).add_result(message)
      case XML.Elem(Markup.MESSAGE, (Markup.CLASS, Markup.STATUS) :: _, elems) =>
        (this /: elems) ((r, e) =>
          e match {
            // command status
            case XML.Elem(Markup.UNPROCESSED, _, _) =>
              r.set_status(Command.Status.UNPROCESSED)
            case XML.Elem(Markup.FINISHED, _, _) =>
              r.set_status(Command.Status.FINISHED)
            case XML.Elem(Markup.FAILED, _, _) =>
              r.set_status(Command.Status.FAILED)
            case XML.Elem(kind, attr, body) =>
              val (begin, end) = Position.offsets_of(attr)
              if (begin.isDefined && end.isDefined) {
                if (kind == Markup.ML_TYPING) {
                  val info = body.first.asInstanceOf[XML.Text].content
                  r.add_markup(cmd.markup_node(begin.get - 1, end.get - 1, TypeInfo(info)))
                } else if (kind == Markup.ML_REF) {
                  body match {
                    case List(XML.Elem(Markup.ML_DEF, attr, _)) =>
                      r.add_markup(cmd.markup_node(
                        begin.get - 1, end.get - 1,
                        RefInfo(
                          Position.file_of(attr),
                          Position.line_of(attr),
                          Position.id_of(attr),
                          Position.offset_of(attr))))
                    case _ =>
                      r
                  }
                } else {
                  r.add_markup(cmd.markup_node(begin.get - 1, end.get - 1, HighlightInfo(kind)))
                }
              } else
                r
            case _ =>
              r
          })
      case _ =>
        System.err.println("ignored: " + message)
        this
    }
    cmd.changed()
    changed
  }

}
