/*  Title:      Tools/jEdit/src/jedit/isabelle_markup.scala
    Author:     Makarius

Isabelle specific physical rendering and markup selection.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color

import org.gjt.sp.jedit.GUIUtilities


object Isabelle_Markup
{
  /* physical rendering */

  val outdated_color = new Color(240, 240, 240)
  val unfinished_color = new Color(255, 228, 225)

  val regular_color = new Color(192, 192, 192)
  val warning_color = new Color(255, 168, 0)
  val error_color = new Color(255, 80, 80)
  val bad_color = new Color(255, 204, 153, 100)

  val warning_icon = GUIUtilities.loadIcon("16x16/status/dialog-warning.png")
  val error_icon = GUIUtilities.loadIcon("16x16/status/dialog-error.png")


  /* command status */

  def status_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.state(command)
    if (snapshot.is_outdated) Some(outdated_color)
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) if i > 0 => Some(unfinished_color)
        case Isar_Document.Unprocessed => Some(unfinished_color)
        case _ => None
      }
  }

  def overview_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.state(command)
    if (snapshot.is_outdated) None
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) if i > 0 => Some(unfinished_color)
        case Isar_Document.Unprocessed => Some(unfinished_color)
        case Isar_Document.Failed => Some(error_color)
        case _ => None
      }
  }


  /* markup selectors */

  private val subexp_include =
    Set(Markup.SORT, Markup.TYP, Markup.TERM, Markup.PROP, Markup.ML_TYPING)

  val subexp: Markup_Tree.Select[(Text.Range, Color)] =
  {
    case Text.Info(range, XML.Elem(Markup(name, _), _)) if subexp_include(name) =>
      (range, Color.black)
  }

  val message: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.WRITELN, _), _)) => regular_color
    case Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), _)) => warning_color
    case Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _)) => error_color
  }

  val background: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _)) => bad_color
  }

  val box: Markup_Tree.Select[Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.TOKEN_RANGE, _), _)) => regular_color
  }

  val tooltip: Markup_Tree.Select[String] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.ML_TYPING, _), body)) =>
      Pretty.string_of(List(Pretty.block(body)), margin = 40)
    case Text.Info(_, XML.Elem(Markup(Markup.SORT, _), _)) => "sort"
    case Text.Info(_, XML.Elem(Markup(Markup.TYP, _), _)) => "type"
    case Text.Info(_, XML.Elem(Markup(Markup.TERM, _), _)) => "term"
    case Text.Info(_, XML.Elem(Markup(Markup.PROP, _), _)) => "proposition"
  }
}
