/*
 * Dockable window for navigating through the document history
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.proofdocument.{Change, Theory_View}

import java.awt.Dimension
import scala.swing.{ListView, FlowPanel}
import scala.swing.event.ListSelectionChanged

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager


class History_Dockable(view: View, position: String) extends FlowPanel
{
  if (position == DockableWindowManager.FLOATING)
    preferredSize = new Dimension(500, 250)

  def dynamic_theory_view(): Option[Theory_View] =
    Isabelle.plugin.theory_view(view.getBuffer)
  def get_versions() =
    dynamic_theory_view() match {
      case None => Nil
      case Some(theory_view) => theory_view.changes
    }

  val list = new ListView[Change]
  list.fixedCellWidth = 500
  list.listData = get_versions()
  contents += list

  listenTo(list.selection)
  reactions += {
    case ListSelectionChanged(source, range, false) =>
      dynamic_theory_view().map(_.set_version(list.listData(range.start)))
  }

  if (dynamic_theory_view().isDefined)
    Isabelle.session.document_change += (_ => list.listData = get_versions())
}
