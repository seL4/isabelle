/*
 * Dockable window for navigating through the document history
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.proofdocument.Change

import java.awt.Dimension
import scala.swing.{ListView, FlowPanel}
import scala.swing.event.ListSelectionChanged

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager


class History_Dockable(view: View, position: String) extends FlowPanel
{
  if (position == DockableWindowManager.FLOATING)
    preferredSize = new Dimension(500, 250)

  def get_versions() =
    Document_Model(view.getBuffer) match {
      case None => Nil
      case Some(model) => model.changes
    }

  val list = new ListView[Change]
  list.fixedCellWidth = 500
  list.listData = get_versions()
  contents += list

  listenTo(list.selection)
  reactions += {
    case ListSelectionChanged(source, range, false) =>
      Document_Model(view.getBuffer).map(_.set_version(list.listData(range.start)))
  }

  if (Document_Model(view.getBuffer).isDefined)
    Isabelle.session.document_change += (_ => list.listData = get_versions())
}
