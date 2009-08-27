/*
 * Dockable window for navigating through the document-versions
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


class BrowseVersionDockable(view : View, position : String) extends FlowPanel
{

  def get_versions() =
    Isabelle.prover_setup(view.getBuffer).map(_.theory_view.changes).getOrElse(Nil)

  if (position == DockableWindowManager.FLOATING)
    preferredSize = new Dimension(500, 250)

  val list = new ListView[Change]
  list.fixedCellWidth = 500
  list.listData = get_versions()
  contents += list

  listenTo(list.selection)
  reactions += {
    case ListSelectionChanged(source, range, false) =>
      Swing_Thread.now {
        Isabelle.prover_setup(view.getBuffer).map(_.
          theory_view.set_version(list.listData(range.start)))
      }
  }

  private var num_changes = 0
  Isabelle.plugin.document_change += {_ =>
    list.listData = get_versions()
  }

}
