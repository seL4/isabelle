/*
 * Dockable window for navigating through the document-versions
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import isabelle.proofdocument.Text

import java.awt.Dimension
import scala.swing.{ListView, FlowPanel}
import scala.swing.event.ListSelectionChanged

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager


class BrowseVersionDockable(view : View, position : String) extends FlowPanel {

  val theory_view = Isabelle.prover_setup(view.getBuffer).get.theory_view
  if (position == DockableWindowManager.FLOATING)
    preferredSize = new Dimension(500, 250)

  val list = new ListView[Text.Change]
  list.fixedCellWidth = 500

  new javax.swing.Timer(1000, new java.awt.event.ActionListener {
    override def actionPerformed(evt: java.awt.event.ActionEvent) {
      list.listData_=(theory_view.get_changes)
    }
  }).start()

  contents += list
  listenTo(list.selection)

  reactions += {
    case ListSelectionChanged(source, range, false) =>
      Swing_Thread.now {
        theory_view.set_version(list.listData(range.start).id)
      }
  }
}
