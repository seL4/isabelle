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


class BrowseVersionDockable(view: View, position: String) extends FlowPanel
{
  if (position == DockableWindowManager.FLOATING)
    preferredSize = new Dimension(500, 250)

  def prover_setup(): Option[ProverSetup] = Isabelle.prover_setup(view.getBuffer)
  def get_versions() =
    prover_setup() match {
      case None => Nil
      case Some(setup) => setup.theory_view.changes
    }

  val list = new ListView[Change]
  list.fixedCellWidth = 500
  list.listData = get_versions()
  contents += list

  listenTo(list.selection)
  reactions += {
    case ListSelectionChanged(source, range, false) =>
        prover_setup().map(_.theory_view.set_version(list.listData(range.start)))
    }

  prover_setup.foreach(_.prover.document_change += (_ => list.listData = get_versions()))
}
