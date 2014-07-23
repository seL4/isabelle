/*  Title:      Tools/jEdit/src/graphview_dockable.scala
    Author:     Makarius

Stateless dockable window for graphview.
*/

package isabelle.jedit


import isabelle._

import javax.swing.JComponent
import java.awt.Point
import java.awt.event.{WindowFocusListener, WindowEvent}

import org.gjt.sp.jedit.View

import scala.swing.TextArea


object Graphview_Dockable
{
  /* implicit arguments -- owned by GUI thread */

  private var implicit_snapshot = Document.Snapshot.init

  private val no_graph: Exn.Result[graphview.Model.Graph] = Exn.Exn(ERROR("No graph"))
  private var implicit_graph = no_graph

  private def set_implicit(snapshot: Document.Snapshot, graph: Exn.Result[graphview.Model.Graph])
  {
    GUI_Thread.require {}

    implicit_snapshot = snapshot
    implicit_graph = graph
  }

  private def reset_implicit(): Unit =
    set_implicit(Document.Snapshot.init, no_graph)

  def apply(view: View, snapshot: Document.Snapshot, graph: Exn.Result[graphview.Model.Graph])
  {
    set_implicit(snapshot, graph)
    view.getDockableWindowManager.floatDockableWindow("isabelle-graphview")
  }
}


class Graphview_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val snapshot = Graphview_Dockable.implicit_snapshot
  private val graph = Graphview_Dockable.implicit_graph

  private val window_focus_listener =
    new WindowFocusListener {
      def windowGainedFocus(e: WindowEvent) { Graphview_Dockable.set_implicit(snapshot, graph) }
      def windowLostFocus(e: WindowEvent) { Graphview_Dockable.reset_implicit() }
    }

  val graphview =
    graph match {
      case Exn.Res(proper_graph) =>
        new isabelle.graphview.Main_Panel(proper_graph) {
          override def make_tooltip(parent: JComponent, x: Int, y: Int, body: XML.Body): String =
          {
            Pretty_Tooltip.invoke(() =>
              {
                val rendering = Rendering(snapshot, PIDE.options.value)
                val info = Text.Info(Text.Range(~1), body)
                Pretty_Tooltip(view, parent, new Point(x, y), rendering, Command.Results.empty, info)
              })
            null
          }
        }
      case Exn.Exn(exn) => new TextArea(Exn.message(exn))
    }
  set_content(graphview)

  override def init()
  {
    GUI.parent_window(this).map(_.addWindowFocusListener(window_focus_listener))
  }

  override def exit()
  {
    GUI.parent_window(this).map(_.removeWindowFocusListener(window_focus_listener))
  }
}
