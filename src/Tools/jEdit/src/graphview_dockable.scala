/*  Title:      Tools/jEdit/src/graphview_dockable.scala
    Author:     Makarius

Stateless dockable window for graphview.
*/

package isabelle.jedit


import isabelle._
import isabelle.jedit_base.Dockable

import javax.swing.JComponent
import java.awt.{Point, Font}
import java.awt.event.{WindowFocusListener, WindowEvent}

import org.gjt.sp.jedit.View

import scala.swing.TextArea


object Graphview_Dockable
{
  /* implicit arguments -- owned by GUI thread */

  private var implicit_snapshot = Document.Snapshot.init

  private val no_graph: Exn.Result[Graph_Display.Graph] = Exn.Exn(ERROR("No graph"))
  private var implicit_graph = no_graph

  private def set_implicit(
    snapshot: Document.Snapshot, graph: Exn.Result[Graph_Display.Graph]): Unit =
  {
    GUI_Thread.require {}

    implicit_snapshot = snapshot
    implicit_graph = graph
  }

  private def reset_implicit(): Unit =
    set_implicit(Document.Snapshot.init, no_graph)

  class Handler extends Active.Handler
  {
    override def handle(
      view: View, text: String, elem: XML.Elem,
      doc_view: Document_View, snapshot: Document.Snapshot): Boolean =
    {
      elem match {
        case XML.Elem(Markup(Markup.GRAPHVIEW, _), body) =>
          Isabelle_Thread.fork(name = "graphview") {
            val graph =
              Exn.capture {
                Graph_Display.decode_graph(body).transitive_reduction_acyclic
              }
            GUI_Thread.later {
              set_implicit(snapshot, graph)
              view.getDockableWindowManager.floatDockableWindow("isabelle-graphview")
            }
          }
          true
        case _ => false
      }
    }
  }
}

class Graphview_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val snapshot = Graphview_Dockable.implicit_snapshot
  private val graph_result = Graphview_Dockable.implicit_graph

  private val window_focus_listener =
    new WindowFocusListener {
      def windowGainedFocus(e: WindowEvent): Unit =
        Graphview_Dockable.set_implicit(snapshot, graph_result)
      def windowLostFocus(e: WindowEvent): Unit =
        Graphview_Dockable.reset_implicit()
    }

  val graphview =
    graph_result match {
      case Exn.Res(graph) =>
        val graphview = new isabelle.graphview.Graphview(graph) {
          def options: Options = PIDE.options.value

          override def make_tooltip(parent: JComponent, x: Int, y: Int, body: XML.Body): String =
          {
            Pretty_Tooltip.invoke(() =>
              {
                val model = File_Model.empty(PIDE.session)
                val rendering = JEdit_Rendering(snapshot, model, options)
                val info = Text.Info(Text.Range.offside, body)
                Pretty_Tooltip(view, parent, new Point(x, y), rendering, Command.Results.empty, info)
              })
            null
          }

          override def make_font(): Font =
            if (editor_style) GUI.imitate_font(Font_Info.main().font)
            else
              GUI.imitate_font(Font_Info.main().font,
                family = options.string("graphview_font_family"),
                scale = options.real("graphview_font_scale"))

          override def foreground_color =
            if (editor_style) view.getTextArea.getPainter.getForeground
            else super.foreground_color

          override def background_color =
            if (editor_style) view.getTextArea.getPainter.getBackground
            else super.background_color

          override def selection_color =
            if (editor_style) view.getTextArea.getPainter.getSelectionColor
            else super.selection_color

          override def highlight_color =
            if (editor_style) view.getTextArea.getPainter.getLineHighlightColor
            else super.highlight_color

          override def error_color = PIDE.options.color_value("error_color")

          editor_style = true
        }
        new isabelle.graphview.Main_Panel(graphview)
      case Exn.Exn(exn) => new TextArea(Exn.message(exn))
    }
  set_content(graphview)


  override def focusOnDefaultComponent(): Unit =
  {
    graphview match {
      case main_panel: isabelle.graphview.Main_Panel =>
        main_panel.tree_panel.tree.requestFocusInWindow
      case _ =>
    }
  }


  /* main */

  private val main =
    Session.Consumer[Session.Global_Options](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later {
          graphview match {
            case main_panel: isabelle.graphview.Main_Panel =>
              main_panel.update_layout()
            case _ =>
          }
        }
    }

  override def init(): Unit =
  {
    GUI.parent_window(this).foreach(_.addWindowFocusListener(window_focus_listener))
    PIDE.session.global_options += main
  }

  override def exit(): Unit =
  {
    GUI.parent_window(this).foreach(_.removeWindowFocusListener(window_focus_listener))
    PIDE.session.global_options -= main
  }
}
