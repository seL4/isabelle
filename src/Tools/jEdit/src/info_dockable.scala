/*  Title:      Tools/jEdit/src/info_dockable.scala
    Author:     Makarius

Dockable window with info text.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{WindowFocusListener, WindowEvent}

import org.gjt.sp.jedit.View


object Info_Dockable {
  /* content as implicit parameter -- owned by GUI thread */

  private var _content = Editor.Output.init

  private def get_content(): Editor.Output = GUI_Thread.require { _content }
  private def set_content(content: Editor.Output): Unit = GUI_Thread.require { _content = content }
  private def reset_content(): Unit = set_content(Editor.Output.init)

  def apply(
    view: View,
    snapshot: Document.Snapshot,
    results: Command.Results,
    messages: List[XML.Elem]
  ): Unit = {
    set_content(Editor.Output(snapshot = snapshot, results = results, messages = messages))
    view.getDockableWindowManager.floatDockableWindow("isabelle-info")
  }
}


class Info_Dockable(view: View, position: String) extends Dockable(view, position) {
  dockable =>


  /* component state -- owned by GUI thread */

  private val content = Info_Dockable.get_content()

  private val window_focus_listener =
    new WindowFocusListener {
      def windowGainedFocus(e: WindowEvent): Unit = Info_Dockable.set_content(content)
      def windowLostFocus(e: WindowEvent): Unit = Info_Dockable.reset_content()
    }


  /* output text area */

  private val output: Output_Area =
    new Output_Area(view) {
      override def handle_shown(): Unit = split_pane_layout()
    }

  output.pretty_text_area.update_output(content)

  private val auto_hovering_button = new JEdit_Options.auto_hovering.GUI

  private val controls =
    Wrap_Panel(auto_hovering_button :: output.pretty_text_area.search_zoom_components)
  add(controls.peer, BorderLayout.NORTH)

  output.setup(dockable)
  set_content(output.split_pane)


  /* main */

  private val main =
    Session.Consumer[Session.Global_Options](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later {
          output.handle_resize()
          auto_hovering_button.load()
        }
    }

  override def init(): Unit = {
    GUI.parent_window(this).foreach(_.addWindowFocusListener(window_focus_listener))
    PIDE.session.global_options += main
    output.init()
  }

  override def exit(): Unit = {
    GUI.parent_window(this).foreach(_.removeWindowFocusListener(window_focus_listener))
    PIDE.session.global_options -= main
    output.exit()
  }
}
