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
  /* implicit arguments -- owned by GUI thread */

  private var implicit_snapshot = Document.Snapshot.init
  private var implicit_results = Command.Results.empty
  private var implicit_info: List[XML.Elem] = Nil

  private def set_implicit(
    snapshot: Document.Snapshot,
    results: Command.Results,
    info: List[XML.Elem]
  ): Unit = {
    GUI_Thread.require {}

    implicit_snapshot = snapshot
    implicit_results = results
    implicit_info = info
  }

  private def reset_implicit(): Unit =
    set_implicit(Document.Snapshot.init, Command.Results.empty, Nil)

  def apply(
    view: View,
    snapshot: Document.Snapshot,
    results: Command.Results,
    info: List[XML.Elem]
  ): Unit = {
    set_implicit(snapshot, results, info)
    view.getDockableWindowManager.floatDockableWindow("isabelle-info")
  }
}


class Info_Dockable(view: View, position: String) extends Dockable(view, position) {
  dockable =>


  /* component state -- owned by GUI thread */

  private val snapshot = Info_Dockable.implicit_snapshot
  private val results = Info_Dockable.implicit_results
  private val info = Info_Dockable.implicit_info

  private val window_focus_listener =
    new WindowFocusListener {
      def windowGainedFocus(e: WindowEvent): Unit =
        Info_Dockable.set_implicit(snapshot, results, info)
      def windowLostFocus(e: WindowEvent): Unit =
        Info_Dockable.reset_implicit()
    }


  /* output text area */

  private val output: Output_Area =
    new Output_Area(view) {
      override def handle_shown(): Unit = split_pane_layout()
    }

  output.pretty_text_area.update(snapshot, results, info)

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
