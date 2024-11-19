/*  Title:      Tools/jEdit/src/state_dockable.scala
    Author:     Makarius

Dockable window for proof state output.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class State_Dockable(view: View, position: String) extends Dockable(view, position) {
  GUI_Thread.require {}


  /* output text area */

  private val output: Output_Area = new Output_Area(view)

  override def detach_operation: Option[() => Unit] = output.pretty_text_area.detach_operation

  private val print_state =
    new Query_Operation(PIDE.editor, view, "print_state", _ => (), output.pretty_text_area.update)

  output.init_gui(this, split = true)


  /* update */

  def update_request(): Unit =
    GUI_Thread.require { print_state.apply_query(Nil) }

  def update(): Unit = {
    GUI_Thread.require {}

    PIDE.editor.current_node_snapshot(view) match {
      case Some(snapshot) =>
        (PIDE.editor.current_command(view, snapshot), print_state.get_location) match {
          case (Some(command1), Some(command2)) if command1.id == command2.id =>
          case _ => update_request()
        }
      case None =>
    }
  }


  /* auto update */

  private var auto_update_enabled = true

  private def auto_update(): Unit =
    GUI_Thread.require { if (auto_update_enabled) update() }


  /* controls */

  private val auto_update_button = new GUI.Check("Auto update", init = auto_update_enabled) {
    tooltip = "Indicate automatic update following cursor movement"
    override def clicked(state: Boolean): Unit = {
      auto_update_enabled = state
      auto_update()
    }
  }

  private val update_button = new GUI.Button("<html><b>Update</b></html>") {
    tooltip = "Update display according to the command at cursor position"
    override def clicked(): Unit = update_request()
  }

  private val locate_button = new GUI.Button("Locate") {
    tooltip = "Locate printed command within source text"
    override def clicked(): Unit = print_state.locate_query()
  }

  private val controls =
    Wrap_Panel(
      List(auto_update_button, update_button, locate_button) :::
      output.pretty_text_area.search_zoom_components)

  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later { output.handle_resize() }

      case changed: Session.Commands_Changed =>
        if (changed.assignment) GUI_Thread.later { auto_update() }

      case Session.Caret_Focus =>
        GUI_Thread.later { auto_update() }
    }

  override def init(): Unit = {
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    output.init()
    print_state.activate()
    auto_update()
  }

  override def exit(): Unit = {
    print_state.deactivate()
    PIDE.session.caret_focus -= main
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    output.exit()
  }
}
