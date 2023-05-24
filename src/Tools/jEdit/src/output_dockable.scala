/*  Title:      Tools/jEdit/src/output_dockable.scala
    Author:     Makarius

Dockable window with result message output.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class Output_Dockable(view: View, position: String) extends Dockable(view, position) {
  /* component state -- owned by GUI thread */

  private var do_update = true
  private var current_output: List[XML.Tree] = Nil


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  override def detach_operation: Option[() => Unit] = pretty_text_area.detach_operation


  private def handle_resize(): Unit =
    GUI_Thread.require { pretty_text_area.zoom(zoom) }

  private def handle_update(follow: Boolean, restriction: Option[Set[Command]]): Unit = {
    GUI_Thread.require {}

    for {
      snapshot <- PIDE.editor.current_node_snapshot(view)
      if follow && !snapshot.is_outdated
    } {
      val (command, results) =
        PIDE.editor.current_command(view, snapshot) match {
          case Some(command) => (command, snapshot.command_results(command))
          case None => (Command.empty, Command.Results.empty)
        }

      val new_output =
        if (restriction.isEmpty || restriction.get.contains(command))
          Rendering.output_messages(results, true)
        else current_output

      if (current_output != new_output) {
        pretty_text_area.update(snapshot, results, Pretty.separate(new_output))
        current_output = new_output
      }
    }
  }


  /* controls */

  private val output_state_button = new JEdit_Options.output_state.GUI

  private val auto_update_button = new GUI.Check("Auto update", init = do_update) {
    tooltip = "Indicate automatic update following cursor movement"
    override def clicked(state: Boolean): Unit = {
      do_update = state
      handle_update(do_update, None)
    }
  }

  private val update_button = new GUI.Button("Update") {
    tooltip = "Update display according to the command at cursor position"
    override def clicked(): Unit = handle_update(true, None)
  }

  private val zoom = new Font_Info.Zoom { override def changed(): Unit = handle_resize() }

  private val controls =
    Wrap_Panel(
      List(output_state_button, auto_update_button,
        update_button, pretty_text_area.search_label, pretty_text_area.search_field, zoom))

  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later {
          handle_resize()
          output_state_button.load()
          handle_update(do_update, None)
        }

      case changed: Session.Commands_Changed =>
        val restriction = if (changed.assignment) None else Some(changed.commands)
        GUI_Thread.later { handle_update(do_update, restriction) }

      case Session.Caret_Focus =>
        GUI_Thread.later { handle_update(do_update, None) }
    }

  override def init(): Unit = {
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    handle_update(true, None)
  }

  override def exit(): Unit = {
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    PIDE.session.caret_focus -= main
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })
}
