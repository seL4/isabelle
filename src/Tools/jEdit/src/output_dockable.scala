/*  Title:      Tools/jEdit/src/output_dockable.scala
    Author:     Makarius

Dockable window with result message output.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout

import org.gjt.sp.jedit.View


class Output_Dockable(view: View, position: String) extends Dockable(view, position) {
  dockable =>


  /* component state -- owned by GUI thread */

  private var do_update = true
  private var current_output: List[XML.Elem] = Nil


  /* output area */

  val output: Output_Area =
    new Output_Area(view) {
      override def handle_update(): Unit = dockable.handle_update()
      override def handle_shown(): Unit = split_pane_layout()
    }

  override def detach_operation: Option[() => Unit] =
    output.pretty_text_area.detach_operation

  private def handle_update(restriction: Option[Set[Command]] = None): Unit =
    GUI_Thread.require {
      for {
        snapshot <- PIDE.editor.current_node_snapshot(view)
        if !snapshot.is_outdated
        command <- PIDE.editor.current_command(view, snapshot)
        if restriction.isEmpty || restriction.get.contains(command)
      } {
        val results = snapshot.command_results(command)
        val new_output = PIDE.editor.output_messages(results)
        if (current_output != new_output) {
          output.pretty_text_area.update(snapshot, results, new_output)
          current_output = new_output
        }
      }
    }

  output.setup(dockable)
  dockable.set_content(output.split_pane)


  /* controls */

  private val output_state_button = new JEdit_Options.output_state.GUI

  private val auto_hovering_button = new JEdit_Options.auto_hovering.GUI

  private val auto_update_button = new GUI.Check("Auto update", init = do_update) {
    tooltip = "Indicate automatic update following cursor movement"
    override def clicked(state: Boolean): Unit = {
      do_update = state
      if (do_update) handle_update()
    }
  }

  private val update_button = new GUI.Button("Update") {
    tooltip = "Update display according to the command at cursor position"
    override def clicked(): Unit = handle_update()
  }

  private val controls =
    Wrap_Panel(
      List(output_state_button, auto_hovering_button, auto_update_button, update_button) :::
      output.pretty_text_area.search_zoom_components)

  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later {
          output.handle_resize()
          output_state_button.load()
          auto_hovering_button.load()
          if (do_update) handle_update()
        }

      case changed: Session.Commands_Changed =>
        val restriction = if (changed.assignment) None else Some(changed.commands)
        GUI_Thread.later { if (do_update) handle_update(restriction = restriction) }

      case Session.Caret_Focus =>
        GUI_Thread.later { if (do_update) handle_update() }
    }

  override def init(): Unit = {
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    output.init()
  }

  override def exit(): Unit = {
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    PIDE.session.caret_focus -= main
    output.exit()
  }
}
