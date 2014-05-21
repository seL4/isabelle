/*  Title:      Tools/jEdit/src/output_dockable.scala
    Author:     Makarius

Dockable window with result message output.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{Button, CheckBox}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class Output_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* component state -- owned by Swing thread */

  private var do_update = true
  private var current_snapshot = Document.Snapshot.init
  private var current_command = Command.empty
  private var current_results = Command.Results.empty
  private var current_output: List[XML.Tree] = Nil


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  override def detach_operation = pretty_text_area.detach_operation


  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private def handle_resize()
  {
    Swing_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom.factor / 100))
  }

  private def handle_update(follow: Boolean, restriction: Option[Set[Command]])
  {
    Swing_Thread.require {}

    val (new_snapshot, new_command, new_results) =
      PIDE.editor.current_node_snapshot(view) match {
        case Some(snapshot) =>
          if (follow && !snapshot.is_outdated) {
            PIDE.editor.current_command(view, snapshot) match {
              case Some(cmd) =>
                (snapshot, cmd, snapshot.state.command_results(snapshot.version, cmd))
              case None =>
                (Document.Snapshot.init, Command.empty, Command.Results.empty)
            }
          }
          else (current_snapshot, current_command, current_results)
        case None => (current_snapshot, current_command, current_results)
      }

    val new_output =
      if (!restriction.isDefined || restriction.get.contains(new_command)) {
        val rendering = Rendering(new_snapshot, PIDE.options.value)
        rendering.output_messages(new_results)
      }
      else current_output

    if (new_output != current_output)
      pretty_text_area.update(new_snapshot, new_results, Pretty.separate(new_output))

    current_snapshot = new_snapshot
    current_command = new_command
    current_results = new_results
    current_output = new_output
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        Swing_Thread.later { handle_resize() }

      case changed: Session.Commands_Changed =>
        val restriction = if (changed.assignment) None else Some(changed.commands)
        Swing_Thread.later { handle_update(do_update, restriction) }

      case Session.Caret_Focus =>
        Swing_Thread.later { handle_update(do_update, None) }
    }

  override def init()
  {
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    handle_update(true, None)
  }

  override def exit()
  {
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    PIDE.session.caret_focus -= main
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
  })


  /* controls */

  private val auto_update = new CheckBox("Auto update") {
    tooltip = "Indicate automatic update following cursor movement"
    reactions += {
      case ButtonClicked(_) => do_update = this.selected; handle_update(do_update, None) }
    selected = do_update
  }

  private val update = new Button("Update") {
    tooltip = "Update display according to the command at cursor position"
    reactions += { case ButtonClicked(_) => handle_update(true, None) }
  }

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(auto_update, update,
      pretty_text_area.search_label, pretty_text_area.search_field, zoom)
  add(controls.peer, BorderLayout.NORTH)
}
