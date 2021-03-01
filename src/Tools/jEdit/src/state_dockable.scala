/*  Title:      Tools/jEdit/src/state_dockable.scala
    Author:     Makarius

Dockable window for proof state output.
*/

package isabelle.jedit


import isabelle._
import isabelle.jedit_base.Dockable

import scala.swing.{Button, CheckBox}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class State_Dockable(view: View, position: String) extends Dockable(view, position)
{
  GUI_Thread.require {}


  /* text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  override def detach_operation: Option[() => Unit] = pretty_text_area.detach_operation

  private val print_state =
    new Query_Operation(PIDE.editor, view, "print_state", _ => (),
      (snapshot, results, body) =>
        pretty_text_area.update(snapshot, results, Pretty.separate(body)))


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })

  private def handle_resize(): Unit =
  {
    GUI_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom.factor / 100))
  }


  /* update */

  def update_request(): Unit =
    GUI_Thread.require { print_state.apply_query(Nil) }

  def update(): Unit =
  {
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

  private val auto_update_button = new CheckBox("Auto update") {
    tooltip = "Indicate automatic update following cursor movement"
    reactions += { case ButtonClicked(_) => auto_update_enabled = this.selected; auto_update() }
    selected = auto_update_enabled
  }

  private val update_button = new Button("<html><b>Update</b></html>") {
    tooltip = "Update display according to the command at cursor position"
    reactions += { case ButtonClicked(_) => update_request() }
  }

  private val locate_button = new Button("Locate") {
    tooltip = "Locate printed command within source text"
    reactions += { case ButtonClicked(_) => print_state.locate_query() }
  }

  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private val controls =
    Wrap_Panel(
      List(auto_update_button, update_button,
        locate_button, pretty_text_area.search_label, pretty_text_area.search_field, zoom))

  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later { handle_resize() }

      case changed: Session.Commands_Changed =>
        if (changed.assignment) GUI_Thread.later { auto_update() }

      case Session.Caret_Focus =>
        GUI_Thread.later { auto_update() }
    }

  override def init(): Unit =
  {
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    handle_resize()
    print_state.activate()
    auto_update()
  }

  override def exit(): Unit =
  {
    print_state.deactivate()
    PIDE.session.caret_focus -= main
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    delay_resize.revoke()
  }
}
