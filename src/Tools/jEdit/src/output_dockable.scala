/*  Title:      Tools/jEdit/src/output_dockable.scala
    Author:     Makarius

Dockable window with result message output.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{FlowPanel, Button, CheckBox}
import scala.swing.event.ButtonClicked

import java.lang.System
import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class Output_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()


  /* component state -- owned by Swing thread */

  private var zoom_factor = 100
  private var show_tracing = false
  private var do_update = true
  private var current_snapshot = Document.State.init.snapshot()
  private var current_state = Command.empty.init_state
  private var current_output: List[XML.Tree] = Nil
  private var current_tracing = 0


  /* pretty text panel */

  private val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)


  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(Isabelle.font_family(),
      scala.math.round(Isabelle.font_size("jedit_font_scale") * zoom_factor / 100))
  }

  private def handle_update(follow: Boolean, restriction: Option[Set[Command]])
  {
    Swing_Thread.require()

    val (new_snapshot, new_state) =
      Document_View(view.getTextArea) match {
        case Some(doc_view) =>
          val snapshot = doc_view.model.snapshot()
          if (follow && !snapshot.is_outdated) {
            snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
              case Some(cmd) =>
                (snapshot, snapshot.state.command_state(snapshot.version, cmd))
              case None =>
                (Document.State.init.snapshot(), Command.empty.init_state)
            }
          }
          else (current_snapshot, current_state)
        case None => (current_snapshot, current_state)
      }

    val (new_output, new_tracing) =
      if (!restriction.isDefined || restriction.get.contains(new_state.command))
      {
        val new_output =
          new_state.results.iterator.map(_._2)
            .filter(msg => !Protocol.is_tracing(msg) || show_tracing).toList
        val new_tracing =
          new_state.results.iterator.map(_._2).filter(Protocol.is_tracing(_)).length
        (new_output, new_tracing)
      }
      else (current_output, current_tracing)

    if (new_output != current_output)
      pretty_text_area.update(new_snapshot, Library.separate(Pretty.Separator, new_output))

    if (new_tracing != current_tracing)
      tracing.text = tracing_text(new_tracing)

    current_snapshot = new_snapshot
    current_state = new_state
    current_output = new_output
    current_tracing = new_tracing
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case Session.Global_Options =>
          Swing_Thread.later { handle_resize() }
        case changed: Session.Commands_Changed =>
          Swing_Thread.later { handle_update(do_update, Some(changed.commands)) }
        case Session.Caret_Focus =>
          Swing_Thread.later { handle_update(do_update, None) }
        case bad => System.err.println("Output_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Swing_Thread.require()

    Isabelle.session.global_options += main_actor
    Isabelle.session.commands_changed += main_actor
    Isabelle.session.caret_focus += main_actor
    handle_update(true, None)
  }

  override def exit()
  {
    Swing_Thread.require()

    Isabelle.session.global_options -= main_actor
    Isabelle.session.commands_changed -= main_actor
    Isabelle.session.caret_focus -= main_actor
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    Swing_Thread.delay_first(
      Time.seconds(Isabelle.options.real("editor_update_delay"))) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
  })


  /* controls */

  private val zoom = new Library.Zoom_Box(factor => { zoom_factor = factor; handle_resize() })
  zoom.tooltip = "Zoom factor for basic font size"

  private def tracing_text(n: Int): String = "Tracing (" + n.toString + ")"
  private val tracing = new CheckBox(tracing_text(current_tracing)) {
    reactions += {
      case ButtonClicked(_) => show_tracing = this.selected; handle_update(do_update, None) }
  }
  tracing.selected = show_tracing
  tracing.tooltip = "Indicate output of tracing messages"

  private val auto_update = new CheckBox("Auto update") {
    reactions += {
      case ButtonClicked(_) => do_update = this.selected; handle_update(do_update, None) }
  }
  auto_update.selected = do_update
  auto_update.tooltip = "Indicate automatic update following cursor movement"

  private val update = new Button("Update") {
    reactions += { case ButtonClicked(_) => handle_update(true, None) }
  }
  update.tooltip = "Update display according to the command at cursor position"

  private val controls = new FlowPanel(FlowPanel.Alignment.Right)(zoom, tracing, auto_update, update)
  add(controls.peer, BorderLayout.NORTH)
}
