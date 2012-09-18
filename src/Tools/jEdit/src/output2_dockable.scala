/*  Title:      Tools/jEdit/src/output2_dockable.scala
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


class Output2_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()


  /* component state -- owned by Swing thread */

  private var zoom_factor = 100
  private var show_tracing = false
  private var do_update = true
  private var current_state = Command.empty.init_state
  private var current_output: List[XML.Tree] = Nil


  /* pretty text panel */

  private val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)


  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(Isabelle.font_family(),
      scala.math.round(Isabelle.font_size() * zoom_factor / 100))
  }

  private def handle_update(follow: Boolean, restriction: Option[Set[Command]])
  {
    Swing_Thread.require()

    val new_state =
      if (follow) {
        Document_View(view.getTextArea) match {
          case Some(doc_view) =>
            val snapshot = doc_view.model.snapshot()
            snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
              case Some(cmd) => snapshot.state.command_state(snapshot.version, cmd)
              case None => Command.empty.init_state
            }
          case None => Command.empty.init_state
        }
      }
      else current_state

    val new_output =
      if (!restriction.isDefined || restriction.get.contains(new_state.command))
        new_state.results.iterator.map(_._2).filter(
        { // FIXME not scalable
          case XML.Elem(Markup(Isabelle_Markup.TRACING, _), _) => show_tracing
          case _ => true
        }).toList
      else current_output

    if (new_output != current_output)
      pretty_text_area.update(Library.separate(Pretty.FBreak, new_output))

    current_state = new_state
    current_output = new_output
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case Session.Global_Settings =>
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

    Isabelle.session.global_settings += main_actor
    Isabelle.session.commands_changed += main_actor
    Isabelle.session.caret_focus += main_actor
    handle_update(true, None)
  }

  override def exit()
  {
    Swing_Thread.require()

    Isabelle.session.global_settings -= main_actor
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

  private val tracing = new CheckBox("Tracing") {
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
