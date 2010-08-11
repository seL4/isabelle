/*  Title:      Tools/jEdit/src/jedit/output_dockable.scala
    Author:     Makarius

Dockable window with result message output.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{FlowPanel, Button, CheckBox}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class Output_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()

  val html_panel =
    new HTML_Panel(Isabelle.system, Isabelle.font_family(), scala.math.round(Isabelle.font_size()))
  add(html_panel, BorderLayout.CENTER)


  /* component state -- owned by Swing thread */

  private var zoom_factor = 100
  private var show_debug = false
  private var show_tracing = false
  private var follow_caret = true
  private var current_command: Option[Command] = None


  private def handle_resize()
  {
    Swing_Thread.now {
      html_panel.resize(Isabelle.font_family(),
        scala.math.round(Isabelle.font_size() * zoom_factor / 100))
    }
  }

  private def handle_perspective(): Boolean =
    Swing_Thread.now {
      Document_View(view.getTextArea) match {
        case Some(doc_view) =>
          val cmd = doc_view.selected_command()
          if (current_command == cmd) false
          else { current_command = cmd; true }
        case None => false
      }
    }

  private def handle_update(restriction: Option[Set[Command]] = None)
  {
    Swing_Thread.now {
      if (follow_caret) handle_perspective()
      Document_View(view.getTextArea) match {
        case Some(doc_view) =>
          current_command match {
            case Some(cmd) if !restriction.isDefined || restriction.get.contains(cmd) =>
              val snapshot = doc_view.model.snapshot()
              val filtered_results =
                snapshot.state(cmd).results filter {
                  case XML.Elem(Markup(Markup.TRACING, _), _) => show_tracing
                  case XML.Elem(Markup(Markup.DEBUG, _), _) => show_debug
                  case _ => true
                }
              html_panel.render(filtered_results)
            case _ =>
          }
        case None =>
      }
    }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case Session.Global_Settings => handle_resize()
        case Command_Set(changed) => handle_update(Some(changed))
        case Session.Perspective => if (follow_caret && handle_perspective()) handle_update()
        case bad => System.err.println("Output_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Isabelle.session.global_settings += main_actor
    Isabelle.session.commands_changed += main_actor
    Isabelle.session.perspective += main_actor
  }

  override def exit()
  {
    Isabelle.session.global_settings -= main_actor
    Isabelle.session.commands_changed -= main_actor
    Isabelle.session.perspective -= main_actor
  }


  /* resize */

  addComponentListener(new ComponentAdapter {
    val delay = Swing_Thread.delay_last(Isabelle.session.update_delay) { handle_resize() }
    override def componentResized(e: ComponentEvent) { delay() }
  })


  /* controls */

  private val zoom = new Library.Zoom_Box(factor => { zoom_factor = factor; handle_resize() })
  zoom.tooltip = "Zoom factor for basic font size"

  private val debug = new CheckBox("Debug") {
    reactions += { case ButtonClicked(_) => show_debug = this.selected; handle_update() }
  }
  debug.selected = show_debug
  debug.tooltip =
    "<html>Indicate output of debug messages<br>(also needs to be enabled on the prover side)</html>"

  private val tracing = new CheckBox("Tracing") {
    reactions += { case ButtonClicked(_) => show_tracing = this.selected; handle_update() }
  }
  tracing.selected = show_tracing
  tracing.tooltip = "Indicate output of tracing messages"

  private val auto_update = new CheckBox("Auto update") {
    reactions += { case ButtonClicked(_) => follow_caret = this.selected; handle_update() }
  }
  auto_update.selected = follow_caret
  auto_update.tooltip = "Indicate automatic update following cursor movement"

  private val update = new Button("Update") {
    reactions += { case ButtonClicked(_) => handle_perspective(); handle_update() }
  }
  update.tooltip = "Update display according to the command at cursor position"

  val controls = new FlowPanel(FlowPanel.Alignment.Right)(zoom, debug, tracing, auto_update, update)
  add(controls.peer, BorderLayout.NORTH)

  handle_update()
}
