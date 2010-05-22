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
  val html_panel = new HTML_Panel(Isabelle.system, scala.math.round(Isabelle.font_size()))
  add(html_panel, BorderLayout.CENTER)


  /* controls */

  private val zoom = new Library.Zoom_Box(factor => { zoom_factor = factor; handle_resize() })
  zoom.tooltip = "Zoom factor for basic font size"

  private val update = new Button("Update") {
    reactions += { case ButtonClicked(_) => handle_update() }
  }
  update.tooltip =
    "<html>Update display according to the<br>state of command at caret position</html>"

  private val tracing = new CheckBox("Tracing") {
    reactions += { case ButtonClicked(_) => handle_update() }
  }
  tracing.tooltip =
    "<html>Indicate output of tracing messages<br>(also needs to be enabled on the prover side)</html>"

  private val debug = new CheckBox("Debug") {
    reactions += { case ButtonClicked(_) => handle_update() }
  }
  debug.tooltip =
    "<html>Indicate output of debug messages<br>(also needs to be enabled on the prover side)</html>"

  private val follow = new CheckBox("Follow")
  follow.selected = true
  follow.tooltip =
    "<html>Indicate automatic update following<br>caret movement or state changes</html>"

  private def filtered_results(document: Document, cmd: Command): List[XML.Tree] =
  {
    val show_tracing = tracing.selected
    val show_debug = debug.selected
    document.current_state(cmd).results filter {
      case XML.Elem(Markup.TRACING, _, _) => show_tracing
      case XML.Elem(Markup.DEBUG, _, _) => show_debug
      case _ => true
    }
  }

  private case class Render(body: List[XML.Tree])

  private def handle_update()
  {
    Swing_Thread.now {
      Document_Model(view.getBuffer) match {
        case Some(model) =>
          val document = model.recent_document
          document.command_at(view.getTextArea.getCaretPosition) match {
            case Some((cmd, _)) =>
              main_actor ! Render(filtered_results(document, cmd))
            case None =>
          }
        case None =>
      }
    }
  }

  private var zoom_factor = 100

  private def handle_resize() =
    Swing_Thread.now {
      html_panel.resize(scala.math.round(Isabelle.font_size() * zoom_factor / 100))
    }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case Session.Global_Settings => handle_resize()
        case Render(body) => html_panel.render(body)

        case cmd: Command =>
          Swing_Thread.now {
            if (follow.selected) Document_Model(view.getBuffer) else None
          } match {
            case None =>
            case Some(model) =>
              html_panel.render(filtered_results(model.recent_document, cmd))
          }

        case bad => System.err.println("Output_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Isabelle.session.results += main_actor
    Isabelle.session.global_settings += main_actor
  }

  override def exit()
  {
    Isabelle.session.results -= main_actor
    Isabelle.session.global_settings -= main_actor
  }


  /* resize */

  addComponentListener(new ComponentAdapter {
    val delay = Swing_Thread.delay_last(500) { handle_resize() }
    override def componentResized(e: ComponentEvent) { delay() }
  })


  /* init controls */

  val controls = new FlowPanel(FlowPanel.Alignment.Right)(zoom, update, debug, tracing, follow)
  add(controls.peer, BorderLayout.NORTH)

  handle_update()
}
