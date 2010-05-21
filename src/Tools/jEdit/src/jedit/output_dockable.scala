/*  Title:      Tools/jEdit/src/jedit/output_dockable.scala
    Author:     Makarius

Dockable window with result message output.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{FlowPanel, Button, CheckBox}
import scala.swing.event.ButtonClicked

import javax.swing.JPanel
import java.awt.{BorderLayout, Dimension}
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager



class Output_Dockable(view: View, position: String) extends JPanel(new BorderLayout)
{
  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))

  val html_panel = new HTML_Panel(Isabelle.system, scala.math.round(Isabelle.font_size()))
  add(html_panel, BorderLayout.CENTER)


  /* controls */

  private val zoom = Library.zoom_box(factor => { zoom_factor = factor; handle_resize() })
  zoom.tooltip = "Zoom factor for basic font size"

  private val update = new Button("Update") {
    reactions += { case ButtonClicked(_) => handle_update() }
  }
  update.tooltip = "Update display according to state of command at caret position"

  private val tracing = new CheckBox("Tracing") {
    reactions += { case ButtonClicked(_) => handle_update() }
  }
  tracing.tooltip = "Indicate output of tracing messages"

  private val debug = new CheckBox("Debug") {
    reactions += { case ButtonClicked(_) => handle_update() }
  }
  debug.tooltip = "Indicate output of debug messages (usually disabled on the prover side)"

  private val follow = new CheckBox("Follow")
  follow.selected = true
  follow.tooltip = "Indicate automatic update according to caret movement or state changes"

  private def filtered_results(document: Document, cmd: Command): List[XML.Tree] =
  {
    val show_tracing = tracing.selected
    val show_debug = debug.selected
    document.current_state(cmd).results filter {
      case Output.Message(Markup.TRACING, _, _) => show_tracing
      case Output.Message(Markup.DEBUG, _, _) => show_debug
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
              output_actor ! Render(filtered_results(document, cmd))
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


  /* actor wiring */

  private val output_actor = actor {
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

        case bad => System.err.println("output_actor: ignoring bad message " + bad)
      }
    }
  }

  override def addNotify()
  {
    super.addNotify()
    Isabelle.session.results += output_actor
    Isabelle.session.global_settings += output_actor
  }

  override def removeNotify()
  {
    Isabelle.session.results -= output_actor
    Isabelle.session.global_settings -= output_actor
    super.removeNotify()
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
