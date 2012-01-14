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

  private val html_panel =
    new HTML_Panel(Isabelle.font_family(), scala.math.round(Isabelle.font_size()))
  {
    override val handler: PartialFunction[HTML_Panel.Event, Unit] = {
      case HTML_Panel.Mouse_Click(elem, event) if elem.getClassName() == "sendback" =>
        val text = elem.getFirstChild().getNodeValue()

        Document_View(view.getTextArea) match {
          case Some(doc_view) =>
            val cmd = current_command.get
            val start_ofs = doc_view.update_snapshot().node.command_start(cmd).get
            val buffer = view.getBuffer
            buffer.beginCompoundEdit()
            buffer.remove(start_ofs, cmd.length)
            buffer.insert(start_ofs, text)
            buffer.endCompoundEdit()
          case None =>
        }
    }       
  }

  set_content(html_panel)


  /* component state -- owned by Swing thread */

  private var zoom_factor = 100
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
              val snapshot = doc_view.update_snapshot()
              val filtered_results =
                snapshot.state.command_state(snapshot.version, cmd).results.iterator
                  .map(_._2).filter(
                  { // FIXME not scalable
                    case XML.Elem(Markup(Isabelle_Markup.TRACING, _), _) => show_tracing
                    case _ => true
                  }).toList
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
        case changed: Session.Commands_Changed => handle_update(Some(changed.commands))
        case Session.Caret_Focus => if (follow_caret && handle_perspective()) handle_update()
        case bad => System.err.println("Output_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Isabelle.session.global_settings += main_actor
    Isabelle.session.commands_changed += main_actor
    Isabelle.session.caret_focus += main_actor
  }

  override def exit()
  {
    Isabelle.session.global_settings -= main_actor
    Isabelle.session.commands_changed -= main_actor
    Isabelle.session.caret_focus -= main_actor
  }


  /* resize */

  addComponentListener(new ComponentAdapter {
    val delay = Swing_Thread.delay_last(Isabelle.session.update_delay) { handle_resize() }
    override def componentResized(e: ComponentEvent) { delay() }
  })


  /* controls */

  private val zoom = new Library.Zoom_Box(factor => { zoom_factor = factor; handle_resize() })
  zoom.tooltip = "Zoom factor for basic font size"

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

  private val controls = new FlowPanel(FlowPanel.Alignment.Right)(zoom, tracing, auto_update, update)
  add(controls.peer, BorderLayout.NORTH)

  handle_update()
}
