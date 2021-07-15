/*  Title:      Tools/jEdit/src/simplifier_trace_dockable.scala
    Author:     Lars Hupel

Dockable window with interactive simplifier trace.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{Button, CheckBox, Orientation, Separator}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class Simplifier_Trace_Dockable(view: View, position: String) extends Dockable(view, position)
{
  GUI_Thread.require {}


  /* component state -- owned by GUI thread */

  private var current_snapshot = Document.State.init.snapshot()
  private var current_command = Command.empty
  private var current_results = Command.Results.empty
  private var current_id = 0L
  private var do_update = true


  private val text_area = new Pretty_Text_Area(view)
  set_content(text_area)

  private def update_contents(): Unit =
  {
    val snapshot = current_snapshot
    val context = Simplifier_Trace.handle_results(PIDE.session, current_id, current_results)

    answers.contents.clear()
    context.questions.values.toList match {
      case q :: _ =>
        val data = q.data
        val content = Pretty.separate(XML.Text(data.text) :: data.content)
        text_area.update(snapshot, Command.Results.empty, content)
        q.answers.foreach { answer =>
          answers.contents += new Button(answer.string) {
            reactions += {
              case ButtonClicked(_) =>
                Simplifier_Trace.send_reply(PIDE.session, data.serial, answer)
            }
          }
        }
      case Nil =>
        text_area.update(snapshot, Command.Results.empty, Nil)
    }

    do_paint()
  }

  private def show_trace(): Unit =
  {
    val trace = Simplifier_Trace.generate_trace(PIDE.session, current_results)
    new Simplifier_Trace_Window(view, current_snapshot, trace)
  }

  private def do_paint(): Unit =
  {
    GUI_Thread.later {
      text_area.resize(Font_Info.main(PIDE.options.real("jedit_font_scale")))
    }
  }

  private def handle_resize(): Unit = do_paint()

  private def handle_update(follow: Boolean): Unit =
  {
    val (new_snapshot, new_command, new_results, new_id) =
      PIDE.editor.current_node_snapshot(view) match {
        case Some(snapshot) =>
          if (follow && !snapshot.is_outdated) {
            PIDE.editor.current_command(view, snapshot) match {
              case Some(cmd) =>
                (snapshot, cmd, snapshot.command_results(cmd), cmd.id)
              case None =>
                (Document.State.init.snapshot(), Command.empty, Command.Results.empty, 0L)
            }
          }
          else (current_snapshot, current_command, current_results, current_id)
        case None => (current_snapshot, current_command, current_results, current_id)
      }

    current_snapshot = new_snapshot
    current_command = new_command
    current_results = new_results
    current_id = new_id
    update_contents()
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later { handle_resize() }

      case changed: Session.Commands_Changed =>
        GUI_Thread.later { handle_update(do_update) }

      case Session.Caret_Focus =>
        GUI_Thread.later { handle_update(do_update) }

      case Simplifier_Trace.Event =>
        GUI_Thread.later { handle_update(do_update) }
    }

  override def init(): Unit =
  {
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    PIDE.session.trace_events += main
    handle_update(true)
  }

  override def exit(): Unit =
  {
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    PIDE.session.caret_focus -= main
    PIDE.session.trace_events -= main
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })


  /* controls */

  private val controls =
    Wrap_Panel(
      List(
        new CheckBox("Auto update") {
          selected = do_update
          reactions += {
            case ButtonClicked(_) =>
              do_update = this.selected
              handle_update(do_update)
          }
        },
        new Button("Update") {
          reactions += {
            case ButtonClicked(_) =>
              handle_update(true)
          }
        },
        new Separator(Orientation.Vertical),
        new Button("Show trace") {
          reactions += {
            case ButtonClicked(_) =>
              show_trace()
          }
        },
        new Button("Clear memory") {
          reactions += {
            case ButtonClicked(_) =>
              Simplifier_Trace.clear_memory(PIDE.session)
          }
        }))

  private val answers = Wrap_Panel(Nil, Wrap_Panel.Alignment.Left)

  add(controls.peer, BorderLayout.NORTH)
  add(answers.peer, BorderLayout.SOUTH)
}
