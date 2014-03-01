/*  Title:      Tools/jEdit/src/simplifier_trace_dockable.scala
    Author:     Lars Hupel

Dockable window with interactive simplifier trace.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{Button, CheckBox, Orientation, Separator}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class Simplifier_Trace_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()

  /* component state -- owned by Swing thread */

  private var current_snapshot = Document.State.init.snapshot()
  private var current_state = Command.empty.init_state
  private var current_id = 0L
  private var do_update = true
  private var do_auto_reply = false


  private val text_area = new Pretty_Text_Area(view)
  set_content(text_area)

  private def get_content(snapshot: Document.Snapshot, question: Simplifier_Trace.Question): XML.Tree =
  {
    val data = question.data

    def make_button(answer: Simplifier_Trace.Answer): XML.Tree =
      XML.Wrapped_Elem(
        Markup(Markup.SIMP_TRACE, Markup.Serial(data.serial) ::: Markup.Name(answer.name)),
        Nil,
        List(XML.Text(answer.string))
      )

    def make_block(body: XML.Body): XML.Body =
      List(Pretty.Block(0, body))

    val all = Pretty.separate(
      XML.Text(data.text) ::
      data.content :::
      make_block(Library.separate(XML.Text(", "), question.answers map make_button))
    )

    XML.Elem(Markup(Markup.TEXT_FOLD, Nil), List(Pretty.block(all)))
  }

  private def set_context(snapshot: Document.Snapshot, context: Simplifier_Trace.Context)
  {
    Swing_Thread.require()
    val questions = context.questions.values
    if (do_auto_reply && !questions.isEmpty)
    {
      questions.foreach(q => Simplifier_Trace.send_reply(PIDE.session, q.data.serial, q.default_answer))
      handle_update(do_update)
    }
    else
    {
      val contents = Pretty.separate(questions.map(get_content(snapshot, _))(collection.breakOut))
      text_area.update(snapshot, Command.Results.empty, contents)
      do_paint()
    }
  }

  private def show_trace()
  {
    val trace = Simplifier_Trace.generate_trace(current_state.results)
    new Simplifier_Trace_Window(view, current_snapshot, trace)
  }

  private def do_paint()
  {
    Swing_Thread.later {
      text_area.resize(Font_Info.main(PIDE.options.real("jedit_font_scale")))
    }
  }

  private def update_contents()
  {
    set_context(
      current_snapshot,
      Simplifier_Trace.handle_results(PIDE.session, current_id, current_state.results)
    )
  }

  private def handle_resize()
  {
    do_paint()
  }

  private def handle_update(follow: Boolean)
  {
    val (new_snapshot, new_state, new_id) =
      PIDE.editor.current_node_snapshot(view) match {
        case Some(snapshot) =>
          if (follow && !snapshot.is_outdated) {
            PIDE.editor.current_command(view, snapshot) match {
              case Some(cmd) =>
                (snapshot, snapshot.state.command_state(snapshot.version, cmd), cmd.id)
              case None =>
                (Document.State.init.snapshot(), Command.empty.init_state, 0L)
            }
          }
          else (current_snapshot, current_state, current_id)
        case None => (current_snapshot, current_state, current_id)
      }

    current_snapshot = new_snapshot
    current_state = new_state
    current_id = new_id
    update_contents()
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case _: Session.Global_Options =>
          Swing_Thread.later { handle_resize() }
        case changed: Session.Commands_Changed =>
          Swing_Thread.later { handle_update(do_update) }
        case Session.Caret_Focus =>
          Swing_Thread.later { handle_update(do_update) }
        case Simplifier_Trace.Event =>
          Swing_Thread.later { handle_update(do_update) }
        case bad => System.err.println("Simplifier_Trace_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Swing_Thread.require()

    PIDE.session.global_options += main_actor
    PIDE.session.commands_changed += main_actor
    PIDE.session.caret_focus += main_actor
    PIDE.session.trace_events += main_actor
    handle_update(true)
  }

  override def exit()
  {
    Swing_Thread.require()

    PIDE.session.global_options -= main_actor
    PIDE.session.commands_changed -= main_actor
    PIDE.session.caret_focus -= main_actor
    PIDE.session.trace_events -= main_actor
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
    override def componentShown(e: ComponentEvent)   { delay_resize.invoke() }
  })


  /* controls */

  private val controls = new Wrap_Panel(Wrap_Panel.Alignment.Right)(
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
    new CheckBox("Auto reply") {
      selected = do_auto_reply
      reactions += {
        case ButtonClicked(_) =>
          do_auto_reply = this.selected
          handle_update(do_update)
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
          Simplifier_Trace.clear_memory()
      }
    }
  )

  add(controls.peer, BorderLayout.NORTH)
}
