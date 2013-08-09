/*  Title:      Tools/jEdit/src/query_operation.scala
    Author:     Makarius

One-shot query operations via asynchronous print functions and temporary
document overlay.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.Label

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.AnimatedIcon


object Query_Operation
{
  def apply(
      view: View,
      name: String,
      consume: (Document.Snapshot, Command.Results, XML.Body) => Unit) =
    new Query_Operation(view, name, consume)
}

final class Query_Operation private(
  view: View,
  operation_name: String,
  consume_result: (Document.Snapshot, Command.Results, XML.Body) => Unit)
{
  private val instance = Document_ID.make().toString


  /* implicit state -- owned by Swing thread */

  private object Status extends Enumeration
  {
    val WAITING = Value("waiting")
    val RUNNING = Value("running")
    val FINISHED = Value("finished")
  }

  private var current_location: Option[Command] = None
  private var current_query: List[String] = Nil
  private var current_update_pending = false
  private var current_output: List[XML.Tree] = Nil
  private var current_status = Status.FINISHED
  private var current_exec_id = Document_ID.none

  private def reset_state()
  {
    current_location = None
    current_query = Nil
    current_update_pending = false
    current_output = Nil
    current_status = Status.FINISHED
    current_exec_id = Document_ID.none
  }

  private def remove_overlay()
  {
    Swing_Thread.require()

    for {
      command <- current_location
      buffer <- JEdit_Lib.jedit_buffer(command.node_name.node)
      model <- PIDE.document_model(buffer)
    } model.remove_overlay(command, operation_name, instance :: current_query)
  }


  /* animation */

  val animation = new Label

  private val passive_icon =
    JEdit_Lib.load_image_icon(PIDE.options.string("process_passive_icon")).getImage
  private val active_icons =
    space_explode(':', PIDE.options.string("process_active_icons")).map(name =>
      JEdit_Lib.load_image_icon(name).getImage)

  private val animation_icon =
    new AnimatedIcon(passive_icon, active_icons.toArray, 5, animation.peer)
  animation.icon = animation_icon

  private def animation_update()
  {
    animation_icon.stop
    current_status match {
      case Status.WAITING =>
        animation.tooltip = "Waiting for evaluation of query context ..."
        animation_icon.setRate(5)
        animation_icon.start
      case Status.RUNNING =>
        animation.tooltip = "Running query operation ..."
        animation_icon.setRate(15)
        animation_icon.start
      case Status.FINISHED =>
        animation.tooltip = null
    }
  }


  /* content update */

  private def content_update()
  {
    Swing_Thread.require()


    /* snapshot */

    val (snapshot, state) =
      current_location match {
        case Some(cmd) =>
          val snapshot = PIDE.document_snapshot(cmd.node_name)
          val state = snapshot.state.command_state(snapshot.version, cmd)
          (snapshot, state)
        case None =>
          (Document.State.init.snapshot(), Command.empty.init_state)
      }

    val results =
      (for {
        (_, elem @ XML.Elem(Markup(Markup.RESULT, props), _)) <- state.results.entries
        if props.contains((Markup.INSTANCE, instance))
      } yield elem).toList


    /* output */

    val new_output =
      for {
        XML.Elem(_, List(XML.Elem(markup, body))) <- results
        if Markup.messages.contains(markup.name)
      } yield XML.Elem(Markup(Markup.message(markup.name), markup.properties), body)


    /* status */

    def get_status(name: String, status: Status.Value): Option[Status.Value] =
      results.collectFirst({ case XML.Elem(_, List(elem: XML.Elem)) if elem.name == name => status })

    val new_status =
      get_status(Markup.FINISHED, Status.FINISHED) orElse
      get_status(Markup.RUNNING, Status.RUNNING) getOrElse
      Status.WAITING

    if (new_status == Status.RUNNING)
      results.collectFirst(
      {
        case XML.Elem(Markup(_, Position.Id(id)), List(elem: XML.Elem))
        if elem.name == Markup.RUNNING => id
      }).foreach(id => current_exec_id = id)


    /* state update */

    if (current_output != new_output || current_status != new_status) {
      if (snapshot.is_outdated)
        current_update_pending = true
      else {
        current_update_pending = false
        if (current_output != new_output) {
          current_output = new_output
          consume_result(snapshot, state.results, new_output)
        }
        if (current_status != new_status) {
          current_status = new_status
          animation_update()
          if (new_status == Status.FINISHED) {
            remove_overlay()
            PIDE.flush_buffers()
          }
        }
      }
    }
  }


  /* query operations */

  def cancel_query(): Unit =
    Swing_Thread.require { PIDE.session.cancel_exec(current_exec_id) }

  def apply_query(query: List[String])
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        val snapshot = doc_view.model.snapshot()
        remove_overlay()
        reset_state()
        snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
          case Some(command) =>
            current_location = Some(command)
            current_query = query
            current_status = Status.WAITING
            doc_view.model.insert_overlay(command, operation_name, instance :: query)
          case None =>
        }
        animation_update()
        PIDE.flush_buffers()
      case None =>
    }
  }

  def locate_query()
  {
    Swing_Thread.require()

    current_location match {
      case Some(command) =>
        val snapshot = PIDE.document_snapshot(command.node_name)
        val commands = snapshot.node.commands
        if (commands.contains(command)) {
          // FIXME revert offset (!?)
          val sources = commands.iterator.takeWhile(_ != command).map(_.source)
          val (line, column) = ((1, 1) /: sources)(Symbol.advance_line_column)
          Hyperlink(command.node_name.node, line, column).follow(view)
        }
      case None =>
    }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case changed: Session.Commands_Changed =>
          current_location match {
            case Some(command)
            if current_update_pending ||
              (current_status != Status.FINISHED && changed.commands.contains(command)) =>
              Swing_Thread.later { content_update() }
            case _ =>
          }
        case bad =>
          java.lang.System.err.println("Query_Operation: ignoring bad message " + bad)
      }
    }
  }

  def activate() { PIDE.session.commands_changed += main_actor }
  def deactivate() { PIDE.session.commands_changed -= main_actor }
}
