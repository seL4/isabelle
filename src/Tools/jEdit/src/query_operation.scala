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


  /* animation */

  private val passive_icon =
    JEdit_Lib.load_image_icon(PIDE.options.string("process_passive_icon")).getImage
  private val active_icons =
    space_explode(':', PIDE.options.string("process_active_icons")).map(name =>
      JEdit_Lib.load_image_icon(name).getImage)

  val animation = new Label
  private val animation_icon =
    new AnimatedIcon(passive_icon, active_icons.toArray, 5, animation.peer)
  animation.icon = animation_icon

  private def animation_rate(rate: Int)
  {
    animation_icon.stop
    if (rate > 0) {
      animation_icon.setRate(rate)
      animation_icon.start
    }
  }


  /* implicit state -- owned by Swing thread */

  private var current_location: Option[Command] = None
  private var current_query: List[String] = Nil
  private var current_update_pending = false
  private var current_output: List[XML.Tree] = Nil
  private var current_status = Markup.FINISHED

  private def reset_state()
  {
    current_location = None
    current_query = Nil
    current_update_pending = false
    current_output = Nil
    current_status = Markup.FINISHED
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

  private def handle_update()
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
        (_, XML.Elem(Markup(Markup.RESULT, props), body)) <- state.results.entries
        if props.contains((Markup.INSTANCE, instance))
      } yield body).toList


    /* output */

    val new_output =
      for {
        List(XML.Elem(markup, body)) <- results
        if Markup.messages.contains(markup.name)
      }
      yield XML.Elem(Markup(Markup.message(markup.name), markup.properties), body)


    /* status */

    def status(name: String): Option[String] =
      results.collectFirst({ case List(XML.Elem(m, _)) if m.name == name => name })

    val new_status =
      status(Markup.FINISHED) orElse status(Markup.RUNNING) getOrElse Markup.WAITING


    /* state update */

    if (current_output != new_output || current_status != new_status) {
      if (snapshot.is_outdated)
        current_update_pending = true
      else {
        if (current_output != new_output)
          consume_result(snapshot, state.results, new_output)
        if (current_status != new_status)
          new_status match {
            case Markup.WAITING => animation_rate(5)
            case Markup.RUNNING => animation_rate(15)
            case Markup.FINISHED =>
              animation_rate(0)
              remove_overlay()
              PIDE.flush_buffers()
            case _ =>
          }
        current_output = new_output
        current_status = new_status
        current_update_pending = false
      }
    }
  }

  def apply_query(query: List[String])
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        val snapshot = doc_view.model.snapshot()
        remove_overlay()
        reset_state()
        animation_rate(0)
        snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
          case Some(command) =>
            current_location = Some(command)
            current_query = query
            current_status = Markup.WAITING
            animation_rate(5)
            doc_view.model.insert_overlay(command, operation_name, instance :: query)
          case None =>
        }
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
              (current_status != Markup.FINISHED && changed.commands.contains(command)) =>
              Swing_Thread.later { handle_update() }
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
