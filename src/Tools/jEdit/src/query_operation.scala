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


  /* status animation */

  private val passive_icon =
    JEdit_Lib.load_image_icon(PIDE.options.string("process_passive_icon")).getImage
  private val active_icons =
    space_explode(':', PIDE.options.string("process_active_icons")).map(name =>
      JEdit_Lib.load_image_icon(name).getImage)

  val animation = new Label
  val animation_icon = new AnimatedIcon(passive_icon, active_icons.toArray, 10, animation.peer)
  animation.icon = animation_icon


  /* implicit state -- owned by Swing thread */

  private var current_location: Option[Command] = None
  private var current_query: List[String] = Nil
  private var current_result = false
  private var current_snapshot = Document.State.init.snapshot()
  private var current_state = Command.empty.init_state
  private var current_output: List[XML.Tree] = Nil

  private def remove_overlay()
  {
    Swing_Thread.require()

    for {
      command <- current_location
      buffer <- JEdit_Lib.jedit_buffer(command.node_name.node)
      model <- PIDE.document_model(buffer)
    } model.remove_overlay(command, operation_name, instance :: current_query)
  }

  private def handle_result()
  {
    Swing_Thread.require()

    val (new_snapshot, new_state) =
      Document_View(view.getTextArea) match {
        case Some(doc_view) =>
          val snapshot = doc_view.model.snapshot()
          current_location match {
            case Some(cmd) =>
              (snapshot, snapshot.state.command_state(snapshot.version, cmd))
            case None =>
              (Document.State.init.snapshot(), Command.empty.init_state)
          }
        case None => (current_snapshot, current_state)
      }

    val new_output =
      (for {
        (_, XML.Elem(Markup(Markup.RESULT, props), List(XML.Elem(markup, body)))) <-
          new_state.results.entries
        if props.contains((Markup.INSTANCE, instance))
      } yield XML.Elem(Markup(Markup.message(markup.name), markup.properties), body)).toList

    if (new_output != current_output)
      consume_result(new_snapshot, new_state.results, new_output)

    if (!new_output.isEmpty) {
      current_result = true
      animation_icon.stop
      remove_overlay()
      PIDE.flush_buffers()
    }

    current_snapshot = new_snapshot
    current_state = new_state
    current_output = new_output
  }

  def apply_query(query: List[String])
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        val snapshot = doc_view.model.snapshot()
        remove_overlay()
        current_location = None
        current_query = Nil
        current_result = false
        animation_icon.start
        snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
          case Some(command) =>
            current_location = Some(command)
            current_query = query
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
        val snapshot = PIDE.session.snapshot(command.node_name)
        val commands = snapshot.node.commands
        if (commands.contains(command)) {
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
            case Some(command) if !current_result && changed.commands.contains(command) =>
              Swing_Thread.later { handle_result() }
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
