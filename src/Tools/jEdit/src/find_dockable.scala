/*  Title:      Tools/jEdit/src/find_dockable.scala
    Author:     Makarius

Dockable window for "find" dialog.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{FlowPanel, Button, Component}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.HistoryTextArea


class Find_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()


  /* component state -- owned by Swing thread */

  private val FIND_THEOREMS = "find_theorems"
  private val instance = Document_ID.make().toString

  private var zoom_factor = 100
  private var current_location: Option[Command] = None
  private var current_query: String = ""
  private var current_snapshot = Document.State.init.snapshot()
  private var current_state = Command.empty.init_state
  private var current_output: List[XML.Tree] = Nil


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)


  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(Rendering.font_family(),
      (Rendering.font_size("jedit_font_scale") * zoom_factor / 100).round)
  }

  private def handle_update()
  {
    Swing_Thread.require()

    val (new_snapshot, new_state) =
      Document_View(view.getTextArea) match {
        case Some(doc_view) =>
          val snapshot = doc_view.model.snapshot()
          if (!snapshot.is_outdated) {
            current_location match {
              case Some(cmd) =>
                (snapshot, snapshot.state.command_state(snapshot.version, cmd))
              case None =>
                (Document.State.init.snapshot(), Command.empty.init_state)
            }
          }
          else (current_snapshot, current_state)
        case None => (current_snapshot, current_state)
      }

    val new_output =
      (for {
        (_, XML.Elem(Markup(Markup.RESULT, props), List(XML.Elem(markup, body)))) <-
          new_state.results.entries
        if props.contains((Markup.KIND, FIND_THEOREMS))
        if props.contains((Markup.INSTANCE, instance))
      } yield XML.Elem(Markup(Markup.message(markup.name), markup.properties), body)).toList

    if (new_output != current_output)
      pretty_text_area.update(new_snapshot, new_state.results, Pretty.separate(new_output))

    current_snapshot = new_snapshot
    current_state = new_state
    current_output = new_output
  }

  private def clear_overlay()
  {
    Swing_Thread.require()

    for {
      command <- current_location
      buffer <- JEdit_Lib.jedit_buffer(command.node_name.node)
      model <- PIDE.document_model(buffer)
    } model.remove_overlay(command, FIND_THEOREMS, List(instance, current_query))

    current_location = None
    current_query = ""
  }

  private def apply_query(query: String)
  {
    Swing_Thread.require()

    clear_overlay()
    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        val snapshot = doc_view.model.snapshot()
        snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1) match {
          case Some(command) =>
            current_location = Some(command)
            current_query = query
            doc_view.model.insert_overlay(command, FIND_THEOREMS, List(instance, query))
          case None =>
        }
      case None =>
    }

    PIDE.flush_buffers()
  }

  private def locate_query()
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
        case _: Session.Global_Options =>
          Swing_Thread.later { handle_resize() }
        case changed: Session.Commands_Changed =>
          current_location match {
            case Some(command) if changed.commands.contains(command) =>
              Swing_Thread.later { handle_update() }
            case _ =>
          }
        case bad =>
          java.lang.System.err.println("Find_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Swing_Thread.require()

    PIDE.session.global_options += main_actor
    PIDE.session.commands_changed += main_actor
    handle_resize()
  }

  override def exit()
  {
    Swing_Thread.require()

    PIDE.session.global_options -= main_actor
    PIDE.session.commands_changed -= main_actor
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
  })


  /* controls */

  private val query = new HistoryTextArea("isabelle-find-theorems") {
    { val max = getPreferredSize; max.width = Integer.MAX_VALUE; setMaximumSize(max) }
    setColumns(25)
    setRows(1)
  }

  private val query_wrapped = Component.wrap(query)

  private val find = new Button("Find") {
    tooltip = "Find theorems meeting specified criteria"
    reactions += { case ButtonClicked(_) => apply_query(query.getText) }
  }

  private val locate = new Button("Locate") {
    tooltip = "Locate context of current query within source text"
    reactions += { case ButtonClicked(_) => locate_query() }
  }

  private val zoom = new GUI.Zoom_Box(factor => { zoom_factor = factor; handle_resize() }) {
    tooltip = "Zoom factor for output font size"
  }

  private val controls =
    new FlowPanel(FlowPanel.Alignment.Right)(query_wrapped, find, locate, zoom)
  add(controls.peer, BorderLayout.NORTH)
}
