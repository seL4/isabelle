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

  private var zoom_factor = 100
  private var current_snapshot = Document.State.init.snapshot()
  private var current_state = Command.empty.init_state
  private var current_output: List[XML.Tree] = Nil
  private var current_location: Option[Command] = None


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)


  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(Rendering.font_family(),
      (Rendering.font_size("jedit_font_scale") * zoom_factor / 100).round)
  }

  private def handle_output()
  {
    Swing_Thread.require()
  }

  private def apply_query(text: String)
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        val snapshot = doc_view.model.snapshot()
        current_location = snapshot.node.command_at(doc_view.text_area.getCaretPosition).map(_._1)
      case None =>
    }
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
              Swing_Thread.later { handle_output() }
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
