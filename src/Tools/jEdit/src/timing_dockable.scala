/*  Title:      Tools/jEdit/src/timing_dockable.scala
    Author:     Makarius

Dockable window for timing information.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{Label, ListView, Alignment, ScrollPane, Component, TextField}
import scala.swing.event.{MouseClicked, ValueChanged}

import java.awt.BorderLayout
import javax.swing.{JList, BorderFactory}

import org.gjt.sp.jedit.View


class Timing_Dockable(view: View, position: String) extends Dockable(view, position) {
  /* entry */

  private object Entry {
    object Ordering extends scala.math.Ordering[Entry] {
      def compare(entry1: Entry, entry2: Entry): Int =
        entry2.timing compare entry1.timing
    }

    def make_gui_style(command: Boolean = false): String =
      HTML.background_property(
        if (command) view.getTextArea.getPainter.getMultipleSelectionColor
        else view.getTextArea.getPainter.getSelectionColor)

    class Renderer extends ListView.Renderer[Entry] {
      private object component extends Label {
        opaque = false
        xAlignment = Alignment.Leading
        border = BorderFactory.createEmptyBorder(2, 2, 2, 2)
      }

      def componentFor(
        list: ListView[_ <: Timing_Dockable.this.Entry],
        isSelected: Boolean,
        focused: Boolean,
        entry: Entry,
        index: Int
      ): Component = {
        component.text = entry.gui_text
        component
      }
    }
  }

  private abstract class Entry {
    def depth: Int = 0
    def timing: Double
    def gui_style: String = ""
    def gui_name: GUI.Name
    def gui_text: String = {
      val style = GUI.Style_HTML
      val bullet = if (depth == 0) style.triangular_bullet else style.regular_bullet
      style.enclose_style(gui_style,
        style.spaces(4 * depth) + bullet + " " +
        style.make_text(Time.print_seconds(timing) + "s ") +
        gui_name.set_style(style).toString)
    }
    def follow(snapshot: Document.Snapshot): Unit
  }

  private case class Theory_Entry(name: Document.Node.Name, timing: Double)
  extends Entry {
    def make_current: Theory_Entry =
      new Theory_Entry(name, timing) { override val gui_style: String = Entry.make_gui_style() }
    def gui_name: GUI.Name = GUI.Name(name.theory, kind = "theory")
    def follow(snapshot: Document.Snapshot): Unit =
      PIDE.editor.goto_file(true, view, name.node)
  }

  private case class Command_Entry(command: Command, timing: Double) extends Entry {
    override def depth: Int = 1
    override val gui_style: String = Entry.make_gui_style(command = true)
    def gui_name: GUI.Name = GUI.Name(command.span.name, kind = "command")
    def follow(snapshot: Document.Snapshot): Unit =
      PIDE.editor.hyperlink_command(true, snapshot, command.id).foreach(_.follow(view))
  }


  /* timing view */

  private val timing_view = new ListView(List.empty[Entry]) {
    listenTo(mouse.clicks)
    reactions += {
      case MouseClicked(_, point, _, clicks, _) if clicks == 2 =>
        val index = peer.locationToIndex(point)
        if (index >= 0) listData(index).follow(PIDE.session.snapshot())
    }
  }
  timing_view.peer.setLayoutOrientation(JList.VERTICAL_WRAP)
  timing_view.peer.setVisibleRowCount(0)
  timing_view.selection.intervalMode = ListView.IntervalMode.Single
  timing_view.renderer = new Entry.Renderer

  set_content(new ScrollPane(timing_view))


  /* timing threshold */

  private var timing_threshold = PIDE.options.real("editor_timing_threshold")

  private val threshold_tooltip = "Threshold for timing display (seconds)"
  private val threshold_value = new TextField(Time.print_seconds(timing_threshold)) {
    reactions += {
      case _: ValueChanged =>
        text match {
          case Value.Double(x) if x >= 0.0 => timing_threshold = x
          case _ =>
        }
        handle_update()
    }
    tooltip = threshold_tooltip
    verifier = { case Value.Double(x) => x >= 0.0 case _ => false }
  }
  private val threshold_label =
    new GUI.Label("Threshold: ", threshold_value) { tooltip = threshold_tooltip }

  private val controls = Wrap_Panel(List(threshold_label, threshold_value))

  add(controls.peer, BorderLayout.NORTH)


  /* component state -- owned by GUI thread */

  private var nodes_status = Document_Status.Nodes_Status.empty

  private def make_entries(): List[Entry] = {
    GUI_Thread.require {}

    val name =
      Document_View.get(view.getTextArea) match {
        case None => Document.Node.Name.empty
        case Some(doc_view) => doc_view.model.node_name
      }

    val theories =
      List.from(
        for ((a, st) <- nodes_status.iterator if st.command_timings.nonEmpty)
          yield Theory_Entry(a, st.total_time.seconds)).sorted(Entry.Ordering)
    val commands =
      (for ((command, timings) <- nodes_status(name).command_timings.toList)
        yield Command_Entry(command, timings.sum.elapsed.seconds)).sorted(Entry.Ordering)

    theories.flatMap(entry =>
      if (entry.name == name) entry.make_current :: commands
      else List(entry))
  }

  private def handle_update(restriction: Option[Set[Document.Node.Name]] = None): Unit = {
    GUI_Thread.require {}

    val snapshot = PIDE.session.snapshot()

    val domain =
      restriction.getOrElse(
        snapshot.version.nodes.names_iterator
          .filterNot(PIDE.resources.loaded_theory).toSet)

    nodes_status =
      nodes_status.update_nodes(PIDE.resources, snapshot.state, snapshot.version,
        threshold = Time.seconds(timing_threshold),
        domain = Some(domain))

    val entries = make_entries()
    if (timing_view.listData.toList != entries) timing_view.listData = entries
  }


  /* main */

  private val main =
    Session.Consumer[Session.Commands_Changed](getClass.getName) {
      case changed =>
        GUI_Thread.later { handle_update(Some(changed.nodes)) }
    }

  override def init(): Unit = {
    PIDE.session.commands_changed += main
    handle_update()
  }

  override def exit(): Unit = {
    PIDE.session.commands_changed -= main
  }
}
