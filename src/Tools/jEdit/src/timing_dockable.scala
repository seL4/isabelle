/*  Title:      Tools/jEdit/src/timing_dockable.scala
    Author:     Makarius

Dockable window for timing information.
*/

package isabelle.jedit


import isabelle._
import isabelle.jedit_base.Dockable

import scala.swing.{Label, ListView, Alignment, ScrollPane, Component, TextField}
import scala.swing.event.{MouseClicked, ValueChanged}

import java.awt.{BorderLayout, Graphics2D, Insets, Color}
import javax.swing.{JList, BorderFactory}
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.{View, jEdit}


class Timing_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* entry */

  private object Entry
  {
    object Ordering extends scala.math.Ordering[Entry]
    {
      def compare(entry1: Entry, entry2: Entry): Int =
        entry2.timing compare entry1.timing
    }

    object Renderer_Component extends Label
    {
      opaque = false
      xAlignment = Alignment.Leading
      border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

      var entry: Entry = null
      override def paintComponent(gfx: Graphics2D)
      {
        def paint_rectangle(color: Color)
        {
          val size = peer.getSize()
          val insets = border.getBorderInsets(peer)
          val x = insets.left
          val y = insets.top
          val w = size.width - x - insets.right
          val h = size.height - y - insets.bottom
          gfx.setColor(color)
          gfx.fillRect(x, y, w, h)
        }

        entry match {
          case theory_entry: Theory_Entry if theory_entry.current =>
            paint_rectangle(view.getTextArea.getPainter.getSelectionColor)
          case _: Command_Entry =>
            paint_rectangle(view.getTextArea.getPainter.getMultipleSelectionColor)
          case _ =>
        }
        super.paintComponent(gfx)
      }
    }

    class Renderer extends ListView.Renderer[Entry]
    {
      def componentFor(list: ListView[_ <: Timing_Dockable.this.Entry],
        isSelected: Boolean, focused: Boolean, entry: Entry, index: Int): Component =
      {
        val component = Renderer_Component
        component.entry = entry
        component.text = entry.print
        component
      }
    }
  }

  private abstract class Entry
  {
    def timing: Double
    def print: String
    def follow(snapshot: Document.Snapshot)
  }

  private case class Theory_Entry(name: Document.Node.Name, timing: Double, current: Boolean)
    extends Entry
  {
    def print: String =
      Time.print_seconds(timing) + "s theory " + quote(name.theory)
    def follow(snapshot: Document.Snapshot) { PIDE.editor.goto_file(true, view, name.node) }
  }

  private case class Command_Entry(command: Command, timing: Double) extends Entry
  {
    def print: String =
      "  " + Time.print_seconds(timing) + "s command " + quote(command.span.name)
    def follow(snapshot: Document.Snapshot)
    { PIDE.editor.hyperlink_command(true, snapshot, command.id).foreach(_.follow(view)) }
  }


  /* timing view */

  private val timing_view = new ListView(Nil: List[Entry]) {
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

  private var timing_threshold = PIDE.options.real("jedit_timing_threshold")

  private val threshold_tooltip = "Threshold for timing display (seconds)"

  private val threshold_label = new Label("Threshold: ") {
    tooltip = threshold_tooltip
  }

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
    verifier = ((s: String) =>
      s match { case Value.Double(x) => x >= 0.0 case _ => false })
  }

  private val controls = Wrap_Panel(List(threshold_label, threshold_value))

  add(controls.peer, BorderLayout.NORTH)


  /* component state -- owned by GUI thread */

  private var nodes_timing = Map.empty[Document.Node.Name, Document_Status.Overall_Timing]

  private def make_entries(): List[Entry] =
  {
    GUI_Thread.require {}

    val name =
      Document_View.get(view.getTextArea) match {
        case None => Document.Node.Name.empty
        case Some(doc_view) => doc_view.model.node_name
      }
    val timing = nodes_timing.getOrElse(name, Document_Status.Overall_Timing.empty)

    val theories =
      (for ((node_name, node_timing) <- nodes_timing.toList if node_timing.command_timings.nonEmpty)
        yield Theory_Entry(node_name, node_timing.total, false)).sorted(Entry.Ordering)
    val commands =
      (for ((command, command_timing) <- timing.command_timings.toList)
        yield Command_Entry(command, command_timing)).sorted(Entry.Ordering)

    theories.flatMap(entry =>
      if (entry.name == name) entry.copy(current = true) :: commands
      else List(entry))
  }

  private def handle_update(restriction: Option[Set[Document.Node.Name]] = None)
  {
    GUI_Thread.require {}

    val snapshot = PIDE.session.snapshot()

    val iterator =
      restriction match {
        case Some(names) => names.iterator.map(name => (name, snapshot.get_node(name)))
        case None => snapshot.version.nodes.iterator
      }
    val nodes_timing1 =
      (nodes_timing /: iterator)({ case (timing1, (name, node)) =>
          if (PIDE.resources.session_base.loaded_theory(name)) timing1
          else {
            val node_timing =
              Document_Status.Overall_Timing.make(
                snapshot.state, snapshot.version, node.commands, threshold = timing_threshold)
            timing1 + (name -> node_timing)
          }
      })
    nodes_timing = nodes_timing1

    val entries = make_entries()
    if (timing_view.listData.toList != entries) timing_view.listData = entries
  }


  /* main */

  private val main =
    Session.Consumer[Session.Commands_Changed](getClass.getName) {
      case changed =>
        GUI_Thread.later { handle_update(Some(changed.nodes)) }
    }

  override def init()
  {
    PIDE.session.commands_changed += main
    handle_update()
  }

  override def exit()
  {
    PIDE.session.commands_changed -= main
  }
}
