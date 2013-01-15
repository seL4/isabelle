/*  Title:      Tools/jEdit/src/theories_dockable.scala
    Author:     Makarius

Dockable window for theories managed by prover.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{FlowPanel, Button, TextArea, Label, ListView, Alignment, ScrollPane, Component}
import scala.swing.event.{ButtonClicked, MouseClicked}

import java.lang.System
import java.awt.{BorderLayout, Graphics2D, Insets}
import javax.swing.{JList, BorderFactory}
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.{View, jEdit}


class Theories_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* status */

  private val status = new ListView(Nil: List[Document.Node.Name]) {
    listenTo(mouse.clicks)
    reactions += {
      case MouseClicked(_, point, _, clicks, _) if clicks == 2 =>
        val index = peer.locationToIndex(point)
        if (index >= 0) jEdit.openFile(view, listData(index).node)
    }
  }
  status.peer.setLayoutOrientation(JList.HORIZONTAL_WRAP)
  status.peer.setVisibleRowCount(0)
  status.selection.intervalMode = ListView.IntervalMode.Single

  set_content(new ScrollPane(status))


  /* controls */

  def phase_text(phase: Session.Phase): String =
    "Prover: " + Library.lowercase(phase.toString)

  private val session_phase = new Label(phase_text(PIDE.session.phase))
  session_phase.border = new SoftBevelBorder(BevelBorder.LOWERED)
  session_phase.tooltip = "Status of prover session"

  private def handle_phase(phase: Session.Phase)
  {
    Swing_Thread.later { session_phase.text = " " + phase_text(phase) + " " }
  }

  private val cancel = new Button("Cancel") {
    reactions += { case ButtonClicked(_) => PIDE.cancel_execution() }
  }
  cancel.tooltip = "Cancel current checking process"

  private val check = new Button("Check") {
    reactions += { case ButtonClicked(_) => PIDE.check_buffer(view.getBuffer) }
  }
  check.tooltip = "Commence full checking of current buffer"

  private val logic = Isabelle_Logic.logic_selector(true)

  private val controls =
    new FlowPanel(FlowPanel.Alignment.Right)(check, cancel, session_phase, logic)
  add(controls.peer, BorderLayout.NORTH)


  /* component state -- owned by Swing thread */

  private var nodes_status: Map[Document.Node.Name, Protocol.Node_Status] = Map.empty

  private object Node_Renderer_Component extends Label
  {
    opaque = false
    xAlignment = Alignment.Leading
    border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

    var node_name = Document.Node.Name.empty
    override def paintComponent(gfx: Graphics2D)
    {
      nodes_status.get(node_name) match {
        case Some(st) if st.total > 0 =>
          val colors = List(
            (st.unprocessed, PIDE.options.color_value("unprocessed1_color")),
            (st.running, PIDE.options.color_value("running_color")),
            (st.warned, PIDE.options.color_value("warning_color")),
            (st.failed, PIDE.options.color_value("error_color")))

          val size = peer.getSize()
          val insets = border.getBorderInsets(this.peer)
          val w = size.width - insets.left - insets.right
          val h = size.height - insets.top - insets.bottom
          var end = size.width - insets.right

          for { (n, color) <- colors }
          {
            gfx.setColor(color)
            val v = (n * (w - colors.length) / st.total) max (if (n > 0) 4 else 0)
            gfx.fillRect(end - v, insets.top, v, h)
            end = end - v - 1
          }
        case _ =>
      }
      super.paintComponent(gfx)
    }
  }

  private class Node_Renderer extends ListView.Renderer[Document.Node.Name]
  {
    def componentFor(list: ListView[_], isSelected: Boolean, focused: Boolean,
      name: Document.Node.Name, index: Int): Component =
    {
      val component = Node_Renderer_Component
      component.node_name = name
      component.text = name.theory
      component
    }
  }
  status.renderer = new Node_Renderer

  private def handle_update(restriction: Option[Set[Document.Node.Name]] = None)
  {
    Swing_Thread.now {
      val snapshot = PIDE.session.snapshot()

      val iterator =
        restriction match {
          case Some(names) => names.iterator.map(name => (name, snapshot.version.nodes(name)))
          case None => snapshot.version.nodes.entries
        }
      val nodes_status1 =
        (nodes_status /: iterator)({ case (status, (name, node)) =>
            if (PIDE.thy_load.loaded_theories(name.theory)) status
            else status + (name -> Protocol.node_status(snapshot.state, snapshot.version, node)) })

      if (nodes_status != nodes_status1) {
        nodes_status = nodes_status1
        status.listData =
          snapshot.version.nodes.topological_order.filter(
            (name: Document.Node.Name) => nodes_status.isDefinedAt(name))
      }
    }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case phase: Session.Phase => handle_phase(phase)

        case _: Session.Global_Options => Swing_Thread.later { logic.load () }

        case changed: Session.Commands_Changed => handle_update(Some(changed.nodes))

        case bad => System.err.println("Theories_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    PIDE.session.phase_changed += main_actor; handle_phase(PIDE.session.phase)
    PIDE.session.global_options += main_actor
    PIDE.session.commands_changed += main_actor; handle_update()
  }

  override def exit()
  {
    PIDE.session.phase_changed -= main_actor
    PIDE.session.global_options -= main_actor
    PIDE.session.commands_changed -= main_actor
  }
}
