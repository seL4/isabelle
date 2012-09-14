/*  Title:      Tools/jEdit/src/session_dockable.scala
    Author:     Makarius

Dockable window for prover session management.
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


class Session_Dockable(view: View, position: String) extends Dockable(view: View, position: String)
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
  status.peer.setLayoutOrientation(JList.VERTICAL_WRAP)
  status.selection.intervalMode = ListView.IntervalMode.Single

  set_content(new ScrollPane(status))


  /* controls */

  private val session_phase = new Label(Isabelle.session.phase.toString)
  session_phase.border = new SoftBevelBorder(BevelBorder.LOWERED)
  session_phase.tooltip = "Prover status"

  private def handle_phase(phase: Session.Phase)
  {
    Swing_Thread.later { session_phase.text = " " + phase.toString + " " }
  }

  private val cancel = new Button("Cancel") {
    reactions += { case ButtonClicked(_) => Isabelle.cancel_execution() }
  }
  cancel.tooltip = jEdit.getProperty("isabelle.cancel-execution.label")

  private val check = new Button("Check") {
    reactions += { case ButtonClicked(_) => Isabelle.check_buffer(view.getBuffer) }
  }
  check.tooltip = jEdit.getProperty("isabelle.check-buffer.label")

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
          val size = peer.getSize()
          val insets = border.getBorderInsets(this.peer)
          val w = size.width - insets.left - insets.right
          val h = size.height - insets.top - insets.bottom
          var end = size.width - insets.right
          for {
            (n, color) <- List(
              (st.unprocessed, Isabelle_Rendering.color_value("unprocessed1_color")),
              (st.running, Isabelle_Rendering.color_value("running_color")),
              (st.warned, Isabelle_Rendering.color_value("warning_color")),
              (st.failed, Isabelle_Rendering.color_value("error_color"))) }
          {
            gfx.setColor(color)
            val v = (n * w / st.total) max (if (n > 0) 2 else 0)
            gfx.fillRect(end - v, insets.top, v, h)
            end -= v
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
      val snapshot = Isabelle.session.snapshot()

      val iterator =
        restriction match {
          case Some(names) => names.iterator.map(name => (name, snapshot.version.nodes(name)))
          case None => snapshot.version.nodes.entries
        }
      val nodes_status1 =
        (nodes_status /: iterator)({ case (status, (name, node)) =>
            if (Isabelle.thy_load.loaded_theories(name.theory)) status
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

        case Session.Global_Settings => Swing_Thread.later { logic.load () }

        case changed: Session.Commands_Changed => handle_update(Some(changed.nodes))

        case bad => System.err.println("Session_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Isabelle.session.phase_changed += main_actor; handle_phase(Isabelle.session.phase)
    Isabelle.session.global_settings += main_actor
    Isabelle.session.commands_changed += main_actor; handle_update()
  }

  override def exit()
  {
    Isabelle.session.phase_changed -= main_actor
    Isabelle.session.global_settings -= main_actor
    Isabelle.session.commands_changed -= main_actor
  }
}
