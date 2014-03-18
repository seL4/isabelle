/*  Title:      Tools/jEdit/src/theories_dockable.scala
    Author:     Makarius

Dockable window for theories managed by prover.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{Button, TextArea, Label, ListView, Alignment,
  ScrollPane, Component, CheckBox, BorderPanel}
import scala.swing.event.{MouseClicked, MouseMoved}

import java.awt.{BorderLayout, Graphics2D, Color, Point, Dimension}
import javax.swing.{JList, BorderFactory}
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.{View, jEdit}


class Theories_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* status */

  private val status = new ListView(Nil: List[Document.Node.Name]) {
    listenTo(mouse.clicks)
    listenTo(mouse.moves)
    reactions += {
      case MouseClicked(_, point, _, clicks, _) =>
        val index = peer.locationToIndex(point)
        if (index >= 0) {
          if (in_checkbox(peer.indexToLocation(index), point)) {
            if (clicks == 1) {
              for {
                buffer <- JEdit_Lib.jedit_buffer(listData(index).node)
                model <- PIDE.document_model(buffer)
              } model.node_required = !model.node_required
            }
          }
          else if (clicks == 2) PIDE.editor.goto_file(view, listData(index).node)
        }
      case MouseMoved(_, point, _) =>
        val index = peer.locationToIndex(point)
        if (index >= 0 && in_checkbox(peer.indexToLocation(index), point))
          tooltip = "Mark as required for continuous checking"
        else
          tooltip = null
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
    Swing_Thread.require()
    session_phase.text = " " + phase_text(phase) + " "
  }

  private val continuous_checking = new Isabelle.Continuous_Checking
  continuous_checking.focusable = false

  private val logic = Isabelle_Logic.logic_selector(true)

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(continuous_checking, session_phase, logic)
  add(controls.peer, BorderLayout.NORTH)


  /* component state -- owned by Swing thread */

  private var nodes_status: Map[Document.Node.Name, Protocol.Node_Status] = Map.empty
  private var nodes_required: Set[Document.Node.Name] = Set.empty

  private def update_nodes_required()
  {
    nodes_required = Set.empty
    for {
      buffer <- JEdit_Lib.jedit_buffers
      model <- PIDE.document_model(buffer)
      if model.node_required
    } nodes_required += model.node_name
  }
  update_nodes_required()

  private def in_checkbox(loc0: Point, p: Point): Boolean =
    Node_Renderer_Component != null &&
      (Node_Renderer_Component.checkbox_geometry match {
        case Some((loc, size)) =>
          loc0.x + loc.x <= p.x && p.x < loc0.x + size.width &&
          loc0.y + loc.y <= p.y && p.y < loc0.y + size.height
        case None => false
      })

  private object Node_Renderer_Component extends BorderPanel
  {
    opaque = false
    border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

    var node_name = Document.Node.Name.empty

    var checkbox_geometry: Option[(Point, Dimension)] = None
    val checkbox = new CheckBox {
      opaque = false
      override def paintComponent(gfx: Graphics2D)
      {
        super.paintComponent(gfx)
        if (location != null && size != null)
          checkbox_geometry = Some((location, size))
      }
    }

    val label = new Label {
      opaque = false
      border = BorderFactory.createEmptyBorder()
      xAlignment = Alignment.Leading

      override def paintComponent(gfx: Graphics2D)
      {
        def paint_segment(x: Int, w: Int, color: Color)
        {
          gfx.setColor(color)
          gfx.fillRect(x, 0, w, size.height)
        }

        nodes_status.get(node_name) match {
          case Some(st) if st.total > 0 =>
            val segments =
              List(
                (st.unprocessed, PIDE.options.color_value("unprocessed1_color")),
                (st.running, PIDE.options.color_value("running_color")),
                (st.warned, PIDE.options.color_value("warning_color")),
                (st.failed, PIDE.options.color_value("error_color"))
              ).filter(_._1 > 0)

            (size.width /: segments)({ case (last, (n, color)) =>
              val w = (n * (size.width - segments.length) / st.total) max 4
              paint_segment(last - w, w, color)
              last - w - 1
            })

          case _ =>
            paint_segment(0, size.width, PIDE.options.color_value("unprocessed1_color"))
        }
        super.paintComponent(gfx)
      }
    }

    layout(checkbox) = BorderPanel.Position.West
    layout(label) = BorderPanel.Position.Center
  }

  private class Node_Renderer extends ListView.Renderer[Document.Node.Name]
  {
    def componentFor(list: ListView[_], isSelected: Boolean, focused: Boolean,
      name: Document.Node.Name, index: Int): Component =
    {
      val component = Node_Renderer_Component
      component.node_name = name
      component.checkbox.selected = nodes_required.contains(name)
      component.label.text = name.theory
      component
    }
  }
  status.renderer = new Node_Renderer

  private def handle_update(restriction: Option[Set[Document.Node.Name]] = None)
  {
    Swing_Thread.require()

    val snapshot = PIDE.session.snapshot()

    val iterator =
      (restriction match {
        case Some(names) => names.iterator.map(name => (name, snapshot.version.nodes(name)))
        case None => snapshot.version.nodes.entries
      }).filter(_._1.is_theory)
    val nodes_status1 =
      (nodes_status /: iterator)({ case (status, (name, node)) =>
          if (PIDE.resources.loaded_theories(name.theory)) status
          else status + (name -> Protocol.node_status(snapshot.state, snapshot.version, node)) })

    if (nodes_status != nodes_status1) {
      nodes_status = nodes_status1
      status.listData =
        snapshot.version.nodes.topological_order.filter(
          (name: Document.Node.Name) => nodes_status.isDefinedAt(name))
    }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case phase: Session.Phase =>
          Swing_Thread.later { handle_phase(phase) }

        case _: Session.Global_Options =>
          Swing_Thread.later {
            continuous_checking.load()
            logic.load ()
            update_nodes_required()
            status.repaint()
          }

        case changed: Session.Commands_Changed =>
          Swing_Thread.later { handle_update(Some(changed.nodes)) }

        case bad => System.err.println("Theories_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    PIDE.session.phase_changed += main_actor
    PIDE.session.global_options += main_actor
    PIDE.session.commands_changed += main_actor

    handle_phase(PIDE.session.phase)
    handle_update()
  }

  override def exit()
  {
    PIDE.session.phase_changed -= main_actor
    PIDE.session.global_options -= main_actor
    PIDE.session.commands_changed -= main_actor
  }
}
