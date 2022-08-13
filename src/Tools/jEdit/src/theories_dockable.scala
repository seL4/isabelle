/*  Title:      Tools/jEdit/src/theories_dockable.scala
    Author:     Makarius

Dockable window for theories managed by prover.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{Button, TextArea, Label, ListView, Alignment,
  ScrollPane, Component, CheckBox, BorderPanel}
import scala.swing.event.{ButtonClicked, MouseClicked, MouseMoved}

import java.awt.{BorderLayout, Graphics2D, Color, Point, Dimension}
import javax.swing.{JList, BorderFactory, UIManager}
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.{View, jEdit}


class Theories_Dockable(view: View, position: String) extends Dockable(view, position) {
  /* status */

  private val status = new ListView(List.empty[Document.Node.Name]) {
    background = {
      // enforce default value
      val c = UIManager.getDefaults.getColor("Panel.background")
      new Color(c.getRed, c.getGreen, c.getBlue, c.getAlpha)
    }
    listenTo(mouse.clicks)
    listenTo(mouse.moves)
    reactions += {
      case MouseClicked(_, point, _, clicks, _) =>
        val index = peer.locationToIndex(point)
        if (index >= 0) {
          if (in_checkbox(peer.indexToLocation(index), point)) {
            if (clicks == 1) Document_Model.node_required(listData(index), toggle = true)
          }
          else if (clicks == 2) PIDE.editor.goto_file(true, view, listData(index).node)
        }
      case MouseMoved(_, point, _) =>
        val index = peer.locationToIndex(point)
        val index_location = peer.indexToLocation(index)
        if (index >= 0 && in_checkbox(index_location, point)) {
          tooltip = "Mark as required for continuous checking"
        } else if (index >= 0 && in_label(index_location, point)) {
          val name = listData(index)
          val st = nodes_status.overall_node_status(name)
          tooltip =
            "theory " + quote(name.theory) +
              (if (st == Document_Status.Overall_Node_Status.ok) "" else " (" + st + ")")
        }
        else tooltip = null
    }
  }
  status.peer.setLayoutOrientation(JList.HORIZONTAL_WRAP)
  status.peer.setVisibleRowCount(0)
  status.selection.intervalMode = ListView.IntervalMode.Single

  set_content(new ScrollPane(status))


  /* controls */

  def phase_text(phase: Session.Phase): String = "Prover: " + phase.print

  private val session_phase = new Label(phase_text(PIDE.session.phase))
  session_phase.border = new SoftBevelBorder(BevelBorder.LOWERED)
  session_phase.tooltip = "Status of prover session"

  private def handle_phase(phase: Session.Phase): Unit = {
    GUI_Thread.require {}
    session_phase.text = " " + phase_text(phase) + " "
  }

  private val purge = new Button("Purge") {
    tooltip = "Restrict document model to theories required for open editor buffers"
    reactions += { case ButtonClicked(_) => PIDE.editor.purge() }
  }

  private val continuous_checking = new Isabelle.Continuous_Checking
  continuous_checking.focusable = false

  private val logic = JEdit_Sessions.logic_selector(PIDE.options, autosave = true)

  private val controls =
    Wrap_Panel(List(purge, continuous_checking, session_phase, logic))

  add(controls.peer, BorderLayout.NORTH)


  /* component state -- owned by GUI thread */

  private var nodes_status = Document_Status.Nodes_Status.empty
  private var nodes_required: Set[Document.Node.Name] = Document_Model.required_nodes()

  private class Geometry {
    private var location: Point = null
    private var size: Dimension = null

    def in(location0: Point, p: Point): Boolean = {
      location != null && size != null &&
        location0.x + location.x <= p.x && p.x < location0.x + size.width &&
        location0.y + location.y <= p.y && p.y < location0.y + size.height
    }

    def update(new_location: Point, new_size: Dimension): Unit = {
      if (new_location != null && new_size != null) {
        location = new_location
        size = new_size
      }
    }
  }

  private def in_checkbox(location0: Point, p: Point): Boolean =
    Node_Renderer_Component != null && Node_Renderer_Component.checkbox_geometry.in(location0, p)

  private def in_label(location0: Point, p: Point): Boolean =
    Node_Renderer_Component != null && Node_Renderer_Component.label_geometry.in(location0, p)


  private object Node_Renderer_Component extends BorderPanel {
    opaque = true
    border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

    var node_name = Document.Node.Name.empty

    val checkbox_geometry = new Geometry
    val checkbox = new CheckBox {
      opaque = false
      override def paintComponent(gfx: Graphics2D): Unit = {
        super.paintComponent(gfx)
        checkbox_geometry.update(location, size)
      }
    }

    val label_geometry = new Geometry
    val label = new Label {
      background = view.getTextArea.getPainter.getBackground
      foreground = view.getTextArea.getPainter.getForeground
      opaque = false
      xAlignment = Alignment.Leading

      override def paintComponent(gfx: Graphics2D): Unit = {
        def paint_segment(x: Int, w: Int, color: Color): Unit = {
          gfx.setColor(color)
          gfx.fillRect(x, 0, w, size.height)
        }

        paint_segment(0, size.width, background)
        nodes_status.get(node_name) match {
          case Some(node_status) =>
            val segments =
              List(
                (node_status.unprocessed, PIDE.options.color_value("unprocessed1_color")),
                (node_status.running, PIDE.options.color_value("running_color")),
                (node_status.warned, PIDE.options.color_value("warning_color")),
                (node_status.failed, PIDE.options.color_value("error_color"))
              ).filter(_._1 > 0)

            segments.foldLeft(size.width - 2) {
              case (last, (n, color)) =>
                val w = (n * ((size.width - 4) - segments.length) / node_status.total) max 4
                paint_segment(last - w, w, color)
                last - w - 1
              }

          case None =>
            paint_segment(0, size.width, PIDE.options.color_value("unprocessed1_color"))
        }
        super.paintComponent(gfx)

        label_geometry.update(location, size)
      }
    }

    def label_border(name: Document.Node.Name): Unit = {
      val st = nodes_status.overall_node_status(name)
      val color =
        st match {
          case Document_Status.Overall_Node_Status.ok =>
            PIDE.options.color_value("ok_color")
          case Document_Status.Overall_Node_Status.failed =>
            PIDE.options.color_value("failed_color")
          case _ => label.foreground
        }
      val thickness1 = if (st == Document_Status.Overall_Node_Status.pending) 1 else 3
      val thickness2 = 4 - thickness1

      label.border =
        BorderFactory.createCompoundBorder(
          BorderFactory.createLineBorder(color, thickness1),
          BorderFactory.createEmptyBorder(thickness2, thickness2, thickness2, thickness2))
    }

    layout(checkbox) = BorderPanel.Position.West
    layout(label) = BorderPanel.Position.Center
  }

  private class Node_Renderer extends ListView.Renderer[Document.Node.Name] {
    def componentFor(
      list: ListView[_ <: isabelle.Document.Node.Name],
      isSelected: Boolean,
      focused: Boolean,
      name: Document.Node.Name,
      index: Int
    ): Component = {
      val component = Node_Renderer_Component
      component.node_name = name
      component.checkbox.selected = nodes_required.contains(name)
      component.label_border(name)
      component.label.text = name.theory_base_name
      component
    }
  }
  status.renderer = new Node_Renderer

  private def handle_update(
    domain: Option[Set[Document.Node.Name]] = None,
    trim: Boolean = false
  ): Unit = {
    GUI_Thread.require {}

    val snapshot = PIDE.session.snapshot()

    val (nodes_status_changed, nodes_status1) =
      nodes_status.update(
        PIDE.resources, snapshot.state, snapshot.version, domain = domain, trim = trim)

    nodes_status = nodes_status1
    if (nodes_status_changed) {
      status.listData =
        (for {
          (name, node_status) <- nodes_status1.present.iterator
          if !node_status.is_suppressed && node_status.total > 0
        } yield name).toList
    }
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case phase: Session.Phase =>
        GUI_Thread.later { handle_phase(phase) }

      case _: Session.Global_Options =>
        GUI_Thread.later {
          continuous_checking.load()
          logic.load ()
          nodes_required = Document_Model.required_nodes()
          status.repaint()
        }

      case changed: Session.Commands_Changed =>
        GUI_Thread.later { handle_update(domain = Some(changed.nodes), trim = changed.assignment) }
    }

  override def init(): Unit = {
    PIDE.session.phase_changed += main
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main

    handle_phase(PIDE.session.phase)
    handle_update()
  }

  override def exit(): Unit = {
    PIDE.session.phase_changed -= main
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
  }
}
