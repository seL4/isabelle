/*  Title:      Tools/jEdit/src/theories_status.scala
    Author:     Makarius

GUI panel for status of theories.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{ListView, Alignment, Label, CheckBox, BorderPanel, Component}
import scala.swing.event.{MousePressed, MouseMoved}

import java.awt.{Graphics2D, Color, Point, Dimension}
import javax.swing.{JList, BorderFactory, UIManager}

import org.gjt.sp.jedit.View


class Theories_Status(view: View, document: Boolean = false) {
  /* component state -- owned by GUI thread */

  private var nodes_status = Document_Status.Nodes_Status.empty
  private var nodes_required = Set.empty[Document.Node.Name]
  private var document_required = Set.empty[Document.Node.Name]

  private def is_loaded_theory(name: Document.Node.Name): Boolean =
    PIDE.resources.loaded_theory(name)

  private def overall_status(name: Document.Node.Name): Document_Status.Overall_Status =
    if (is_loaded_theory(name)) Document_Status.Overall_Status.ok
    else nodes_status.overall_status(name)

  private def init_state(): Unit = GUI_Thread.require {
    if (document) {
      nodes_required = PIDE.editor.document_required().toSet
    }
    else {
      nodes_required = Document_Model.nodes_required()
      document_required = PIDE.editor.document_required().toSet
    }
  }


  /* node renderer */

  private class Geometry {
    private var location: Point = null
    private var size: Dimension = null

    def in(location0: Point, p: Point): Boolean =
      location != null && size != null && location0 != null && p != null && {
        val x = location0.x + location.x
        val y = location0.y + location.y
        x <= p.x && p.x < x + size.width &&
        y <= p.y && p.y < y + size.height
      }

    def update(new_location: Point, new_size: Dimension): Unit = {
      if (new_location != null && new_size != null) {
        location = new_location
        size = new_size
      }
    }
  }

  private class Node_Renderer extends ListView.Renderer[Document.Node.Name] {
    private val document_marker = Symbol.decode(" \\<^file>")
    private val no_document_marker = "   "

    private object component extends BorderPanel {
      opaque = true
      border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

      var node_name: Document.Node.Name = Document.Node.Name.empty

      val required_geometry = new Geometry
      val required: CheckBox = new CheckBox {
        opaque = false
        override def paintComponent(gfx: Graphics2D): Unit = {
          super.paintComponent(gfx)
          required_geometry.update(location, size)
        }
      }

      val label_geometry = new Geometry
      val label: Label = new Label {
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
                  (node_status.unprocessed, PIDE.plugin.options.color_value("unprocessed1_color")),
                  (node_status.running, PIDE.plugin.options.color_value("running_color")),
                  (node_status.warned, PIDE.plugin.options.color_value("warning_color")),
                  (node_status.failed, PIDE.plugin.options.color_value("error_color"))
                ).filter(_._1 > 0)

              segments.foldLeft(size.width - 2) {
                case (last, (n, color)) =>
                  val w = (n * ((size.width - 4) - segments.length) / node_status.total) max 4
                  paint_segment(last - w, w, color)
                  last - w - 1
                }

            case None =>
              if (!is_loaded_theory(node_name)) {
                paint_segment(0, size.width, PIDE.plugin.options.color_value("unprocessed1_color"))
              }
          }
          super.paintComponent(gfx)

          label_geometry.update(location, size)
        }
      }

      def label_border(name: Document.Node.Name): Unit = {
        val st = overall_status(name)
        val color =
          st match {
            case Document_Status.Overall_Status.ok =>
              PIDE.plugin.options.color_value("ok_color")
            case Document_Status.Overall_Status.failed =>
              PIDE.plugin.options.color_value("failed_color")
            case _ => label.foreground
          }
        val thickness1 = if (st == Document_Status.Overall_Status.pending) 1 else 3
        val thickness2 = 4 - thickness1

        label.border =
          BorderFactory.createCompoundBorder(
            BorderFactory.createLineBorder(color, thickness1),
            BorderFactory.createEmptyBorder(thickness2, thickness2, thickness2, thickness2))
      }

      layout(required) = BorderPanel.Position.West
      layout(label) = BorderPanel.Position.Center
    }

    def in_required(location0: Point, p: Point): Boolean =
      component.required_geometry.in(location0, p)

    def in_label(location0: Point, p: Point): Boolean =
      component.label_geometry.in(location0, p)

    def componentFor(
      list: ListView[_ <: isabelle.Document.Node.Name],
      isSelected: Boolean,
      focused: Boolean,
      name: Document.Node.Name,
      index: Int
    ): Component = {
      component.node_name = name
      component.required.selected = nodes_required.contains(name)
      component.label_border(name)
      component.label.text =
        name.theory_base_name +
        (if (document_required.contains(name)) document_marker else no_document_marker)
      component
    }
  }


  /* GUI component */

  val gui: ListView[Document.Node.Name] = new ListView[Document.Node.Name](Nil) {
    private val node_renderer = new Node_Renderer
    renderer = node_renderer

    background = {
      // enforce default value
      val c = UIManager.getDefaults.getColor("Panel.background")
      new Color(c.getRed, c.getGreen, c.getBlue, c.getAlpha)
    }
    listenTo(mouse.clicks)
    listenTo(mouse.moves)
    reactions += {
      case mouse: MousePressed =>
        val index = peer.locationToIndex(mouse.point)
        if (index >= 0) {
          val index_location = peer.indexToLocation(index)
          if (node_renderer.in_required(index_location, mouse.point)) {
            if (mouse.clicks == 1) {
              val name = listData(index)
              if (document) PIDE.editor.document_select(Set(name.theory), toggle = true)
              else Document_Model.node_required(name, toggle = true)
            }
          }
          else if (mouse.clicks == 2) PIDE.editor.goto_file(view, listData(index).node, focus = true)
        }
      case mouse: MouseMoved =>
        val index = peer.locationToIndex(mouse.point)
        val index_location = peer.indexToLocation(index)
        if (index >= 0 && node_renderer.in_required(index_location, mouse.point)) {
          tooltip =
            if (document) "Mark for inclusion in document"
            else "Mark as required for continuous checking"
        }
        else if (index >= 0 && node_renderer.in_label(index_location, mouse.point)) {
          val name = listData(index)
          val st = overall_status(name)
          tooltip =
            "theory " + quote(name.theory) +
              (if (st == Document_Status.Overall_Status.ok) "" else " (" + st + ")")
        }
        else tooltip = null
    }

    peer.setLayoutOrientation(JList.HORIZONTAL_WRAP)
    peer.setVisibleRowCount(0)
    selection.intervalMode = ListView.IntervalMode.Single
  }


  /* update */

  def update(
    domain: Option[Set[Document.Node.Name]] = None,
    trim: Boolean = false,
    force: Boolean = false
  ): Unit = {
    GUI_Thread.require {}

    val snapshot = PIDE.session.snapshot()

    val now = Date.now()

    val nodes_status1 =
      nodes_status.update_nodes(now,
        PIDE.resources, snapshot.state, snapshot.version, domain = domain, trim = trim)

    if (force || nodes_status1 != nodes_status) {
      gui.listData =
        if (document) PIDE.editor.document_theories()
        else {
          (for {
            name <- snapshot.version.nodes.topological_order.iterator
            node_status = nodes_status1(name)
            if !node_status.is_empty && !node_status.suppressed && node_status.total > 0
          } yield name).toList
        }
    }

    nodes_status = nodes_status1
  }


  /* refresh */

  def refresh(): Unit = GUI_Thread.require {
    init_state()
    gui.repaint()
  }

  init_state()
}
