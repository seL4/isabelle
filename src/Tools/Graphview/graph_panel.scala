/*  Title:      Tools/Graphview/graph_panel.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graphview Java2D drawing panel.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Dimension, Graphics2D, Point}
import java.awt.geom.{AffineTransform, Point2D}
import java.awt.image.BufferedImage
import javax.swing.{JScrollPane, JComponent, SwingUtilities}

import scala.swing.{Panel, ScrollPane}
import scala.swing.event.{Event, Key, MousePressed, MouseDragged, MouseClicked, MouseEvent}


class Graph_Panel(val visualizer: Visualizer) extends ScrollPane
{
  panel =>

  tooltip = ""

  override lazy val peer: JScrollPane = new JScrollPane with SuperMixin {
    override def getToolTipText(event: java.awt.event.MouseEvent): String =
      find_node(Transform.pane_to_graph_coordinates(event.getPoint)) match {
        case Some(node) =>
          visualizer.model.complete_graph.get_node(node) match {
            case Nil => null
            case content => visualizer.make_tooltip(panel.peer, event.getX, event.getY, content)
          }
        case None => null
      }
  }

  focusable = true
  requestFocus()

  horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  verticalScrollBarPolicy = ScrollPane.BarPolicy.Always

  peer.getVerticalScrollBar.setUnitIncrement(10)

  def find_node(at: Point2D): Option[Graph_Display.Node] =
  {
    val m = visualizer.metrics()
    visualizer.model.visible_nodes_iterator
      .find(node => visualizer.Drawer.shape(m, node).contains(at))
  }

  def refresh()
  {
    if (paint_panel != null) {
      paint_panel.set_preferred_size()
      paint_panel.repaint()
    }
  }

  def fit_to_window() = {
    Transform.fit_to_window()
    refresh()
  }

  val zoom = new GUI.Zoom_Box { def changed = rescale(0.01 * factor) }

  def rescale(s: Double)
  {
    Transform.scale = s
    if (zoom != null) zoom.set_item((Transform.scale_discrete * 100).floor.toInt)
    refresh()
  }

  def apply_layout()
  {
    visualizer.Coordinates.update_layout()
    repaint()
  }

  private class Paint_Panel extends Panel
  {
    def set_preferred_size()
    {
      val box = visualizer.Coordinates.bounding_box()
      val s = Transform.scale_discrete

      preferredSize =
        new Dimension((box.width * s).ceil.toInt, (box.height * s).ceil.toInt)

      revalidate()
    }

    override def paint(gfx: Graphics2D)
    {
      super.paintComponent(gfx)
      gfx.setColor(visualizer.background_color)
      gfx.fillRect(0, 0, peer.getWidth, peer.getHeight)
      gfx.transform(Transform())

      visualizer.Drawer.paint_all_visible(gfx, true)
    }
  }
  private val paint_panel = new Paint_Panel
  contents = paint_panel

  listenTo(mouse.moves)
  listenTo(mouse.clicks)
  reactions += Mouse_Interaction.react
  reactions +=
  {
    case MousePressed(_, _, _, _, _) => repaint()
    case MouseDragged(_, _, _) => repaint()
    case MouseClicked(_, _, _, _, _) => repaint()
  }

  visualizer.model.Colors.events += { case _ => repaint() }
  visualizer.model.Mutators.events += { case _ => repaint() }

  apply_layout()
  rescale(1.0)

  private object Transform
  {
    private var _scale: Double = 1.0
    def scale: Double = _scale
    def scale_=(s: Double)
    {
      _scale = (s min 10.0) max 0.1
    }

    def scale_discrete: Double =
      (scale * visualizer.font_size).floor / visualizer.font_size

    def apply() =
    {
      val box = visualizer.Coordinates.bounding_box()
      val at = AffineTransform.getScaleInstance(scale_discrete, scale_discrete)
      at.translate(- box.x, - box.y)
      at
    }

    def fit_to_window()
    {
      if (visualizer.model.visible_nodes_iterator.isEmpty)
        rescale(1.0)
      else {
        val box = visualizer.Coordinates.bounding_box()
        rescale((size.width / box.width) min (size.height / box.height))
      }
    }

    def pane_to_graph_coordinates(at: Point2D): Point2D =
    {
      val s = Transform.scale_discrete
      val p = Transform().inverseTransform(peer.getViewport.getViewPosition, null)

      p.setLocation(p.getX + at.getX / s, p.getY + at.getY / s)
      p
    }
  }

  object Mouse_Interaction
  {
    type Dummy = (Graph_Display.Edge, Int)

    private var draginfo: (Point, List[Graph_Display.Node], List[Dummy]) = null

    val react: PartialFunction[Event, Unit] =
    {
      case MousePressed(_, p, _, _, _) => pressed(p)
      case MouseDragged(_, to, _) =>
        drag(draginfo, to)
        val (_, p, d) = draginfo
        draginfo = (to, p, d)
      case e @ MouseClicked(_, p, m, n, _) => click(p, m, n, e)
    }

    def dummy(at: Point2D): Option[Dummy] =
    {
      val m = visualizer.metrics()
      visualizer.model.visible_edges_iterator.map(
        edge => visualizer.Coordinates(edge).zipWithIndex.map((edge, _))).flatten.find(
          {
            case (_, ((x, y), _)) =>
              visualizer.Drawer.shape(m, Graph_Display.Node.dummy).
                contains(at.getX() - x, at.getY() - y)
          }) match {
            case None => None
            case Some((edge, (_, index))) => Some((edge, index))
          }
    }

    def pressed(at: Point)
    {
      val c = Transform.pane_to_graph_coordinates(at)
      val l =
        find_node(c) match {
          case Some(node) =>
            if (visualizer.Selection.contains(node)) visualizer.Selection.get()
            else List(node)
          case None => Nil
        }
      val d =
        l match {
          case Nil =>
            dummy(c) match {
              case Some(d) => List(d)
              case None => Nil
            }
          case _ => Nil
        }
      draginfo = (at, l, d)
    }

    def click(at: Point, m: Key.Modifiers, clicks: Int, e: MouseEvent)
    {
      val c = Transform.pane_to_graph_coordinates(at)

      def left_click()
      {
        (find_node(c), m) match {
          case (Some(node), Key.Modifier.Control) => visualizer.Selection.add(node)
          case (None, Key.Modifier.Control) =>

          case (Some(node), Key.Modifier.Shift) => visualizer.Selection.add(node)
          case (None, Key.Modifier.Shift) =>

          case (Some(node), _) =>
            visualizer.Selection.clear()
            visualizer.Selection.add(node)
          case (None, _) =>
            visualizer.Selection.clear()
        }
      }

      def right_click()
      {
        val menu = Popups(panel, find_node(c), visualizer.Selection.get())
        menu.show(panel.peer, at.x, at.y)
      }

      if (clicks < 2) {
        if (SwingUtilities.isRightMouseButton(e.peer)) right_click()
        else left_click()
      }
    }

    def drag(draginfo: (Point, List[Graph_Display.Node], List[Dummy]), to: Point)
    {
      val (from, p, d) = draginfo

      val s = Transform.scale_discrete
      val (dx, dy) = (to.x - from.x, to.y - from.y)
      (p, d) match {
        case (Nil, Nil) =>
          val r = panel.peer.getViewport.getViewRect
          r.translate(-dx, -dy)

          paint_panel.peer.scrollRectToVisible(r)

        case (Nil, ds) =>
          ds.foreach(d => visualizer.Coordinates.translate(d, (dx / s, dy / s)))

        case (ls, _) =>
          ls.foreach(l => visualizer.Coordinates.translate(l, (dx / s, dy / s)))
      }
    }
  }
}
