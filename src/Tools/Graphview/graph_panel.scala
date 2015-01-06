/*  Title:      Tools/Graphview/graph_panel.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graphview Java2D drawing panel.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Dimension, Graphics2D, Point}
import java.awt.geom.{AffineTransform, Point2D}
import javax.swing.{JScrollPane, JComponent, SwingUtilities}

import scala.swing.{Panel, ScrollPane}
import scala.swing.event.{Event, Key, MousePressed, MouseDragged, MouseClicked, MouseEvent}


class Graph_Panel(val visualizer: Visualizer) extends ScrollPane
{
  panel =>

  tooltip = ""

  override lazy val peer: JScrollPane = new JScrollPane with SuperMixin {
    override def getToolTipText(event: java.awt.event.MouseEvent): String =
      find_visible_node(Transform.pane_to_graph_coordinates(event.getPoint)) match {
        case Some(node) =>
          visualizer.model.full_graph.get_node(node) match {
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

  def find_visible_node(at: Point2D): Option[Graph_Display.Node] =
    visualizer.visible_graph.keys_iterator.find(node =>
      Shapes.Node.shape(visualizer, node).contains(at))

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
    visualizer.update_layout()
    repaint()
  }

  private class Paint_Panel extends Panel
  {
    def set_preferred_size()
    {
      val box = visualizer.bounding_box()
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

      visualizer.paint_all_visible(gfx)
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
    {
      val font_height = GUI.line_metrics(visualizer.metrics.font).getHeight.toInt
      (scale * font_height).floor / font_height
    }

    def apply() =
    {
      val box = visualizer.bounding_box()
      val at = AffineTransform.getScaleInstance(scale_discrete, scale_discrete)
      at.translate(- box.x, - box.y)
      at
    }

    def fit_to_window()
    {
      if (visualizer.visible_graph.is_empty)
        rescale(1.0)
      else {
        val box = visualizer.bounding_box()
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
    private var draginfo: (Point, List[Graph_Display.Node], List[Layout.Dummy]) = null

    val react: PartialFunction[Event, Unit] =
    {
      case MousePressed(_, p, _, _, _) => pressed(p)
      case MouseDragged(_, to, _) =>
        drag(draginfo, to)
        val (_, p, d) = draginfo
        draginfo = (to, p, d)
      case e @ MouseClicked(_, p, m, n, _) => click(p, m, n, e)
    }

    def dummy(at: Point2D): Option[Layout.Dummy] =
      visualizer.layout.find_dummy(d => Shapes.Dummy.shape(visualizer, d).contains(at))

    def pressed(at: Point)
    {
      val c = Transform.pane_to_graph_coordinates(at)
      val l =
        find_visible_node(c) match {
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
        (find_visible_node(c), m) match {
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
        val menu = Popups(panel, find_visible_node(c), visualizer.Selection.get())
        menu.show(panel.peer, at.x, at.y)
      }

      if (clicks < 2) {
        if (SwingUtilities.isRightMouseButton(e.peer)) right_click()
        else left_click()
      }
    }

    def drag(info: (Point, List[Graph_Display.Node], List[Layout.Dummy]), to: Point)
    {
      val (from, p, d) = info

      val s = Transform.scale_discrete
      val (dx, dy) = (to.x - from.x, to.y - from.y)
      (p, d) match {
        case (Nil, Nil) =>
          val r = panel.peer.getViewport.getViewRect
          r.translate(- dx, - dy)
          paint_panel.peer.scrollRectToVisible(r)

        case (Nil, ds) =>
          ds.foreach(d => visualizer.translate_vertex(d, dx / s, dy / s))

        case (ls, _) =>
          ls.foreach(l => visualizer.translate_vertex(Layout.Node(l), dx / s, dy / s))
      }
    }
  }
}
