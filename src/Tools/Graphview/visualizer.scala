/*  Title:      Tools/Graphview/visualizer.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graph visualization parameters and interface state.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Font, FontMetrics, Color, Shape, RenderingHints, Graphics2D}
import java.awt.font.FontRenderContext
import java.awt.image.BufferedImage
import java.awt.geom.Rectangle2D
import javax.swing.JComponent


object Visualizer
{
  object Metrics
  {
    def apply(font: Font, font_render_context: FontRenderContext) =
      new Metrics(font, font_render_context)

    def apply(gfx: Graphics2D): Metrics =
      new Metrics(gfx.getFont, gfx.getFontRenderContext)
  }

  class Metrics private(font: Font, font_render_context: FontRenderContext)
  {
    def string_bounds(s: String) = font.getStringBounds(s, font_render_context)
    private val mix = string_bounds("mix")
    val space_width = string_bounds(" ").getWidth
    def char_width: Double = mix.getWidth / 3
    def height: Double = mix.getHeight
    def ascent: Double = font.getLineMetrics("", font_render_context).getAscent
    def gap: Double = mix.getWidth
    def pad: Double = char_width
  }
}

class Visualizer(val model: Model)
{
  visualizer =>


  /* tooltips */

  def make_tooltip(parent: JComponent, x: Int, y: Int, body: XML.Body): String = null


  /* main colors */

  def foreground_color: Color = Color.BLACK
  def background_color: Color = Color.WHITE
  def selection_color: Color = Color.GREEN
  def error_color: Color = Color.RED
  def dummy_color: Color = Color.GRAY


  /* font rendering information */

  def font_size: Int = 12
  def font(): Font = new Font("Helvetica", Font.PLAIN, font_size)

  val rendering_hints =
    new RenderingHints(
      RenderingHints.KEY_ANTIALIASING,
      RenderingHints.VALUE_ANTIALIAS_ON)

  val font_render_context = new FontRenderContext(null, true, false)

  def metrics(): Visualizer.Metrics =
    Visualizer.Metrics(font(), font_render_context)


  /* rendering parameters */

  var arrow_heads = false

  object Colors
  {
    private val filter_colors = List(
      new Color(0xD9, 0xF2, 0xE2), // blue
      new Color(0xFF, 0xE7, 0xD8), // orange
      new Color(0xFF, 0xFF, 0xE5), // yellow
      new Color(0xDE, 0xCE, 0xFF), // lilac
      new Color(0xCC, 0xEB, 0xFF), // turquoise
      new Color(0xFF, 0xE5, 0xE5), // red
      new Color(0xE5, 0xE5, 0xD9)  // green
    )

    private var curr : Int = -1
    def next(): Color =
    {
      curr = (curr + 1) % filter_colors.length
      filter_colors(curr)
    }
  }


  object Coordinates
  {
    // owned by GUI thread
    private var layout = Layout.empty

    def get_node(node: Graph_Display.Node): Layout.Point = layout.get_node(node)
    def get_dummies(edge: Graph_Display.Edge): List[Layout.Point] = layout.get_dummies(edge)

    def translate_node(node: Graph_Display.Node, dx: Double, dy: Double)
    {
      layout = layout.map_node(node, p => Layout.Point(p.x + dx, p.y + dy))
    }

    def translate_dummy(d: (Graph_Display.Edge, Int), dx: Double, dy: Double)
    {
      val (edge, index) = d
      layout = layout.map_dummies(edge,
        ds => {
          val p = ds(index)
          (ds.zipWithIndex :\ List.empty[Layout.Point]) {
            case ((t, i), n) => if (index == i) Layout.Point(p.x + dx, p.y + dy) :: n else t :: n
          }
        })
    }

    def update_layout()
    {
      // FIXME avoid expensive operation on GUI thread
      layout = Layout.make(metrics(), model.make_visible_graph())
    }

    def bounding_box(): Rectangle2D.Double =
    {
      val m = metrics()
      var x0 = 0.0
      var y0 = 0.0
      var x1 = 0.0
      var y1 = 0.0
      for (node <- model.make_visible_graph().keys_iterator) {
        val shape = Shapes.Node.shape(m, visualizer, node)
        x0 = x0 min shape.getMinX
        y0 = y0 min shape.getMinY
        x1 = x1 max shape.getMaxX
        y1 = y1 max shape.getMaxY
      }
      x0 = (x0 - m.gap).floor
      y0 = (y0 - m.gap).floor
      x1 = (x1 + m.gap).ceil
      y1 = (y1 + m.gap).ceil
      new Rectangle2D.Double(x0, y0, x1 - x0, y1 - y0)
    }
  }

  object Drawer
  {
    def apply(gfx: Graphics2D, node: Graph_Display.Node): Unit =
      if (!node.is_dummy) Shapes.Node.paint(gfx, visualizer, node)

    def apply(gfx: Graphics2D, edge: Graph_Display.Edge, head: Boolean, dummies: Boolean): Unit =
      Shapes.Cardinal_Spline_Edge.paint(gfx, visualizer, edge, head, dummies)

    def paint_all_visible(gfx: Graphics2D, dummies: Boolean)
    {
      gfx.setFont(font())
      gfx.setRenderingHints(rendering_hints)
      val visible_graph = model.make_visible_graph()
      visible_graph.edges_iterator.foreach(apply(gfx, _, arrow_heads, dummies))
      visible_graph.keys_iterator.foreach(apply(gfx, _))
    }

    def shape(m: Visualizer.Metrics, node: Graph_Display.Node): Shape =
      if (node.is_dummy) Shapes.Dummy.shape(m, visualizer)
      else Shapes.Node.shape(m, visualizer, node)
  }

  object Selection
  {
    // owned by GUI thread
    private var state: List[Graph_Display.Node] = Nil

    def get(): List[Graph_Display.Node] = GUI_Thread.require { state }
    def contains(node: Graph_Display.Node): Boolean = get().contains(node)

    def add(node: Graph_Display.Node): Unit = GUI_Thread.require { state = node :: state }
    def clear(): Unit = GUI_Thread.require { state = Nil }
  }

  sealed case class Node_Color(border: Color, background: Color, foreground: Color)

  def node_color(node: Graph_Display.Node): Node_Color =
    if (Selection.contains(node))
      Node_Color(foreground_color, selection_color, foreground_color)
    else
      Node_Color(foreground_color, model.colors.getOrElse(node, background_color), foreground_color)

  def edge_color(edge: Graph_Display.Edge): Color = foreground_color
}