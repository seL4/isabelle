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
  def foreground1_color: Color = Color.GRAY
  def background_color: Color = Color.WHITE
  def selection_color: Color = Color.GREEN
  def error_color: Color = Color.RED


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
    private var layout = Layout.empty

    def apply(k: String): (Double, Double) =
      layout.nodes.getOrElse(k, (0.0, 0.0))

    def apply(e: (String, String)): List[(Double, Double)] =
      layout.dummies.get(e) match {
        case Some(ds) => ds
        case None => Nil
      }

    def reposition(k: String, to: (Double, Double))
    {
      layout = layout.copy(nodes = layout.nodes + (k -> to))
    }

    def reposition(d: ((String, String), Int), to: (Double, Double))
    {
      val (e, index) = d
      layout.dummies.get(e) match {
        case None =>
        case Some(ds) =>
          layout = layout.copy(dummies =
            layout.dummies + (e ->
              (ds.zipWithIndex :\ List.empty[(Double, Double)]) {
                case ((t, i), n) => if (index == i) to :: n else t :: n
              }))
      }
    }

    def translate(k: String, by: (Double, Double))
    {
      val ((x, y), (dx, dy)) = (Coordinates(k), by)
      reposition(k, (x + dx, y + dy))
    }

    def translate(d: ((String, String), Int), by: (Double, Double))
    {
      val ((e, i),(dx, dy)) = (d, by)
      val (x, y) = apply(e)(i)
      reposition(d, (x + dx, y + dy))
    }

    def update_layout()
    {
      layout =
        if (model.current_graph.is_empty) Layout.empty
        else {
          val m = metrics()

          val max_width =
            model.current_graph.iterator.map({ case (_, (info, _)) =>
              m.string_bounds(info.name).getWidth }).max
          val box_distance = (max_width + m.pad + m.gap).ceil
          def box_height(n: Int): Double = (m.char_width * 1.5 * (5 max n)).ceil

          Layout.make(model.current_graph, box_distance, box_height _)
        }
    }

    def bounding_box(): Rectangle2D.Double =
    {
      val m = metrics()
      var x0 = 0.0
      var y0 = 0.0
      var x1 = 0.0
      var y1 = 0.0
      for (node_name <- model.visible_nodes_iterator) {
        val shape = Shapes.Growing_Node.shape(m, visualizer, Some(node_name))
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
    def apply(g: Graphics2D, n: Option[String])
    {
      n match {
        case None =>
        case Some(_) => Shapes.Growing_Node.paint(g, visualizer, n)
      }
    }

    def apply(g: Graphics2D, e: (String, String), head: Boolean, dummies: Boolean)
    {
      Shapes.Cardinal_Spline_Edge.paint(g, visualizer, e, head, dummies)
    }

    def paint_all_visible(g: Graphics2D, dummies: Boolean)
    {
      g.setFont(font)

      g.setRenderingHints(rendering_hints)

      model.visible_edges_iterator.foreach(e => {
          apply(g, e, arrow_heads, dummies)
        })

      model.visible_nodes_iterator.foreach(l => {
          apply(g, Some(l))
        })
    }

    def shape(m: Visualizer.Metrics, n: Option[String]): Shape =
      if (n.isEmpty) Shapes.Dummy.shape(m, visualizer, n)
      else Shapes.Growing_Node.shape(m, visualizer, n)
  }

  object Selection
  {
    private var selected: List[String] = Nil

    def apply() = selected
    def apply(s: String) = selected.contains(s)

    def add(s: String) { selected = s :: selected }
    def set(ss: List[String]) { selected = ss }
    def clear() { selected = Nil }
  }

  sealed case class Node_Color(border: Color, background: Color, foreground: Color)

  def node_color(l: Option[String]): Node_Color =
    l match {
      case None =>
        Node_Color(foreground1_color, background_color, foreground_color)
      case Some(c) if Selection(c) =>
        Node_Color(foreground_color, selection_color, foreground_color)
      case Some(c) =>
        Node_Color(foreground_color, model.colors.getOrElse(c, background_color), foreground_color)
    }

  def edge_color(e: (String, String)): Color = foreground_color

  object Caption
  {
    def apply(key: String) = model.complete_graph.get_node(key).name
  }
}