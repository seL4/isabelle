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
import javax.swing.JComponent


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

  def font_size: Int = 14
  def font(): Font = new Font("IsabelleText", Font.BOLD, font_size)

  val rendering_hints =
    new RenderingHints(
      RenderingHints.KEY_ANTIALIASING,
      RenderingHints.VALUE_ANTIALIAS_ON)

  val font_render_context = new FontRenderContext(null, true, false)

  def graphics_context(): Graphics2D =
  {
    val gfx = new BufferedImage(1, 1, BufferedImage.TYPE_INT_ARGB).createGraphics
    gfx.setFont(font())
    gfx.setRenderingHints(rendering_hints)
    gfx
  }

  class Metrics private[Visualizer](f: Font, frc: FontRenderContext)
  {
    def string_bounds(s: String) = f.getStringBounds(s, frc)
    private val specimen = string_bounds("mix")

    def char_width: Double = specimen.getWidth / 3
    def height: Double = specimen.getHeight
    def ascent: Double = font.getLineMetrics("", frc).getAscent
    def gap: Double = specimen.getWidth
    def pad: Double = char_width
  }
  def metrics(): Metrics = new Metrics(font(), font_render_context)
  def metrics(gfx: Graphics2D): Metrics = new Metrics(gfx.getFont, gfx.getFontRenderContext)


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
      layout.nodes.get(k) match {
        case Some(c) => c
        case None => (0, 0)
      }

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
          val box_distance = max_width + m.pad + m.gap
          def box_height(n: Int): Double = m.char_width * 1.5 * (5 max n)

          Layout.make(model.current_graph, box_distance, box_height _)
        }
    }

    def bounds(): (Double, Double, Double, Double) =
      model.visible_nodes_iterator.toList match {
        case Nil => (0, 0, 0, 0)
        case nodes =>
          val X: (String => Double) = (n => apply(n)._1)
          val Y: (String => Double) = (n => apply(n)._2)

          (X(nodes.minBy(X)), Y(nodes.minBy(Y)),
           X(nodes.maxBy(X)), Y(nodes.maxBy(Y)))
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

    def shape(g: Graphics2D, n: Option[String]): Shape =
      n match {
        case None => Shapes.Dummy.shape(g, visualizer, None)
        case Some(_) => Shapes.Growing_Node.shape(g, visualizer, n)
      }
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