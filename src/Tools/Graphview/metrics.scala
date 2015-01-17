/*  Title:      Tools/Graphview/metrics.scala
    Author:     Makarius

Physical metrics for layout and painting.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Font, RenderingHints}
import java.awt.font.FontRenderContext
import java.awt.geom.Rectangle2D


object Metrics
{
  val rendering_hints: RenderingHints =
    new RenderingHints(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON)

  val font_render_context: FontRenderContext =
    new FontRenderContext(null, true, false)

  def apply(font: Font): Metrics = new Metrics(font)

  val default: Metrics = apply(new Font("Helvetica", Font.PLAIN, 12))
}

class Metrics private(val font: Font)
{
  def string_bounds(s: String): Rectangle2D = font.getStringBounds(s, Metrics.font_render_context)
  private val mix = string_bounds("mix")
  val space_width = string_bounds(" ").getWidth
  def char_width: Double = mix.getWidth / 3
  def height: Double = mix.getHeight
  def ascent: Double = font.getLineMetrics("", Metrics.font_render_context).getAscent
  def pad_x: Double = char_width * 1.5
  def pad_y: Double = char_width

  def gap: Double = mix.getWidth.ceil

  def dummy_size2: Double = (pad_x / 2).ceil

  def node_width2(lines: List[String]): Double =
    (((0.0 /: lines)({ case (w, s) => w max string_bounds(s).getWidth }) + pad_x) / 2).ceil

  def node_height2(num_lines: Int): Double =
    ((height.ceil * (num_lines max 1) + pad_y) / 2).ceil

  def level_height2(num_lines: Int, num_edges: Int): Double =
    (node_height2(num_lines) + gap) max (node_height2(1) * (num_edges max 5))

  object Pretty_Metric extends Pretty.Metric
  {
    val unit = space_width max 1.0
    def apply(s: String): Double = if (s == "\n") 1.0 else string_bounds(s).getWidth / unit
  }
}

