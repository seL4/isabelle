/*  Title:      Tools/Graphview/metrics.scala
    Author:     Makarius

Physical metrics for layout and painting.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Font, RenderingHints}
import java.awt.font.FontRenderContext


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
  def string_bounds(s: String) = font.getStringBounds(s, Metrics.font_render_context)
  private val mix = string_bounds("mix")
  val space_width = string_bounds(" ").getWidth
  def char_width: Double = mix.getWidth / 3
  def height: Double = mix.getHeight
  def ascent: Double = font.getLineMetrics("", Metrics.font_render_context).getAscent
  def gap: Double = mix.getWidth
  def pad_x: Double = char_width * 1.5
  def pad_y: Double = char_width

  def box_width2(node: Graph_Display.Node): Double =
    ((string_bounds(node.toString).getWidth + pad_x) / 2).ceil
  def box_gap: Double = gap.ceil
  def box_height(n: Int): Double = (char_width * 1.5 * (5 max n)).ceil
}

