/*  Title:      Pure/GUI/gui.scala
    Author:     Makarius

Precise metric for smooth font rendering, notably for pretty-printing.
*/

package isabelle

import java.awt.{Font, RenderingHints}
import java.awt.font.FontRenderContext
import java.awt.geom.Rectangle2D


object Font_Metric {
  val default_hints: RenderingHints =
    new RenderingHints(
      java.util.Map.of(
        RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON,
        RenderingHints.KEY_FRACTIONALMETRICS, RenderingHints.VALUE_FRACTIONALMETRICS_ON))

  val default_font: Font = new Font("Helvetica", Font.PLAIN, 12)
  val default_context: FontRenderContext = new FontRenderContext(null, true, true)
  val default: Font_Metric = new Font_Metric()
}

class Font_Metric(
  val font: Font = Font_Metric.default_font,
  val context: FontRenderContext = Font_Metric.default_context) extends Pretty.Metric
{
  override def toString: String = font.toString
  override def hashCode: Int = font.hashCode

  override def equals(that: Any): Boolean =
    that match {
      case other: Font_Metric => font == other.font && context == other.context
      case _ => false
    }

  def string_bounds(str: String): Rectangle2D = font.getStringBounds(str, context)
  def string_width(str: String): Double = string_bounds(str).getWidth

  protected def sample: String = "mix"
  val height: Double = string_bounds(sample).getHeight
  val average_width: Double = string_width(sample) / sample.length

  val space_width: Double = string_width(Symbol.space)
  override def unit: Double = space_width max 1.0
  override def apply(s: String): Double = if (s == "\n") 1.0 else string_width(s) / unit
  def average: Double = average_width / unit
}
