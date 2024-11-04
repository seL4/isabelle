/*  Title:      Tools/Graphview/metrics.scala
    Author:     Makarius

Physical metrics for layout and painting.
*/

package isabelle.graphview


import isabelle._

import java.awt.Font


object Metrics {
  def apply(font: Font): Metrics = new Metrics(font)
  val default: Metrics = apply(Font_Metric.default.font)
}

class Metrics private(font: Font) extends Font_Metric(font = font) {
  val ascent: Double = font.getLineMetrics("", context).getAscent

  def gap: Double = (average_width * 3).ceil

  def dummy_size2: Double = (average_width / 2).ceil

  def node_width2(lines: List[String]): Double =
    ((lines.foldLeft(0.0)({ case (w, s) => w max string_width(s) }) + 2 * average_width) / 2).ceil

  def node_height2(num_lines: Int): Double =
    ((height.ceil * (num_lines max 1) + average_width) / 2).ceil

  def level_height2(num_lines: Int, num_edges: Int): Double =
    (node_height2(num_lines) + gap) max (node_height2(1) * (num_edges max 5))
}
