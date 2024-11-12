/*  Title:      Pure/GUI/rich_text.scala
    Author:     Makarius

Support for rendering of rich text, based on individual messages (XML.Elem).
*/

package isabelle


import javax.swing.JComponent

import scala.collection.mutable


object Rich_Text {
  /* margin */

  def make_margin(metric: Font_Metric, margin: Int, limit: Int = -1): Int = {
    val m = (margin * metric.average).toInt
    (if (limit < 0) m else m min limit) max 20
  }

  def component_margin(metric: Font_Metric, component: JComponent): Int =
    make_margin(metric, (component.getWidth.toDouble / metric.average_width).toInt)


  /* format */

  sealed case class Formatted(id: Document_ID.Generic, body: XML.Body) {
    lazy val text: String = XML.content(body)
    lazy val markups: Command.Markups = Command.Markups.init(Markup_Tree.from_XML(body))
    def command(results: Command.Results): Command =
      Command.unparsed(text, id = id, results = results, markups = markups)
  }

  def format(msgs: List[XML.Elem], margin: Double, metric: Font_Metric): List[Formatted] = {
    val result = new mutable.ListBuffer[Formatted]
    for (msg <- msgs) {
      if (result.nonEmpty) result += Formatted(Document_ID.make(), Pretty.Separator)

      val id = Protocol_Message.get_serial(msg)
      val body = Pretty.formatted(List(msg), margin = margin, metric = metric)
      result += Formatted(id, body)

      Exn.Interrupt.expose()
    }
    result.toList
  }

  def formatted_lines(formatted: List[Formatted]): Int =
    if (formatted.isEmpty) 0
    else {
      1 + formatted.iterator.map(form =>
        XML.traverse_text(form.body, 0, (n, s) => n + Library.count_newlines(s))).sum
    }

  def formatted_margin(metric: Font_Metric, formatted: List[Formatted]): Double =
    split_lines(formatted.map(_.text).mkString)
      .foldLeft(0.0) { case (m, line) => m max metric(line) }
}
