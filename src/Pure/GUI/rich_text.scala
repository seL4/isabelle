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

  sealed case class Formatted(id: Document_ID.Generic, body: XML.Body, results: Command.Results) {
    lazy val text: String = XML.content(body)
    lazy val command: Command =
      Command.unparsed(text, id = id, results = results,
        markups = Command.Markups.init(Markup_Tree.from_XML(body)))
  }

  def format(
    msgs: List[XML.Elem],
    margin: Double,
    metric: Font_Metric,
    results: Command.Results
  ) : List[Formatted] = {
    val result = new mutable.ListBuffer[Formatted]
    for (msg <- msgs) {
      if (result.nonEmpty) result += Formatted(Document_ID.make(), Pretty.Separator, Command.Results.empty)

      val id = Protocol_Message.get_serial(msg)
      val body = Pretty.formatted(List(msg), margin = margin, metric = metric)
      result += Formatted(id, body, results)

      Exn.Interrupt.expose()
    }
    result.toList
  }
}
