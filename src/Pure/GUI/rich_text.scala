/*  Title:      Pure/GUI/rich_text.scala
    Author:     Makarius

Support for rendering of rich text, based on individual messages (XML.Elem).
*/

package isabelle


import javax.swing.JComponent

import scala.collection.mutable


object Rich_Text {
  def command(
    body: XML.Body = Nil,
    id: Document_ID.Command = Document_ID.none,
    results: Command.Results = Command.Results.empty
  ): Command = {
    val source = XML.content(body)
    val markups = Command.Markups.init(Markup_Tree.from_XML(body))
    Command.unparsed(source, id = id, results = results, markups = markups)
  }

  def format(
    msgs: List[XML.Elem],
    margin: Double,
    metric: Font_Metric,
    results: Command.Results
  ) : List[Command] = {
    val result = new mutable.ListBuffer[Command]
    for (msg <- msgs) {
      if (result.nonEmpty) {
        result += command(body = Pretty.Separator, id = Document_ID.make())
      }
      val body = Pretty.formatted(List(msg), margin = margin, metric = metric)
      result += command(body = body, id = Protocol_Message.get_serial(msg))

      Exn.Interrupt.expose()
    }
    result.toList
  }

  def make_margin(metric: Font_Metric, margin: Int, limit: Int = -1): Int = {
    val m = (margin * metric.average).toInt
    (if (limit < 0) m else m min limit) max 20
  }

  def component_margin(metric: Font_Metric, component: JComponent): Int =
    make_margin(metric, (component.getWidth.toDouble / metric.average_width).toInt)
}
