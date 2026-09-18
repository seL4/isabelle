/*  Title:      Tools/VSCode/src/pretty_text_panel.scala
    Author:     Thomas Lindae, TU Muenchen

Pretty-printed text or HTML with decorations.
*/

package isabelle.vscode


import isabelle._


object Pretty_Text_Panel {
  def apply(
    session: VSCode_Session,
    channel: Channel,
    output: (String, Option[LSP.Decoration]) => JSON.T
  ): Pretty_Text_Panel = new Pretty_Text_Panel(session, channel, output)
}

class Pretty_Text_Panel private(
  session: VSCode_Session,
  channel: Channel,
  output_json: (String, Option[LSP.Decoration]) => JSON.T
) {
  def resources: VSCode_Resources = session.resources

  private var current_output: List[XML.Elem] = Nil
  private var current_formatted: XML.Body = Nil
  private var margin: Double = resources.message_margin

  private val delay_margin = channel.Delay.last(resources.output_delay) {
    refresh(current_output)
  }

  def update_margin(new_margin: Double): Unit = {
    margin = new_margin
    delay_margin.invoke()
  }

  def refresh(output: List[XML.Elem]): Unit = {
    if (resources.html_output) {
      if (output != current_output) {
        channel.write(output_json(YXML.string_of_body(output), None))
      }
    }
    else {
      val formatted =
        Pretty.formatted(Pretty.separate(output), margin = margin, metric = Symbol.Metric)

      if (formatted != current_formatted) {
        val converted = resources.output_text_xml(formatted)
        val converted_tree = Markup_Tree.from_XML(converted)
        val converted_text = XML.content(converted)

        val document = Line.Document(converted_text)
        val markups =
          converted_tree.cumulate[Option[Markup]](
            Text.Range.full, None, Rendering.text_color_elements,
            { case (_, m) => Some(Some(m.info.markup)) })
        val entries =
          (for {
            case Text.Info(range, Some(markup)) <- markups
            color <- Rendering.get_text_color(markup)
          } yield color -> document.range(range))
            .groupMap(_._1)(p => LSP.Decoration_Range(p._2))
            .iterator.map({ case (c, rs) => LSP.Decoration_Entry.text_color(c, rs) })
            .toList

        channel.write(output_json(converted_text, Some(LSP.Decoration(entries))))
        current_formatted = formatted
      }
    }
    current_output = output
  }
}
