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
  private var current_output: List[XML.Elem] = Nil
  private var current_formatted: XML.Body = Nil
  private var margin: Double = resources.message_margin

  private val delay_margin = Delay.last(resources.output_delay, channel.Error_Logger) {
    refresh(current_output)
  }

  def resources: VSCode_Resources = session.resources

  def update_margin(new_margin: Double): Unit = {
    margin = new_margin
    delay_margin.invoke()
  }

  def refresh(output: List[XML.Elem]): Unit = {
    val formatted =
      Pretty.formatted(Pretty.separate(output), margin = margin, metric = Symbol.Metric)

    if (formatted != current_formatted) {
      current_output = output
      current_formatted = formatted

      if (resources.html_output) {
        val node_context =
          new Browser_Info.Node_Context {
            override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
              for {
                thy_file <- Position.Def_File.unapply(props)
                def_line <- Position.Def_Line.unapply(props)
                platform_path <- resources.source_file(session.store.ml_settings, thy_file)
                uri = File.uri(Path.explode(File.standard_path(platform_path)).absolute_file)
              } yield HTML.link(uri.toString + "#" + def_line, body)
          }
        val elements = Browser_Info.extra_elements.copy(entity = Markup.Elements.full)
        val html = node_context.make_html(elements, formatted)
        val message = output_json(HTML.source(html).toString, None)
        channel.write(message)
      }
      else {
        def convert_symbols(body: XML.Body): XML.Body =
          body.map {
            case XML.Elem(markup, body) => XML.Elem(markup, convert_symbols(body))
            case XML.Text(content) => XML.Text(resources.output_text(content))
          }

        val converted = convert_symbols(formatted)

        val tree = Markup_Tree.from_XML(converted)
        val text = XML.content(converted)

        val document = Line.Document(text)
        val decorations =
          tree.cumulate[Option[Markup]](Text.Range.full, None, Rendering.text_color_elements,
            { case (_, m) => Some(Some(m.info.markup)) }
          ).flatMap(info =>
              info.info match {
                case Some(markup) =>
                  val range = document.range(info.range)
                  Some((range, "text_" + Rendering.get_text_color(markup).get.toString))
                case None => None
              }
          ).groupMap(_._2)(e => LSP.Decoration_Options(e._1, Nil)).toList

        channel.write(output_json(text, Some(LSP.Decoration(decorations))))
      }
    }
  }
}
