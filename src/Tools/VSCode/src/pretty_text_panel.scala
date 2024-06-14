/*  Title:      Tools/VSCode/src/pretty_text_panel.scala
    Author:     Thomas Lindae, TU Muenchen

Pretty-printed text or HTML with decorations.
*/

package isabelle.vscode

import isabelle._

object Pretty_Text_Panel {
  def apply(
    resources: VSCode_Resources,
    channel: Channel,
    output: (String, Option[LSP.Decoration_List]) => Unit
  ): Pretty_Text_Panel = new Pretty_Text_Panel(resources, channel, output)
}

class Pretty_Text_Panel private(
  resources: VSCode_Resources,
  channel: Channel,
  output: (String, Option[LSP.Decoration_List]) => Unit
) {
  private var current_body: XML.Body = Nil
  private var current_formatted: XML.Body = Nil
  private var margin: Double = resources.message_margin

  private val delay_margin = Delay.last(resources.output_delay, channel.Error_Logger) {
    refresh(current_body)
  }
  
  def update_margin(new_margin: Double): Unit = {
    margin = new_margin
    delay_margin.invoke()
  }

  def refresh(body: XML.Body): Unit = {
    val formatted = Pretty.formatted(Pretty.separate(body), margin = margin, metric = Symbol.Metric)

    if (formatted == current_formatted) return

    current_body = body
    current_formatted = formatted

    if (resources.html_output) {
      val node_context =
        new Browser_Info.Node_Context {
          override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
            for {
              thy_file <- Position.Def_File.unapply(props)
              def_line <- Position.Def_Line.unapply(props)
              source <- resources.source_file(thy_file)
              uri = File.uri(Path.explode(source).absolute_file)
            } yield HTML.link(uri.toString + "#" + def_line, body)
        }
      val elements = Browser_Info.extra_elements.copy(entity = Markup.Elements.full)
      val html = node_context.make_html(elements, formatted)
      output(HTML.source(html).toString, None)
    } else {
      def convert_symbols(body: XML.Body): XML.Body = {
        body.map {
          case XML.Elem(markup, body) => XML.Elem(markup, convert_symbols(body))
          case XML.Text(content) => XML.Text(Symbol.output(resources.unicode_symbols, content))
        }
      }

      val tree = Markup_Tree.from_XML(convert_symbols(formatted))
      val text = resources.output_text(XML.content(formatted))

      val document = Line.Document(text)
      val decorations = tree
        .cumulate(Text.Range.full, None: Option[String], Rendering.text_color_elements, (_, m) => {
          Some(Some(m.info.name))
        })
        .flatMap(e => e._2 match {
          case None => None
          case Some(i) => Some((document.range(e._1), "text_" ++ Rendering.text_color(i).toString))
        })
        .groupMap(_._2)(e => LSP.Decoration_Options(e._1, List())).toList

      output(text, Some(decorations))
    }
  }
}

