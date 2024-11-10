/*  Title:      Pure/GUI/rich_text.scala
    Author:     Makarius

Support for rendering of rich text, based on individual messages (XML.Elem).
*/

package isabelle


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
}
