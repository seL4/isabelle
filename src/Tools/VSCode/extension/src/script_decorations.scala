/*  Title:      Tools/VSCode/extension/src/script_decorations.scala
    Author:     Denis Paluca, TU Muenchen
    Author:     Fabian Huch

Non-unicode Isabelle symbols as text decorations.
*/

package isabelle.vscode.extension

import VSCode.{Decoration, Document, Extension, Text_Editor, Window, Workspace}

import isabelle._


object Script_Decorations {
  enum Style { case sub, sup, bold, control, hidden }

  class Styling extends XML.Traversal {
    private var offset: Text.Offset = 0
    private var rev_stack: List[(Markup, Text.Offset)] = Nil

    private var unhide_start: Set[Text.Offset] = Set.empty
    private var unhide_stop: Set[Text.Offset] = Set.empty
    private var _result: List[(Markup, Text.Range)] = Nil

    def text(s: String): Unit = { offset += s.length }
    def elem(markup: Markup, end: Boolean): Unit = {
      rev_stack ::= markup -> offset
      if (end) end_elem(markup.name)
    }

    def end_elem(name: String): Unit =
      rev_stack.find((markup, _) => markup.name == name) match {
        case Some(elem) =>
          val (unclosed, rest) = rev_stack.splitAt(rev_stack.indexOf(elem))
          unclosed.foreach(unhide_stop += _._2)
          _result ::= elem._1 -> Text.Range(elem._2, offset)
          rev_stack = rest.tail
        case None => unhide_start += offset
      }

    val styles =
      Map(HTML.sub.name -> Style.sub, HTML.sup.name -> Style.sup, HTML.bold.name -> Style.bold)
    def style(markup: Markup): Option[Style] =
      markup match {
        case Markup("span", List("class" -> "hidden")) => Some(Style.hidden)
        case Markup("span", List("class" -> "control")) => Some(Style.control)
        case _ => styles.get(markup.name)
      }

    def result: List[(Style, Text.Range)] = {
      rev_stack.foreach(unhide_stop += _._2)
      for {
        (markup, range) <- _result
        style <- style(markup)
        if style != Style.hidden || (!unhide_start(range.start) && !unhide_stop(range.stop))
      } yield style -> range 
    }
  }

  private def extract_ranges(doc: Document): Map[Style, List[Decoration.Options]] = {
    val styling = new Styling
    HTML.traverse(styling, doc.text, control_blocks = true, hidden = true)

    def doc_range(text_range: Text.Range): Line.Range =
      Line.Range(doc.position(text_range.start), doc.position(text_range.stop))

    styling.result.map((style, text_range) => style ->
      Decoration.Options(doc_range(text_range))).groupMap(_._1)(_._2)
  }

  def register_script_decorations(context: Extension.Context): Unit = {
    val hide =
      Window.create_decoration(
        Decoration.Rendering(
          text_decoration = "none; font-size: 0.001em",
          range_behavior = Decoration.Range_Behavior.closed_closed))

    val superscript =
      Window.create_decoration(
        Decoration.Rendering(
          text_decoration = "none; position: relative; top: -0.5em; font-size: 80%"))

    val subscript =
      Window.create_decoration(
        Decoration.Rendering(
          text_decoration = "none; position: relative; bottom: -0.5em; font-size: 80%"))

    val bold =
      Window.create_decoration(Decoration.Rendering(text_decoration = "none; font-weight: bold"))

    val control =
      Window.create_decoration(
        Decoration.Rendering(text_decoration = "none; font-weight: bold; font-style: italic"))

    def set_decorations(editor: Text_Editor, doc: Document): Unit = {
      val ranges = extract_ranges(doc)

      editor.set_decorations(hide, ranges.getOrElse(Style.hidden, Nil))
      editor.set_decorations(superscript, ranges.getOrElse(Style.sup, Nil))
      editor.set_decorations(subscript, ranges.getOrElse(Style.sub, Nil))
      editor.set_decorations(control, ranges.getOrElse(Style.control, Nil))
      editor.set_decorations(bold, ranges.getOrElse(Style.bold, Nil))
    }

    def handle_change_editor(editor: Text_Editor): Unit = set_decorations(editor, editor.document)
    def handle_set_decorations(change: Document.Change): Unit =
      for (editor <- Window.visible_editors if editor.document.uri == change.document.uri) {
        set_decorations(editor, change.document)
      }

    context.subscribe(hide, superscript, subscript, control, bold,
      Window.on_change_active_editor(_.foreach(handle_change_editor)),
      Workspace.on_change_document(handle_set_decorations))
  }
}
