/*  Title:      Tools/VSCode/extension/src/decorations.scala
    Author:     Makarius
    Author:     Fabian Huch

PIDE document decorations.
*/

package isabelle.vscode.extension

import VSCode.{Decoration, Uri, Extension, Text_Editor, Window, Document}

import scala.scalajs.js

import isabelle._
import isabelle.vscode._


object Decorations {
  /* known decoration types */

  val background_colors =
    List(
      "unprocessed1",
      "running1",
      "canceled",
      "bad",
      "intensify",
      "quoted",
      "antiquoted",
      "markdown_bullet1",
      "markdown_bullet2",
      "markdown_bullet3",
      "markdown_bullet4")

  val foreground_colors =
    List(
      "quoted",
      "antiquoted")

  val dotted_colors =
    List(
      "writeln",
      "information",
      "warning")

  val text_colors =
    List(
      "main",
      "keyword1",
      "keyword2",
      "keyword3",
      "quasi_keyword",
      "improper",
      "operator",
      "tfree",
      "tvar",
      "free",
      "skolem",
      "bound",
      "var",
      "inner_numeral",
      "inner_quoted",
      "inner_cartouche",
      "comment1",
      "comment2",
      "comment3",
      "dynamic",
      "class_parameter",
      "antiquote",
      "raw_text",
      "plain_text")

  val text_overview_colors =
    List(
      "unprocessed",
      "running",
      "error",
      "warning")


  /* setup */

  private var types = Map.empty[String, Decoration]

  def setup(context: Extension.Context): Unit = {
    def decoration(options: Decoration.Rendering): Decoration = {
      val typ = Window.create_decoration(options)
      context.subscribe(typ)
      typ
    }

    def background(color: String): Decoration = {
      decoration(
        Decoration.Rendering(
          light = Decoration.Themed(background_color = VSCode_Lib.get_color(color, true)),
          dark = Decoration.Themed(background_color = VSCode_Lib.get_color(color, false))))
    }

    def text_color(color: String): Decoration = {
      decoration(
        Decoration.Rendering(
          light = Decoration.Themed(color = VSCode_Lib.get_color(color, true)),
          dark = Decoration.Themed(color = VSCode_Lib.get_color(color, false))))
    }

    def text_overview_color(color: String): Decoration = {
      decoration(
        Decoration.Rendering(
          overview_ruler_lane = Decoration.Overview_Ruler_Lane.right,
          light = Decoration.Themed(overview_ruler_color = VSCode_Lib.get_color(color, true)),
          dark = Decoration.Themed(overview_ruler_color = VSCode_Lib.get_color(color, false))))
    }

    def bottom_border(width: String, style: String, color: String): Decoration = {
      val border = width + " none; border-bottom-style: " + style + "; border-color: "
      decoration(
        Decoration.Rendering(
          light = Decoration.Themed(border = border + VSCode_Lib.get_color(color, true)),
          dark = Decoration.Themed(border = border + VSCode_Lib.get_color(color, false))))
    }


    /* reset */

    types.values.foreach { typ =>
      for (editor <- Window.visible_editors) { editor.set_decorations(typ) }
      context.unsubscribe(typ)
      typ.dispose()
    }
    types = Map.empty


    /* init */

    for (color <- background_colors) {
      types += "background_" + color -> background(color)
    }
    for (color <- foreground_colors) {
      types += "foreground_" + color -> background(color) // approximation
    }
    for (color <- dotted_colors) {
      types += "dotted_" + color -> bottom_border("2px", "dotted", color)
    }
    for (color <- text_colors) {
      types += "text_" + color -> text_color(color)
    }
    for (color <- text_overview_colors) {
      types += "text_overview_" + color -> text_overview_color(color)
    }
    types += "spell_checker" -> bottom_border("1px", "solid", "spell_checker")


    /* update editors */

    Window.visible_editors.foreach(update_editor)
  }


  /* decoration for document node */

  private var document_decorations =
    Map.empty[Uri, Map[String, List[Decoration.Options]]]

  def close_document(document: Document): Unit = {
    document_decorations -= document.uri
  }

  def apply_decoration(decoration: LSP.Decoration): Unit = {
    val uri = Uri.parse(decoration.uri)

    for {
      decoration <- decoration.entries
      typ <- types.get(decoration.typ)
    } {
      val content = decoration.content.map(opt =>
        Decoration.Options(opt.range, opt.hover_message))

      val document = document_decorations.getOrElse(uri, Map.empty)
      document_decorations += uri -> (document + (decoration.typ -> content))

      for {
        editor <- Window.visible_editors
        if uri == editor.document.uri
      } editor.set_decorations(typ, content)
    }
  }

  def update_editor(editor: Text_Editor): Unit =
    for {
      decorations <- document_decorations.get(editor.document.uri)
      (name, content) <- decorations
      typ <- types.get(name)
    } editor.set_decorations(typ, content)


  /* handle document changes */

  private var touched_documents = Set.empty[Document]
  private var touched_timer: Option[js.timers.SetTimeoutHandle] = None

  private def update_touched_documents(): Unit = {
    val touched_editors = new scala.collection.mutable.ListBuffer[Text_Editor]
    for {
      editor <- Window.visible_editors
      if touched_documents(editor.document)
    } touched_editors += editor

    touched_documents = Set.empty
    touched_editors.foreach(update_editor)
  }

  def touch_document(document: Document): Unit = {
    touched_timer.foreach(js.timers.clearTimeout)
    touched_documents += document
    touched_timer = Some(js.timers.setTimeout(1000) { update_touched_documents() })
  }
}
