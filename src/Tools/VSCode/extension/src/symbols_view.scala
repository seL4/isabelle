/*  Title:      Tools/VSCode/extension/src/symbols_view.scala
    Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius
    Author:     Fabian Huch

Isabelle symbols web view.
*/

package isabelle.vscode.extension

import scala.language.unsafeNulls

import VSCode.{Webview, Extension, Window, Language_Client}

import isabelle._
import isabelle.vscode._


object Symbols_View {
  private val control_render =
    (for (sym <- List(Symbol.sub, Symbol.sup, Symbol.bold))
     yield Symbol.control_name(sym).get -> Symbol.decode(sym)).toMap

  class Provider(context: Extension.Context, language_client: Language_Client)
    extends Webview.Provider("isabelle-symbols", context) {

    private var view: Option[Webview.View] = None
    private var abbrevs: List[(String, String)] = Nil

    private def update_webview(): Unit =
      view.foreach(_.webview.post_message(
        JSON.Object("abbrevs" -> abbrevs.map((a, b) => List(a, b)))))

    def setup(): Unit = {
      language_client.on_notification(LSP.Abbrevs_Response.name,
        { case LSP.Abbrevs_Response(abbrevs) => update_abbrevs(abbrevs) })
      language_client.send_notification(LSP.Abbrevs_Request())
    }

    def resolve(view: Webview.View): Unit = {
      this.view = Some(view)

      view.webview.html =
        Webviews.get_html(view.webview, context.uri.platform_path, "Symbols", "symbols_webview.js")

      view.webview.on_message(message =>
        JSON.string(message, "command") match {
          case Some("ready") => update_webview()
          case Some("insert_symbol") => JSON.string(message, "symbol").foreach(insert_symbol)
          case Some("reset_control") => reset_control()
          case Some("apply_control") => JSON.string(message, "action").foreach(apply_control)
          case _ =>
        })
    }

    private def apply_control(action: String): Unit =
      for {
        editor <- Window.active_editor
        selection = editor.selection
        selected_text = editor.document.text(selection.range)
        if !selected_text.isBlank || selection.is_empty
        control_symbol <- control_render.get(action)
      } {
        val all_control_symbols = control_render.values.toList

        if (!selection.is_empty) {
          val new_text = selected_text
            .split("")
            .map(char =>
              if (char.trim == "") char
              else if (all_control_symbols.contains(char)) ""
              else control_symbol + char)
            .mkString
          editor.edit(List(LSP.TextEdit(selection.range, new_text)))
        }
        else editor.edit(List(LSP.TextEdit(Line.Range(selection.active), control_symbol)))
      }

    private def insert_symbol(symbol: String): Unit =
      Window.active_editor.foreach { editor =>
        editor.edit(List(LSP.TextEdit(Line.Range(editor.selection.active), symbol)))
      }

    private def reset_control(): Unit =
      for {
        editor <- Window.active_editor
        selection = editor.selection
        if !selection.is_empty
        selected_text = editor.document.text(selection.range)
        if !selected_text.isBlank
      } {
        val all_control_symbols = control_render.values.toList
        val new_text = selected_text
          .map(char => if (all_control_symbols.contains(char.toString)) "" else char.toString)
          .mkString
        editor.edit(List(LSP.TextEdit(selection.range, new_text)))
      }

    def update_abbrevs(abbrevs: List[(String, String)]): Unit = {
      this.abbrevs = abbrevs
      update_webview()
    }
  }
}
