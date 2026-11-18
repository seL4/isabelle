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
          case Some("apply_control") => JSON.string(message, "symbol").foreach(edit_control_style)
          case _ =>
        })
    }

    private def edit_control_style(control_sym: Symbol.Symbol): Unit = {
      def update_style(text: String): String =
        Library.string_builder() { result =>
          for (sym <- Symbol.iterator(text) if !HTML.is_control(sym)) {
            if (Symbol.is_controllable(sym)) result ++= control_sym
            result ++= sym
          }
        }

      for (editor <- Window.active_editor) {
        val selection = editor.selection
        val text =
          if (selection.is_empty) control_sym
          else update_style(editor.document.text(selection.range))

        editor.edit(List(LSP.TextEdit(selection.range, text)))
      }
    }

    private def insert_symbol(symbol: Symbol.Symbol): Unit =
      Window.active_editor.foreach { editor =>
        editor.edit(List(LSP.TextEdit(Line.Range(editor.selection.active), symbol)))
      }

    def update_abbrevs(abbrevs: List[(String, String)]): Unit = {
      this.abbrevs = abbrevs
      update_webview()
    }
  }
}
