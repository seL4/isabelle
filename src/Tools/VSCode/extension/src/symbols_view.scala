/*  Title:      Tools/VSCode/extension/src/symbols_view.scala
    Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius
    Author:     Fabian Huch

Isabelle symbols web view.
*/

package isabelle.vscode.extension

import scala.language.unsafeNulls

import VSCode.{Webview, Uri, Extension, Window, Language_Client}

import isabelle._
import isabelle.vscode._


object Symbols_View {
  val control_render =
    for (sym <- List(Symbol.sub, Symbol.sup, Symbol.bold)) yield Symbol.symbols.get(sym).get

  class Provider(
    _context: Extension.Context,
    _language_client: Language_Client
  ) extends Webview.Provider("isabelle-symbols", _context) {
    private var _view: Option[Webview.View] = None
    private var _abbrevs: List[(String, String)] = Nil

    private def update_webview(): Unit = {
      _view.foreach(_.webview.post_message(
        JSON.Object("abbrevs" -> _abbrevs.map((a, b) => List(a, b)))))
    }

    def setup(): Unit = {
      this._language_client.on_notification(LSP.Abbrevs_Response.name,
        { case LSP.Abbrevs_Response(abbrevs) => this.update_abbrevs(abbrevs) })
      this._language_client.send_notification(LSP.Abbrevs_Request())
    }

    def resolve(view: Webview.View): Unit = {
      this._view = Some(view)

      view.webview.html =
        Webviews.get_html(view.webview, _context.uri.platform_path, "Symbols", "symbols_webview.js")

      view.webview.on_message(message =>
        JSON.string(message, "command") match {
          case Some("ready") =>
            this.update_webview()
          case Some("insert_symbol") =>
            JSON.string(message, "symbol").foreach(_insert_symbol)
          case Some("reset_control") =>
            this._reset_control()
          case Some("apply_control") =>
            JSON.string(message, "action").foreach(_apply_control)
          case _ =>
        })
    }

    private def _apply_control(action: String): Unit =
      for {
        editor <- Window.active_editor

        document = editor.document
        selection = editor.selection

        selected_text = document.text(selection.range)
        if !selected_text.isBlank || selection.is_empty

        control_symbols =
          control_render.map(symbol => symbol.name -> Symbol.decode(symbol.symbol)).toMap

        if (control_symbols.contains(action))
        control_symbol = control_symbols(action)
        all_control_symbols = control_symbols.values.toList

      } editor.edit(
        if (!selection.is_empty) {
          val new_text = selected_text
            .split("")
            .map(char => {
              if (char.trim == "") char
              else if (all_control_symbols.contains(char)) ""
              else control_symbol + char
            })
            .mkString
          List(LSP.TextEdit(selection.range, new_text))
        }
        else {
          List(LSP.TextEdit(Line.Range(selection.active), control_symbol))
        })

    private def _insert_symbol(symbol: String): Unit = {
      Window.active_editor.foreach { editor =>
        editor.edit(List(LSP.TextEdit(Line.Range(editor.selection.active), symbol)))
      }
    }

    private def _reset_control(): Unit =
      for {
        editor <- Window.active_editor

        document = editor.document
        selection = editor.selection

        selected_text = document.text(selection.range)
        if !selected_text.isBlank || selection.is_empty

        control_symbols =
          control_render.map(symbol => symbol.name -> Symbol.decode(symbol.symbol)).toMap

        all_control_symbols = control_symbols.values.toList

        if !selection.is_empty
      } editor.edit({
        val new_text = selected_text
          .map(char => if (all_control_symbols.contains(char.toString)) "" else char.toString)
          .mkString

        List(LSP.TextEdit(selection.range, new_text))
      })

    def update_abbrevs(abbrevs: List[(String, String)]): Unit = {
      this._abbrevs = abbrevs
      this.update_webview()
    }
  }
}
