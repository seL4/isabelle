/*  Title:      Tools/VSCode/extension/src/output_view.scala
    Author:     Fabian Huch

Isabelle output panel as web view.
*/

package isabelle.vscode.extension

import VSCode.{Extension, Language_Client, Uri, Webview}

import isabelle._
import isabelle.vscode._


object Output_View {
  class Provider(_context: Extension.Context, _language_client: Language_Client)
   extends Webview.Provider("isabelle-output", _context) {

    private var _view: Option[Webview.View] = None
    private var content = ""

    def resolve(view: Webview.View): Unit = {
      this._view = Some(view)

      view.webview.html =
        Webviews.get_html(view.webview, _context.uri.platform_path, "Output", "output_webview.js")
      view.webview.on_message(message =>
        JSON.string(message, "command") match {
          case Some("ready") =>
            view.webview.post_message(content)
          case _ =>
            _language_client.send_notification(message)
        })
    }

    def update_content(content: String): Unit = {
      this.content = content
      this._view.foreach(_.webview.post_message(this.content))
    }
  }
}
