/*  Title:      Tools/VSCode/extension/src/sledgehammer_view.scala
    Author:     Fabian Huch

Sledgehammer view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import VSCode.{Extension, Language_Client, Uri, Webview}

import isabelle._
import isabelle.vscode._


object Sledgehammer_View {
  class Provider(_context: Extension.Context, _language_client: Language_Client)
   extends Webview.Provider("isabelle-sledgehammer", _context) {
    private var _view: Option[Webview.View] = None

    private var _provers: String = ""
    private var _status: String = ""
    private var _output: String = ""

    def setup(): Unit = {
      this._language_client.on_notification(LSP.Sledgehammer_Status.name,
        { case LSP.Sledgehammer_Status(status) => update_status(status) })
      this._language_client.on_notification(LSP.Sledgehammer_Output.name,
        { case LSP.Sledgehammer_Output(output) => update_output(output) })
      this._language_client.on_notification(LSP.Sledgehammer_Provers_Response.name,
        { case LSP.Sledgehammer_Provers_Response(provers) => update_provers(provers) })
      this._language_client.send_notification(LSP.Sledgehammer_Provers_Request())
    }

    def resolve(view: Webview.View): Unit = {
      this._view = Some(view)
      view.webview.html = this._get_html()
      this._setup_message_handler()
    }
    private def _setup_message_handler(): Unit =
      this._view.foreach(_.webview.on_message(message =>
        JSON.string(message, "command") match {
          case Some("ready") =>
            this.update_provers(this._provers)
            this.update_status(this._status)
            this.update_output(this._output)
          case _ =>
            _language_client.send_notification(message)
        }))

    private def update_status(message: String): Unit = {
      this._status = message
      this._view.foreach { _.webview.post_message(
        JSON.Object("command" -> "status", "message" -> message)) }
    }

    private def update_provers(provers: String): Unit = {
      this._provers = provers
      this._view.foreach { _.webview.post_message(
        JSON.Object("command" -> "provers", "provers" -> provers)) }
    }

    private def update_output(content: String): Unit = {
      this._output = content
      this._view.foreach {
        _.webview.post_message(JSON.Object("command" -> "result", "content" -> content))
      }
    }

    private def _get_html(): String = {
      Webviews.get_html(
        this._view.get.webview, this._context.uri.platform_path, "Sledgehammer Panel",
          "sledgehammer_webview.js")
    }
  }
}
