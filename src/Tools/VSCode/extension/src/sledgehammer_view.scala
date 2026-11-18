/*  Title:      Tools/VSCode/extension/src/sledgehammer_view.scala
    Author:     Fabian Huch

Sledgehammer view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import VSCode.{Extension, Language_Client, Webview}

import isabelle._
import isabelle.vscode._


object Sledgehammer_View {
  class Provider(context: Extension.Context, language_client: Language_Client)
    extends Webview.Provider("isabelle-sledgehammer", context) {

    private var view: Option[Webview.View] = None

    private var provers: String = ""
    private var status: String = ""
    private var output: String = ""

    def setup(): Unit = {
      language_client.on_notification(LSP.Sledgehammer_Status.name,
        { case LSP.Sledgehammer_Status(status) => update_status(status) })
      language_client.on_notification(LSP.Sledgehammer_Output.name,
        { case LSP.Sledgehammer_Output(output) => update_output(output) })
      language_client.on_notification(LSP.Sledgehammer_Provers_Response.name,
        { case LSP.Sledgehammer_Provers_Response(provers) => update_provers(provers) })
      language_client.send_notification(LSP.Sledgehammer_Provers_Request())
    }

    def resolve(view: Webview.View): Unit = {
      this.view = Some(view)
      view.webview.html =
        Webviews.get_html(view.webview, context.uri.platform_path, "Sledgehammer Panel",
          "sledgehammer_webview.js")
      setup_message_handler()
    }

    private def setup_message_handler(): Unit =
      view.foreach(_.webview.on_message(message =>
        JSON.string(message, "command") match {
          case Some("ready") =>
            update_provers(provers)
            update_status(status)
            update_output(output)
          case _ =>
            language_client.send_notification(message)
        }))

    private def update_status(message: String): Unit = {
      this.status = message
      view.foreach(_.webview.post_message(JSON.Object("command" -> "status", "message" -> message)))
    }

    private def update_provers(provers: String): Unit = {
      this.provers = provers
      view.foreach(
        _.webview.post_message(JSON.Object("command" -> "provers", "provers" -> provers)))
    }

    private def update_output(content: String): Unit = {
      this.output = content
      view.foreach(_.webview.post_message(JSON.Object("command" -> "result", "content" -> content)))
    }
  }
}
