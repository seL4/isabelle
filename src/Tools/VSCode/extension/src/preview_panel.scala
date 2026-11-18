/*  Title:      Tools/VSCode/extension/src/preview_panel.scala
    Author:     Makarius

Preview panel via HTML webview inside VSCode.
*/

package isabelle.vscode.extension

import VSCode.{Language_Client, Uri, Text_Editor, Window}

import isabelle._
import isabelle.vscode._


object Preview_Panel {
  private var language_client: Option[Language_Client] = None

  class Panel(column: Text_Editor.Column) {
    private val webview_panel = Window.create_panel("isabelle-preview", "Preview", column)

    def set_content(title: String, body: String): Unit = {
      webview_panel.title = title
      webview_panel.webview.html = body
    }

    def reveal(column: Text_Editor.Column): Unit = webview_panel.reveal(column)

    webview_panel.on_dispose { _ => panel = None }
  }

  private var panel: Option[Panel] = None

  def setup(client: Language_Client): Unit = {
    language_client = Some(client)
    client.on_notification(LSP.Preview_Response.name,
      {
        case LSP.Preview_Response(_, column, label, content) =>
          panel match {
            case None => panel = Some(new Panel(Text_Editor.Column(column)))
            case Some(panel) => panel.reveal(Text_Editor.Column(column))
          }
          panel.foreach(_.set_content(label, content))
      })
  }

  def request(arg: Any, split: Boolean = false): Unit = {
    val document_uri =
      arg match {
        case uri: Uri => uri
        case _ => Window.active_editor.get.document.uri
      }
    language_client.foreach(
      _.send_notification(
        LSP.Preview_Request(document_uri.toString,
          VSCode_Lib.adjacent_editor_column(Window.active_editor, split).rep)))
  }
}
