/*  Title:      Tools/VSCode/extension/src/state_panel.scala
    Author:     Fabian Huch

State panel within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import VSCode.{Extension, Text_Editor, Window, Language_Client}

import isabelle._
import isabelle.vscode._


object State_Panel {
  private var language_client: Option[Language_Client] = None

  def panel_column: Text_Editor.Column =
    VSCode_Lib.adjacent_editor_column(Window.active_editor, true)

  class Panel(context: Extension.Context) {
    private var state: Option[LSP.State_Output] = None
    private val webview_panel = Window.create_panel("isabelle-state", "State", panel_column)

    def get_id: Counter.ID = state.get.id
    def check_id(id: Counter.ID): Boolean = get_id == id

    private def update_webview(): Unit =
      state.foreach(state =>
        webview_panel.webview.post_message(
          JSON.Object("content" -> state.content, "auto_update" -> state.auto_update)))

    def set_content(state: LSP.State_Output): Unit = {
      this.state = Some(state)
      update_webview()
    }

    def reveal(): Unit = webview_panel.reveal(panel_column)

    webview_panel.on_dispose(_ => State_Panel.exit_panel())
    webview_panel.webview.on_message { message =>
      language_client.foreach(language_client =>
        JSON.string(message, "command") match {
          case Some("ready") =>
            update_webview()
          case Some("auto_update") =>
            JSON.bool(message, "enabled").foreach(enabled =>
              language_client.send_notification(LSP.State_Auto_Update(get_id, enabled)))
          case Some("update") =>
            language_client.send_notification(LSP.State_Update(get_id))
          case Some("locate") =>
            language_client.send_notification(LSP.State_Locate(get_id))
          case _ =>
            language_client.send_notification(message)
        })
    }
    webview_panel.webview.html =
      Webviews.get_html(webview_panel.webview, context.uri.platform_path, "Output",
        "state_webview.js")
  }

  private var panel: Option[Panel] = None

  def exit_panel(): Unit = {
    if (panel.isDefined) {
      language_client.foreach(_.send_notification(LSP.State_Exit(panel.get.get_id)))
      panel = None
    }
  }

  def init(): Unit =
    language_client.foreach { language_client =>
      panel match {
        case Some(panel) => panel.reveal()
        case None => language_client.send_request(LSP.State_Init(LSP.Id.empty))
      }
    }

  def setup(context: Extension.Context, client: Language_Client): Unit = {
    language_client = Some(client)
    client.on_notification(LSP.State_Output.name,
      {
        case LSP.State_Output(params) =>
          if (panel.isEmpty) { panel = Some(new Panel(context)) }
          panel.get.set_content(params)
      })
  }
}
