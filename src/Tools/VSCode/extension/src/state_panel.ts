/*  Author:     Makarius

State panel via HTML webview inside VSCode.
*/

"use strict";

import { ExtensionContext, Uri, ViewColumn, WebviewPanel, window } from "vscode"
import { LanguageClient } from "vscode-languageclient/node"

import * as LSP from "./lsp"
import * as VSCode_Lib from "./vscode_lib"
import * as Webview from "./webview"


let language_client: LanguageClient

function panel_column(): ViewColumn {
  return VSCode_Lib.adjacent_editor_column(window.activeTextEditor, true)
}

class Panel {
  private state: LSP.State_Output
  private webview_panel: WebviewPanel
  private readonly _extension_path: string

  public get_id(): number { return this.state.id }
  public check_id(id: number): boolean { return this.state.id === id }

  private update_webview() {
    if (this.webview_panel.webview) {
      this.webview_panel.webview.postMessage(this.state)
    }
  }

  public set_content(state: LSP.State_Output) {
    this.state = state
    this.update_webview()
  }

  public reveal() {
    this.webview_panel.reveal(panel_column())
  }

  constructor(extension_path: string) {
    this._extension_path = extension_path
    this.webview_panel =
      window.createWebviewPanel("isabelle-state", "State", panel_column(), { enableScripts: true })
    this.webview_panel.onDidDispose(exit_panel)
    this.webview_panel.webview.onDidReceiveMessage(message =>
      {
        switch (message.command) {
          case "ready":
            this.update_webview()
            break
          case "auto_update":
            language_client.sendNotification(
              LSP.state_auto_update_type, { id: this.get_id(), enabled: message.enabled })
            break
          case "update":
            language_client.sendNotification(LSP.state_update_type, { id: this.get_id() })
            break
          case "locate":
            language_client.sendNotification(LSP.state_locate_type, { id: this.get_id() })
            break
          default:
            language_client.sendNotification(message.method, message.params)
            break
        }
      })
    this.webview_panel.webview.html =
      Webview.get_html(this.webview_panel.webview, this._extension_path, "Output", "state_panel.js")
  }
}

let panel: Panel

function exit_panel() {
  if (panel) {
    language_client.sendNotification(LSP.state_exit_type, { id: panel.get_id() })
    panel = null
  }
}

export function init(_uri: Uri) {
  if (language_client) {
    if (panel) panel.reveal()
    else language_client.sendRequest(LSP.state_init_type, null)
  }
}

export function setup(context: ExtensionContext, client: LanguageClient) {
  language_client = client
  language_client.onNotification(LSP.state_output_type, params =>
    {
      if (!panel) { panel = new Panel(context.extensionPath) }
      panel.set_content(params)
    })
}
