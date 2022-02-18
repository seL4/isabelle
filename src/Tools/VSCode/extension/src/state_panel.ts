'use strict';

import * as library from './library'
import * as protocol from './protocol'
import { LanguageClient } from 'vscode-languageclient';
import { Uri, ExtensionContext, window, WebviewPanel, ViewColumn } from 'vscode'


let language_client: LanguageClient

function panel_column(): ViewColumn
{
  return library.adjacent_editor_column(window.activeTextEditor, true)
}

class Panel
{
  private state_id: number
  private webview_panel: WebviewPanel

  public get_id(): number { return this.state_id }
  public check_id(id: number): boolean { return this.state_id === id }

  public set_content(id: number, body: string)
  {
    this.state_id = id
    this.webview_panel.webview.html = body
  }

  public reveal()
  {
    this.webview_panel.reveal(panel_column())
  }

  constructor()
  {
    this.webview_panel =
      window.createWebviewPanel("isabelle-state", "State", panel_column(),
        {
          enableScripts: true
        });
    this.webview_panel.onDidDispose(exit_panel)
    this.webview_panel.webview.onDidReceiveMessage(message =>
      {
        switch (message.command) {
          case 'auto_update':
            language_client.sendNotification(
              protocol.state_auto_update_type, { id: this.state_id, enabled: message.enabled })
            break;

          case 'update':
            language_client.sendNotification(protocol.state_update_type, { id: this.state_id })
            break;

          case 'locate':
            language_client.sendNotification(protocol.state_locate_type, { id: this.state_id })
            break;

          default:
            break;
        }
      })
  }
}

let panel: Panel

function exit_panel()
{
  if (panel) {
    language_client.sendNotification(protocol.state_exit_type, { id: panel.get_id() })
    panel = null
  }
}

export function init(uri: Uri)
{
  if (language_client) {
    if (panel) panel.reveal()
    else language_client.sendNotification(protocol.state_init_type)
  }
}

export function setup(context: ExtensionContext, client: LanguageClient)
{
  language_client = client
  language_client.onNotification(protocol.state_output_type, params =>
    {
      if (!panel) { panel = new Panel() }
      panel.set_content(params.id, params.content)
    })
}
