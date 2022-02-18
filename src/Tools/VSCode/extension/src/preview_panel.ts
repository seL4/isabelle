'use strict';

import { ExtensionContext, Uri, window, ViewColumn, WebviewPanel } from 'vscode'
import { LanguageClient } from 'vscode-languageclient'
import * as library from './library'
import * as protocol from './protocol'


let language_client: LanguageClient

class Panel
{
  private webview_panel: WebviewPanel

  public set_content(title: string, body: string)
  {
    this.webview_panel.title = title
    this.webview_panel.webview.html = body
  }

  public reveal(column: ViewColumn)
  {
    this.webview_panel.reveal(column)
  }

  constructor(column: ViewColumn)
  {
    this.webview_panel =
      window.createWebviewPanel("isabelle-preview", "Preview", column,
        {
          enableScripts: true
        })
    this.webview_panel.onDidDispose(() => { panel = null })
  }
}

let panel: Panel

export function setup(context: ExtensionContext, client: LanguageClient)
{
  language_client = client
  language_client.onNotification(protocol.preview_response_type, params =>
    {
      if (!panel) { panel = new Panel(params.column) }
      else panel.reveal(params.column)
      panel.set_content(params.label, params.content)
    })
}

export function request(uri?: Uri, split: boolean = false)
{
  const document_uri = uri || window.activeTextEditor.document.uri
  if (language_client) {
    language_client.sendNotification(protocol.preview_request_type,
      { uri: document_uri.toString(),
        column: library.adjacent_editor_column(window.activeTextEditor, split) })
  }
}
