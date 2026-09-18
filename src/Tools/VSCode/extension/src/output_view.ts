/*  Author:     Denis Paluca, TU Muenchen

Isabelle output panel as web view.
*/

"use strict";

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
   CancellationToken } from "vscode"
import { LanguageClient } from "vscode-languageclient/node"

import * as Webview from "./webview"


export const view_type = "isabelle-output"

export class Provider implements WebviewViewProvider {
  private _view?: WebviewView
  private content: string = ""

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  public resolveWebviewView(
    view: WebviewView,
    _context: WebviewViewResolveContext,
    _token: CancellationToken
  ) {
    this._view = view

    // Allow scripts in the webview
    view.webview.options = { enableScripts: true, localResourceRoots: [this._extension_uri]}

    view.webview.html =
      Webview.get_html(this._view.webview, this._extension_uri.fsPath, "Output", "output_view.js")
    view.webview.onDidReceiveMessage(async message =>
      {
        switch (message.command) {
          case "ready":
            view.webview.postMessage(this.content)
            break
          default:
            this._language_client.sendNotification(message.method, message.params)
            break
        }
      })
  }

  public update_content(content: string) {
    this.content = content
    if (this._view) this._view.webview.postMessage(this.content)
  }
}
