/*  Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Control panel for Sledgehammer.
*/

"use strict";

import {CancellationToken, Uri, WebviewView, WebviewViewProvider, WebviewViewResolveContext} from "vscode"
import {LanguageClient} from "vscode-languageclient/node"

import * as LSP from "./lsp"
import * as Webview from "./webview"


export const view_type = "isabelle-sledgehammer"

export class Provider implements WebviewViewProvider{
  private _view?: WebviewView

  private _provers: string = ""
  private _status: string = ""
  private _output: string = ""

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  public setup() {
    this._language_client.onNotification(LSP.sledgehammer_status_type, msg =>
      this.update_status(msg.message))
    this._language_client.onNotification(LSP.sledgehammer_output_type, msg =>
      this.update_output(msg.content))
    this._language_client.onNotification(LSP.sledgehammer_provers_response_type, msg =>
      this.update_provers(msg.provers))
    this._language_client.sendNotification(LSP.sledgehammer_provers_request_type)
  }

  public resolveWebviewView(
    view: WebviewView,
    _context: WebviewViewResolveContext,
    _token: CancellationToken
  ): void {
    this._view = view
    this._view.webview.options = { enableScripts: true, localResourceRoots: [this._extension_uri] }
    this._view.webview.html = this._get_html()
    this._setup_message_handler()
  }
  private _setup_message_handler(): void {
    if (this._view) {
      this._view.webview.onDidReceiveMessage(async message => {
        switch (message.command) {
          case "ready":
            this.update_provers(this._provers)
            this.update_status(this._status)
            this.update_output(this._output)
            break
          default:
            this._language_client.sendNotification(message.method, message.params)
            break
        }
      })
    }
  }

  private update_status(message: string): void {
    this._status = message
    if (this._view) { this._view.webview.postMessage({ command: "status", message }) }
  }

  private update_provers(provers: string): void {
    this._provers = provers
    if (this._view) { this._view.webview.postMessage({ command: "provers", provers }) }
  }

  private update_output(content: string): void {
    this._output = content
    if (this._view) {
      this._view.webview.postMessage({ command: "result", content: content })
    }
  }

  private _get_html(): string {
    return Webview.get_html(
      this._view.webview, this._extension_uri.fsPath, "Sledgehammer Panel", "sledgehammer_view.js")
  }
}
