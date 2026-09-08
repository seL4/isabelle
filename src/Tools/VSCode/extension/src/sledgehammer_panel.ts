/*  Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Control panel for Sledgehammer.
*/

"use strict";

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext, CancellationToken,
  window, Position } from "vscode"
import { LanguageClient } from "vscode-languageclient/node"

import * as LSP from "./lsp"
import * as Webview from "./webview"


export const view_type = "isabelle-sledgehammer"

export class Provider implements WebviewViewProvider{
  private _view?: WebviewView

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  public setup() {
    this._language_client.onNotification(LSP.sledgehammer_status_type, msg =>
      this.update_status(msg.message))
    this._language_client.onNotification(LSP.sledgehammer_output_type, msg =>
      this.update_output(msg.content))
    this._language_client.onNotification(LSP.sledgehammer_insert_type, msg =>
      this.insert(msg))
    this._language_client.onNotification(LSP.sledgehammer_provers_response_type, msg =>
      this.update_provers(msg.provers))
    this.request_provers(this._language_client)
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

  request_provers(language_client: LanguageClient) {
    if (language_client) {
      this._language_client.sendNotification(LSP.sledgehammer_provers_request_type)
    }
  }

  private _setup_message_handler(): void {
    if (this._view) {
      this._view.webview.onDidReceiveMessage(async message => {
        switch (message.command) {
          case "apply":
            this._language_client.sendNotification(LSP.sledgehammer_request_type,
              { provers: message.provers, isar: message.isar, try0: message.try0 })
            break
          case "cancel":
            this._language_client.sendNotification(LSP.sledgehammer_cancel_type)
            break
          case "locate":
            this._language_client.sendNotification(LSP.sledgehammer_locate_type)
            break
          case "sendback":
            this._language_client.sendNotification(LSP.sledgehammer_sendback_type,
              { text: message.text })
            break
        }
      })
    }
  }

  private update_status(message: string): void {
    if (this._view) { this._view.webview.postMessage({ command: "status", message }) }
  }

  private update_provers(provers: string): void {
    if (this._view) { this._view.webview.postMessage({ command: "provers", provers }) }
  }

  private insert(arg: LSP.Sledgehammer_Insert): void {
    const uri = Uri.parse(arg.uri)
    const editor = window.activeTextEditor
    if (editor && editor.document.uri.toString() === uri.toString()) {
      const pos = new Position(arg.line, arg.character)
      const line_text = editor.document.lineAt(pos.line).text
      editor.edit(edit_builder =>
        edit_builder.insert(pos, line_text.trim() === "" ? arg.text : "\n" + arg.text))
    }
  }

  private update_output(content: string): void {
    if (this._view) {
      this._view.webview.postMessage({ command: "result", content: content })
    }
  }

  private _get_html(): string {
    return Webview.get_html(this._view.webview, this._extension_uri.fsPath, "Sledgehammer Panel",
      "sledgehammer.js", "sledgehammer.css")
  }
}
