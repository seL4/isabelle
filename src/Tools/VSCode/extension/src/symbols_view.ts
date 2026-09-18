/*  Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Isabelle symbols web view.
*/

"use strict";

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
  CancellationToken, window } from "vscode"
import { LanguageClient } from "vscode-languageclient/node"

import * as LSP from "./lsp"
import * as Symbol from "./symbol"
import * as Webview from "./webview"


export const view_type = "isabelle-symbols"

export class Provider implements WebviewViewProvider {
  private _view?: WebviewView
  private _abbrevs: [string, string][] = []

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  private update_webview() {
    if (this._view) this._view.webview.postMessage({ abbrevs: this._abbrevs })
  }

  public setup() {
    this._language_client.onNotification(LSP.abbrevs_response_type, params => {
      this.update_abbrevs(params.abbrevs)
    })
    this._language_client.sendNotification(LSP.abbrevs_request_type)
  }

  public resolveWebviewView(
    view: WebviewView,
    _context: WebviewViewResolveContext,
    _token: CancellationToken
  ) {
    this._view = view

    view.webview.options = { enableScripts: true, localResourceRoots: [this._extension_uri] }

    view.webview.html =
      Webview.get_html(this._view.webview, this._extension_uri.fsPath, "Symbols", "symbols_view.js")

    this._view.webview.onDidReceiveMessage(async message =>
      {
        switch (message.command) {
          case "ready":
            this.update_webview()
            break
          case "insert_symbol":
            this._insert_symbol(message.symbol)
            break
          case "reset_control":
            this._reset_control()
            break
          case "apply_control":
            this._apply_control(message.action)
            break
        }
      })
  }

  private _apply_control(action: string): void {
    const editor = window.activeTextEditor
    if (!editor) return

    const document = editor.document
    const selection = editor.selection

    const selected_text = document.getText(selection)
    if (!selected_text.trim() && !selection.isEmpty) return

    const control_symbols: { [key: string]: string } = {}
    Symbol.control_render.forEach(symbol => control_symbols[symbol.name] = symbol.decoded)

    if (!control_symbols[action]) return
    const control_symbol = control_symbols[action]
    const all_control_symbols = Object.values(control_symbols)

    editor.edit(edit_builder => {
      if (!selection.isEmpty) {
        const new_text = selected_text
          .split("")
          .map((char, _index, _arr) => {
            if (char.trim() === "") return char
            if (all_control_symbols.includes(char)) return ""

            return `${control_symbol}${char}`
          })
          .join("")

        edit_builder.replace(selection, new_text)
      }
      else {
        edit_builder.insert(selection.active, control_symbol)
      }
    }).then(success => {
      if (!success) { window.showErrorMessage("Failed to apply control effect.") }
    })
  }

  private _insert_symbol(symbol: string): void {
    const editor = window.activeTextEditor
    if (editor) {
      editor.edit(edit_builder => edit_builder.insert(editor.selection.active, symbol))
    }
  }

  private _reset_control(): void {
    const editor = window.activeTextEditor
    if (!editor) { return }

    const document = editor.document
    const selection = editor.selection

    const selected_text = document.getText(selection)
    if (!selected_text.trim() && !selection.isEmpty) return

    const control_symbols: { [key: string]: string } = {}
    Symbol.control_render.forEach(symbol => control_symbols[symbol.decoded] = symbol.name)

    const all_control_symbols = Object.keys(control_symbols)

    editor.edit(edit_builder => {
      if (!selection.isEmpty) {
        const new_text = selected_text
          .split("")
          .map(char => (all_control_symbols.includes(char) ? "" : char))
          .join("")

        edit_builder.replace(selection, new_text)
      }
    })
  }

  public update_abbrevs(abbrevs: [string, string][]): void {
    this._abbrevs = abbrevs
    this.update_webview()
  }
}
