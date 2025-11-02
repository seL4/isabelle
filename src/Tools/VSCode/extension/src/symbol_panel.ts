/*  Author:     Diana Korchmar, LMU Muenchen

Isabelle symbols panel as web view.
*/

"use strict";

import {
  WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
  CancellationToken, window, Position, Selection, Webview
} from "vscode"
import { text_colors } from "./decorations"
import * as vscode_lib from "./vscode_lib"
import * as path from "path"
import * as lsp from "./lsp"
import { LanguageClient } from "vscode-languageclient/node";
import * as fs from "fs";

class Symbols_Panel_Provider implements WebviewViewProvider {
  public static readonly view_type = "isabelle-symbols"

  private _view?: WebviewView
  private _groupedSymbols: { [key: string]: lsp.Symbol_Entry[] } = {}
  private _initialized = false;
  private _abbrevsFromThy: [string, string][] = [];

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  request( language_client: LanguageClient) {
    if (language_client) {
      this._language_client.sendNotification(lsp.symbols_request_type);
    }
  }

  setup(language_client: LanguageClient) {
    language_client.onNotification(lsp.symbols_response_type, params => {
      if (!params?.symbols || !Array.isArray(params.symbols)) {
        return;

      }

      this._groupedSymbols = this._group_symbols(params.symbols);
      this._abbrevsFromThy = params.abbrevs_from_Thy ?? [];
      if (this._view) {
        this._update_webview();
      }
    });
  }

  public resolveWebviewView(
    view: WebviewView,
    context: WebviewViewResolveContext,
    _token: CancellationToken) {
    this._view = view

    view.webview.options = {
      enableScripts: true,

      localResourceRoots: [
        this._extension_uri
      ]
    }

    view.webview.html = this._get_html()

    if (Object.keys(this._groupedSymbols).length > 0) {
      this._update_webview();
    }

    this._view.webview.onDidReceiveMessage(message => {
      if (message.command === "insertSymbol") {
        this._insert_symbol(message.symbol);
      }
      else if (message.command === "resetControlSymbols") {
        this._reset_control_symbols();
      }
      else if (message.command === "applyControl") {
        this._apply_control_effect(message.action);
      }
    });


    this._initialized = true;
  }

  private _apply_control_effect(action: string): void {
    const editor = window.activeTextEditor;
    if (!editor) return;

    const document = editor.document;
    const selection = editor.selection;
    let selectedText = document.getText(selection);

    if (!selectedText.trim() && !selection.isEmpty) return;

    const control_group = this._groupedSymbols["control"];
    if (!control_group) return;

    const control_symbols: { [key: string]: string } = {};
    control_group.forEach(symbol => {
      if (symbol.name === "sup" || symbol.name === "sub" || symbol.name === "bold") {
        control_symbols[symbol.name] = String.fromCodePoint(symbol.code);
      }
    });

    if (!control_symbols[action]) return;
    const control_symbol = control_symbols[action];
    const all_control_symbols = Object.values(control_symbols);


    editor.edit(edit_builder => {
      if (!selection.isEmpty) {
        if (action === "bold") {
          editor.setDecorations(this.boldDecoration, [{ range: selection }]);
        }
        else {
          let new_text = selectedText
            .split("")
            .map((char, index, arr) => {
              const prevChar = index > 0 ? arr[index - 1] : null;
              if (char.trim() === "") return char;
              if (all_control_symbols.includes(char)) return "";

              return `${control_symbol}${char}`;
            })
            .join("");

          edit_builder.replace(selection, new_text);
        }
      }
      else {
        edit_builder.insert(selection.active, control_symbol);
      }
    }).then(success => {
      if (!success) {
        window.showErrorMessage("Failed to apply control effect.");
      }
    });
  }

  private _insert_symbol(symbol: string): void {
    const editor = window.activeTextEditor;
    if (editor) {
      editor.edit(editBuilder => {
        editBuilder.insert(editor.selection.active, symbol);
      });
    }
  }

  private boldDecoration = window.createTextEditorDecorationType({
    fontWeight: "bold",
    textDecoration: "none"
  });

  private _reset_control_symbols(): void {
    const editor = window.activeTextEditor;
    if (!editor) {
      return;
    }

    const document = editor.document;
    const selection = editor.selection;
    let selectedText = document.getText(selection);

    if (!selectedText.trim() && !selection.isEmpty) return;

    const control_group = this._groupedSymbols["control"];
    if (!control_group) return;


    const control_symbols: { [key: string]: string } = {};
    control_group.forEach(symbol => {
      if (symbol.name === "sup" || symbol.name === "sub" || symbol.name === "bold") {
        control_symbols[String.fromCodePoint(symbol.code)] = symbol.name;
      }
    });

    const all_control_symbols = Object.keys(control_symbols);

    editor.edit(edit_builder => {
      if (!selection.isEmpty) {
        if (this.boldDecoration) {
          editor.setDecorations(this.boldDecoration, []);
        }

        let new_text = selectedText
          .split("")
          .map(char => (all_control_symbols.includes(char) ? "" : char))
          .join("");

        edit_builder.replace(selection, new_text);
      }
    }).then(success => {
      if (!success) {
      }
    });
  }

  private _update_webview(): void {
    this._view.webview.postMessage({
      command: "update",
      symbols: this._groupedSymbols,
      abbrevs_from_Thy: this._abbrevsFromThy,
    });
  }

  private _group_symbols(symbols: lsp.Symbol_Entry[]): { [key: string]: lsp.Symbol_Entry[] } {
    const grouped_symbols: { [key: string]: lsp.Symbol_Entry[] } = {};
    symbols.forEach(symbol => {
      if (!symbol.groups || !Array.isArray(symbol.groups)) {
        return;
      }

      symbol.groups.forEach(group => {
        if (!grouped_symbols[group]) {
          grouped_symbols[group] = [];
        }
        grouped_symbols[group].push(symbol);
      });
    });
    return grouped_symbols;
  }

  private _get_html(): string {
    return get_webview_html(this._view.webview, this._extension_uri.fsPath)
  }
}

function open_webview_link(link: string) {
  const uri = Uri.parse(link)
  const line = Number(uri.fragment) || 0
  const pos = new Position(line, 0)
  window.showTextDocument(uri.with({ fragment: "" }), {
    preserveFocus: false,
    selection: new Selection(pos, pos)
  })
}

function get_webview_html(webview: Webview, extension_path: string): string {
  const script_uri = webview.asWebviewUri(Uri.file(path.join(extension_path, "media", "symbols.js")))
  const css_uri = webview.asWebviewUri(Uri.file(path.join(extension_path, "media", "symbols.css")))
  const font_uri =
    webview.asWebviewUri(Uri.file(path.join(extension_path, "fonts", "IsabelleDejaVuSansMono.ttf")))

  return `<!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <link href="${css_uri}" rel="stylesheet" type="text/css">
        <style>
            @font-face {
                font-family: "Isabelle DejaVu Sans Mono";
                src: url(${font_uri});
            }
            ${_get_decorations()}
        </style>
        <title>Symbols Panel</title>
      </head>
      <body>
        <div id="symbols-container"></div>
        <script src="${script_uri}"></script>
      </body>
    </html>`
}

function _get_decorations(): string {
  let style: string[] = []
  for (const key of text_colors) {
    style.push(`body.vscode-light .${key} { color: ${vscode_lib.get_color(key, true)} }\n`)
    style.push(`body.vscode-dark .${key} { color: ${vscode_lib.get_color(key, false)} }\n`)
  }
  return style.join("")
}

export { Symbols_Panel_Provider, get_webview_html, open_webview_link }
