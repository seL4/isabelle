/*  Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Control panel for Sledgehammer.
*/

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext, CancellationToken,
  window, Webview, Selection, Range, TextDocument, TextDocumentContentChangeEvent } from "vscode";
import * as path from "path";
import { text_colors } from "./decorations";
import * as vscode_lib from "./vscode_lib"
import * as lsp from "./lsp";
import { LanguageClient } from "vscode-languageclient/node";
import { Position } from "vscode";


class Sledgehammer_Panel_Provider implements WebviewViewProvider {
  public static readonly view_type = "isabelle-sledgehammer";
  private _view?: WebviewView;
  private _lastResultPosition?: { uri: string; line: number; character: number; lineText: string };
  private text_to_insert: string;

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  public resolveWebviewView(view: WebviewView, context: WebviewViewResolveContext, _token: CancellationToken): void {
    this._view = view;
    this._view.webview.options = {
      enableScripts: true,
      localResourceRoots: [this._extension_uri]
    };
    this._view.webview.html = this._get_html();
    this._setup_message_handler();
  }

  request_provers(language_client: LanguageClient) {
    if (language_client) {
      this._language_client.sendNotification(lsp.sledgehammer_provers_request_type);
    }
  }

  private _setup_message_handler(): void {
    if (!this._view) return;
    this._view.webview.onDidReceiveMessage(async message => {
      const editor = window.activeTextEditor;
      const pos = editor?.selection.active;

      if (editor && pos) {
        this._language_client.sendNotification(lsp.caret_update_type, {
          uri: editor.document.uri.toString(),
          line: pos.line,
          character: pos.character
        });
      }
      switch (message.command) {
        case "apply":
          this._language_client.sendNotification(lsp.sledgehammer_request_type, {
            provers: message.provers,
            isar: message.isar,
            try0: message.try0,
            purpose: 1
          });

          break;
        case "cancel":
          this._language_client.sendNotification(lsp.sledgehammer_cancel_type);
          break;
        case "locate":
          this._language_client.sendNotification(lsp.sledgehammer_request_type, {
            provers: message.provers,
            isar: message.isar,
            try0: message.try0,
            purpose: 2
          });
          break;

        case "insert_text":
          this._language_client.sendNotification(lsp.sledgehammer_request_type, {
            provers: message.provers,
            isar: message.isar,
            try0: message.try0,
            purpose: 3
          });
          this.text_to_insert = message.text;
          break;
      }
    });
  }

  public update_status(message: string): void {
    if (this._view) {
      this._view.webview.postMessage({ command: "status", message });
    }
  }

  public update_provers(provers: string): void {
    if (this._view) {
      this._view.webview.postMessage({ command: "provers", provers });
    }
  }

  public locate(state_location: { uri: string; line: number; character: number }): void {
    const docUri = Uri.parse(state_location.uri);
    const editor = window.activeTextEditor;

    if (editor && editor.document.uri.toString() === docUri.toString()) {
      const position = new Position(state_location.line, state_location.character);
      editor.selections = [new Selection(position, position)];
      editor.revealRange(new Range(position, position));
    }
  }

  public insert(position: { uri: string; line: number; character: number }): void {
    const editor = window.activeTextEditor;
    if (!editor) return;

    const uri = Uri.parse(position.uri);
    if (editor.document.uri.toString() !== uri.toString()) return;

    const pos = new Position(position.line, position.character);
    const existingLineText = editor.document.lineAt(pos.line).text;
    const textToInsert =
      existingLineText.trim() === "" ? this.text_to_insert : "\n" + this.text_to_insert;

    editor.edit(editBuilder => {
      editBuilder.insert(pos, textToInsert);
    });
  }


  public updateResult(result: lsp.SledgehammerApplyResult): void {
    const editor = window.activeTextEditor;
    const lineText = editor?.document.lineAt(result.position.line).text ?? "";
    this._lastResultPosition = {
      ...result.position,
      lineText
    };

    if (this._view) {
        this._view.webview.postMessage({
          command: "result",
          content: result.content,
          position: result.position,
          sendback_id: result.sendback_id
        });

    }
  }

  public update_no_proof(): void {
    if (this._view) {
      this._view.webview.postMessage({ command: "no_proof" });
    }
  }

  private _get_html(): string {
    return get_webview_html(this._view?.webview, this._extension_uri.fsPath);
  }
}

function get_webview_html(webview: Webview | undefined, extension_path: string): string {
  const script_uri =
    webview?.asWebviewUri(Uri.file(path.join(extension_path, "media", "sledgehammer.js")));
  const css_uri =
    webview?.asWebviewUri(Uri.file(path.join(extension_path, "media", "sledgehammer.css")));
  const font_uri =
    webview.asWebviewUri(Uri.file(path.join(extension_path, "fonts", "IsabelleDejaVuSansMono.ttf")))


  return `
    <!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <link href="${css_uri}" rel="stylesheet">
        <style>
            @font-face {
                font-family: "Isabelle DejaVu Sans Mono";
                src: url(${font_uri});
            }
            ${_get_decorations()}
        </style>
        <title>Sledgehammer Panel</title>
      </head>
      <body>
        <script src="${script_uri}"></script>
      </body>
    </html>`;
}

function _get_decorations(): string {
  let style: string[] = []
  for (const key of text_colors) {
    style.push(`body.vscode-light .${key} { color: ${vscode_lib.get_color(key, true)} }\n`)
    style.push(`body.vscode-dark .${key} { color: ${vscode_lib.get_color(key, false)} }\n`)
  }
  return style.join("")
}

export { Sledgehammer_Panel_Provider, get_webview_html };

export interface PositionInfo {
  uri: string;
  line: number;
  character: number;
}
