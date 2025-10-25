/*  Author:     Diana Korchmar, LMU Muenchen

Isabelle documentation panel as web view.
*/

'use strict';

import {
  WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
  CancellationToken, window, workspace, Webview, env
} from 'vscode'
import { text_colors } from './decorations'
import * as vscode_lib from './vscode_lib'
import * as path from 'path'
import * as lsp from './lsp'
import { commands } from 'vscode'
import { LanguageClient } from 'vscode-languageclient/node';

class Documentation_Panel_Provider implements WebviewViewProvider {
  public static readonly view_type = 'isabelle-documentation';

  private _view?: WebviewView;
  private _documentation_sections: any[] = [];
  private _initialized = false;

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  request(language_client: LanguageClient) {
    if (language_client) {
      this._language_client.sendNotification(lsp.documentation_request_type, { init: true });

    }
  }

  setupDocumentation(language_client: LanguageClient) {
    language_client.onNotification(lsp.documentation_response_type, params => {
      if (!params || !params.sections || !Array.isArray(params.sections)) {
        return;
      }
      this._documentation_sections = params.sections;
      if (this._view) {
        this._update_webview();
      }
    });
  }

  public resolveWebviewView(
    view: WebviewView,
    context: WebviewViewResolveContext,
    _token: CancellationToken
  ): void {
    this._view = view;
    this._view.webview.options = {
      enableScripts: true,
      localResourceRoots: [
        this._extension_uri
      ]
    };

    this._view.webview.html = this._get_html();

    if (Object.keys(this._documentation_sections).length > 0) {
      this._update_webview();
    }

    this._view.webview.onDidReceiveMessage(async message => {
      if (message.command === 'openFile') {
        this._open_document(message.path);
      }
    });

    this._initialized = true;
  }

  private _update_webview(): void {
    if (!this._view) {
      return;
    }

    this._view.webview.postMessage({
      command: 'update',
      sections: this._documentation_sections,
    });
  }

  private _open_document(filePath: string): void {
    let cleanPath = filePath.replace(/^"+|"+$/g, '').trim();

    const isabelleHome = process.env.ISABELLE_HOME;
    if (isabelleHome && cleanPath.includes("$ISABELLE_HOME")) {
      cleanPath = cleanPath.replace("$ISABELLE_HOME", isabelleHome);
    }

    if (cleanPath.startsWith("/cygdrive/")) {
      const match = cleanPath.match(/^\/cygdrive\/([a-zA-Z])\/(.*)/);
      if (match) {
        const driveLetter = match[1].toUpperCase();
        const rest = match[2].replace(/\//g, '\\');
        cleanPath = `${driveLetter}:\\${rest}`;
      }
    }

    const uri = Uri.file(cleanPath);

    if (cleanPath.toLowerCase().endsWith(".pdf")) {
      commands.executeCommand("vscode.open", uri)
    } else {
      workspace.openTextDocument(uri).then(document => {
        window.showTextDocument(document);
      });
    }
  }


  private _get_html(): string {
    return get_webview_html(this._view?.webview, this._extension_uri.fsPath);
  }
}

function get_webview_html(webview: Webview | undefined, extension_path: string): string {
  const script_uri =
    webview.asWebviewUri(Uri.file(path.join(extension_path, 'media', 'documentation.js')))
  const css_uri =
    webview.asWebviewUri(Uri.file(path.join(extension_path, 'media', 'documentation.css')))
  const font_uri =
    webview.asWebviewUri(Uri.file(path.join(extension_path, 'fonts', 'IsabelleDejaVuSansMono.ttf')))

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
        <title>Documentation Panel</title>
      </head>
      <body>
        <div id="documentation-container">Loading documentation...</div>
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

export { Documentation_Panel_Provider, get_webview_html };
