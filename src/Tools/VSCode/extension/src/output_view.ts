/*  Author:     Denis Paluca, TU Muenchen

Isabelle output panel as web view.
*/

'use strict';

import { WebviewViewProvider, WebviewView, Uri, WebviewViewResolveContext,
   CancellationToken, window, Position, Selection, Webview} from 'vscode'
import { text_colors } from './decorations'
import * as vscode_lib from './vscode_lib'
import * as path from 'path'
import * as lsp from './lsp'
import { LanguageClient } from 'vscode-languageclient/node';


class Output_View_Provider implements WebviewViewProvider
{

  public static readonly view_type = 'isabelle-output'

  private _view?: WebviewView
  private content: string = ''

  constructor(
    private readonly _extension_uri: Uri,
    private readonly _language_client: LanguageClient
  ) { }

  public resolveWebviewView(
    view: WebviewView,
    context: WebviewViewResolveContext,
    _token: CancellationToken)
  {
    this._view = view

    view.webview.options = {
      // Allow scripts in the webview
      enableScripts: true,

      localResourceRoots: [
        this._extension_uri
      ]
    }

    view.webview.html = this._get_html(this.content)
    view.webview.onDidReceiveMessage(async message =>
    {
      switch (message.command) {
        case "open":
          open_webview_link(message.link)
          break
        case "resize":
          this._language_client.sendNotification(
            lsp.output_set_margin_type, { margin: message.margin })
          break
      }
    })
  }

  public update_content(content: string)
  {
    if (!this._view) {
      this.content = content
      return
    }

    this._view.webview.html = this._get_html(content)
  }

  private _get_html(content: string): string
  {
    return get_webview_html(content, this._view.webview, this._extension_uri.fsPath)
  }
}

function open_webview_link(link: string)
{
  const uri = Uri.parse(link)
  const line = Number(uri.fragment) || 0
  const pos = new Position(line, 0)
  window.showTextDocument(uri.with({ fragment: '' }), {
    preserveFocus: false,
    selection: new Selection(pos, pos)
  })
}

function get_webview_html(content: string, webview: Webview, extension_path: string): string
{
  const script_uri = webview.asWebviewUri(Uri.file(path.join(extension_path, 'media', 'main.js')))
  const css_uri = webview.asWebviewUri(Uri.file(path.join(extension_path, 'media', 'vscode.css')))
  const font_uri =
    webview.asWebviewUri(Uri.file(path.join(extension_path, 'fonts', 'IsabelleDejaVuSansMono.ttf')))

  return `<!DOCTYPE html>
    <html lang='en'>
      <head>
        <meta charset='UTF-8'>
        <meta name='viewport' content='width=device-width, initial-scale=1.0'>
        <link href='${css_uri}' rel='stylesheet' type='text/css'>
        <style>
            @font-face {
                font-family: "Isabelle DejaVu Sans Mono";
                src: url(${font_uri});
            }
            ${_get_decorations()}
        </style>
        <title>Output</title>
      </head>
      <body>
        ${content}
        <script src='${script_uri}'></script>
      </body>
    </html>`
}

function _get_decorations(): string
{
  let style: string[] = []
  for (const key of text_colors) {
    style.push(`body.vscode-light .${key} { color: ${vscode_lib.get_color(key, true)} }\n`)
    style.push(`body.vscode-dark .${key} { color: ${vscode_lib.get_color(key, false)} }\n`)
  }
  return style.join("")
}

export { Output_View_Provider, get_webview_html, open_webview_link }
