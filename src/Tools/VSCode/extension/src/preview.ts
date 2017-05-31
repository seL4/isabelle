'use strict';

import * as timers from 'timers'
import { ViewColumn, TextDocument, TextEditor, TextDocumentContentProvider,
  ExtensionContext, Event, EventEmitter, Uri, Position, workspace,
  window, commands } from 'vscode'
import { LanguageClient } from 'vscode-languageclient';
import * as library from './library'
import * as protocol from './protocol';


/* Uri information */

const preview_uri_template = Uri.parse("isabelle-preview:Preview")
const preview_uri_scheme = preview_uri_template.scheme

function encode_preview(document_uri: Uri | undefined): Uri | undefined
{
  if (document_uri && library.is_file(document_uri)) {
    return preview_uri_template.with({ query: document_uri.fsPath })
  }
  else undefined
}

function decode_preview(preview_uri: Uri | undefined): Uri | undefined
{
  if (preview_uri && preview_uri.scheme === preview_uri_scheme) {
    return Uri.file(preview_uri.query)
  }
  else undefined
}


/* HTML content */

const preview_content = new Map<string, string>()

const default_preview_content =
  `<html>
  <head>
    <meta http-equiv="Content-type" content="text/html; charset=UTF-8">
  </head>
  <body>
    <h1>Isabelle Preview</h1>
  </body>
  </html>`

class Provider implements TextDocumentContentProvider
{
  dispose() { }

  private emitter = new EventEmitter<Uri>()
  public update(preview_uri: Uri) { this.emitter.fire(preview_uri) }
  get onDidChange(): Event<Uri> { return this.emitter.event }

  provideTextDocumentContent(preview_uri: Uri): string
  {
    return preview_content.get(preview_uri.toString()) || default_preview_content
  }
}


/* init */

let language_client: LanguageClient
let provider: Provider

export function init(context: ExtensionContext, client: LanguageClient)
{
  language_client = client

  provider = new Provider()
  context.subscriptions.push(
    workspace.registerTextDocumentContentProvider(preview_uri_scheme, provider),
    provider)

  context.subscriptions.push(
    commands.registerCommand("isabelle.preview", uri => request_preview(uri, false)),
    commands.registerCommand("isabelle.preview-side", uri => request_preview(uri, true)),
    commands.registerCommand("isabelle.preview-source", show_source))

  language_client.onNotification(protocol.preview_response_type,
    params => show_preview(Uri.parse(params.uri), params.column, params.label, params.content))
}


/* commands */

function preview_column(side: boolean): ViewColumn
{
  const active_editor = window.activeTextEditor

  if (!active_editor) return ViewColumn.One
  else if (!side) return active_editor.viewColumn
  else if (active_editor.viewColumn === ViewColumn.One) return ViewColumn.Two
  else return ViewColumn.Three
}

function request_preview(uri?: Uri, side: boolean = false)
{
  const document_uri = uri || window.activeTextEditor.document.uri
  const preview_uri = encode_preview(document_uri)
  if (preview_uri) {
    language_client.sendNotification(protocol.preview_request_type,
      {uri: document_uri.toString(), column: preview_column(side) })
  }
}

function show_preview(document_uri: Uri, column: ViewColumn, label: string, content: string)
{
  const preview_uri = encode_preview(document_uri)
  if (preview_uri) {
    preview_content.set(preview_uri.toString(), content)
    commands.executeCommand("vscode.previewHtml", preview_uri, column, label)
  }
}

function show_source(preview_uri: Uri)
{
  const document_uri = decode_preview(preview_uri)
  if (document_uri) {
    const editor =
      window.visibleTextEditors.find(editor =>
        editor.document.uri.scheme === document_uri.scheme &&
        editor.document.uri.fsPath === document_uri.fsPath)
    if (editor) window.showTextDocument(editor.document, editor.viewColumn)
    else workspace.openTextDocument(document_uri).then(window.showTextDocument)
  }
  else commands.executeCommand("workbench.action.navigateBack")
}
