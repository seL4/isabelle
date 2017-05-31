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

class Content_Provider implements TextDocumentContentProvider
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
let content_provider: Content_Provider

export function init(context: ExtensionContext, client: LanguageClient)
{
  language_client = client

  content_provider = new Content_Provider()
  context.subscriptions.push(
    workspace.registerTextDocumentContentProvider(preview_uri_scheme, content_provider),
    content_provider)

  language_client.onNotification(protocol.preview_response_type, params =>
    {
      const preview_uri = encode_preview(Uri.parse(params.uri))
      if (preview_uri) {
        preview_content.set(preview_uri.toString(), params.content)
        if (params.column == 0) content_provider.update(preview_uri)
        else commands.executeCommand("vscode.previewHtml", preview_uri, params.column, params.label)
      }
    })
}


/* commands */

function preview_column(split: boolean): ViewColumn
{
  const active_editor = window.activeTextEditor

  if (!active_editor) return ViewColumn.One
  else if (!split) return active_editor.viewColumn
  else if (active_editor.viewColumn === ViewColumn.One) return ViewColumn.Two
  else return ViewColumn.Three
}

export function request(uri?: Uri, split: boolean = false)
{
  const document_uri = uri || window.activeTextEditor.document.uri
  const preview_uri = encode_preview(document_uri)
  if (preview_uri && language_client) {
    language_client.sendNotification(protocol.preview_request_type,
      { uri: document_uri.toString(), column: preview_column(split) })
  }
}

export function update(preview_uri: Uri)
{
  const document_uri = decode_preview(preview_uri)
  if (document_uri && language_client) {
    language_client.sendNotification(protocol.preview_request_type,
      { uri: document_uri.toString(), column: 0 })
  }
}

export function source(preview_uri: Uri)
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
