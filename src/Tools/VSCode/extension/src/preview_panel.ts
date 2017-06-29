'use strict';

import * as timers from 'timers'
import { ViewColumn, TextDocument, TextEditor, TextDocumentContentProvider,
  ExtensionContext, Event, EventEmitter, Uri, Position, workspace,
  window, commands } from 'vscode'
import { LanguageClient } from 'vscode-languageclient';
import * as library from './library'
import * as protocol from './protocol'
import { Content_Provider } from './content_provider'


/* HTML content */

const content_provider = new Content_Provider("isabelle-preview")

function encode_preview(document_uri: Uri | undefined): Uri | undefined
{
  if (document_uri && library.is_file(document_uri)) {
    return content_provider.uri_template.with({ query: document_uri.fsPath })
  }
  else undefined
}

function decode_preview(preview_uri: Uri | undefined): Uri | undefined
{
  if (preview_uri && preview_uri.scheme === content_provider.uri_scheme) {
    return Uri.file(preview_uri.query)
  }
  else undefined
}


/* setup */

let language_client: LanguageClient

export function setup(context: ExtensionContext, client: LanguageClient)
{
  context.subscriptions.push(content_provider.register())

  language_client = client
  language_client.onNotification(protocol.preview_response_type, params =>
    {
      const preview_uri = encode_preview(Uri.parse(params.uri))
      if (preview_uri) {
        content_provider.set_content(preview_uri, params.content)
        content_provider.update(preview_uri)

        const existing_document =
          workspace.textDocuments.find(document =>
            document.uri.scheme === preview_uri.scheme &&
            document.uri.query === preview_uri.query)
        if (!existing_document && params.column != 0) {
          commands.executeCommand("vscode.previewHtml", preview_uri, params.column, params.label)
        }
      }
    })
}


/* commands */

export function request(uri?: Uri, split: boolean = false)
{
  const document_uri = uri || window.activeTextEditor.document.uri
  const preview_uri = encode_preview(document_uri)
  if (preview_uri && language_client) {
    language_client.sendNotification(protocol.preview_request_type,
      { uri: document_uri.toString(),
        column: library.adjacent_editor_column(window.activeTextEditor, split) })
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
    const editor = library.find_file_editor(document_uri)
    if (editor) window.showTextDocument(editor.document, editor.viewColumn)
    else workspace.openTextDocument(document_uri).then(window.showTextDocument)
  }
  else commands.executeCommand("workbench.action.navigateBack")
}
