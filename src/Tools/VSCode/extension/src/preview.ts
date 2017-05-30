'use strict';

import * as timers from 'timers'
import { TextDocument, TextEditor, TextDocumentContentProvider, ExtensionContext,
  Event, EventEmitter, Uri, Position, workspace, window, commands } from 'vscode'
import * as library from './library'


/* generated content */

const uri_scheme = 'isabelle-preview';

export function encode_preview(document_uri: Uri): Uri
{
  return Uri.parse(uri_scheme + ":Preview?" + JSON.stringify([document_uri.toString()]))
}

export function decode_preview(preview_uri: Uri): Uri
{
  const [name] = <[string]>JSON.parse(preview_uri.query)
  return Uri.parse(name)
}

class Provider implements TextDocumentContentProvider
{
  dispose() { }

  private emitter = new EventEmitter<Uri>()
  public update(preview_uri: Uri) { this.emitter.fire(preview_uri) }
  get onDidChange(): Event<Uri> { return this.emitter.event }

  provideTextDocumentContent(preview_uri: Uri): string | Thenable<string>
  {
    const document_uri = decode_preview(preview_uri)
    const editor =
      window.visibleTextEditors.find(editor =>
        document_uri.toString() === editor.document.uri.toString())
    return `
      <html>
      <head>
        <meta http-equiv="Content-type" content="text/html; charset=UTF-8">
      </head>
      <body>
        <h1>Isabelle Preview</h1>
        <ul>
        <li><b>file</b> = <code>${document_uri.fsPath}</code></li>` +
        (editor ? `<li><b>line count</b> = ${editor.document.lineCount}</li>` : "") +
        `</ul>
      </body>
      </html>`
  }
}


/* init */

let provider: Provider

export function init(context: ExtensionContext)
{
  provider = new Provider()
  context.subscriptions.push(workspace.registerTextDocumentContentProvider(uri_scheme, provider))
  context.subscriptions.push(provider)

  context.subscriptions.push(
    commands.registerTextEditorCommand("isabelle.preview", editor =>
    {
      const preview_uri = encode_preview(editor.document.uri)
      return workspace.openTextDocument(preview_uri).then(doc =>
        commands.executeCommand("vscode.previewHtml", preview_uri,
          library.other_column(window.activeTextEditor), "Isabelle Preview"))
    }))
}


/* handle document changes */

const touched_documents = new Set<TextDocument>()
let touched_timer: NodeJS.Timer

function update_touched_documents()
{
  if (provider) {
    for (const document of touched_documents) {
      provider.update(encode_preview(document.uri))
    }
  }
}

export function touch_document(document: TextDocument)
{
  if (library.is_file(document.uri) && document.languageId === 'isabelle') {
    if (touched_timer) timers.clearTimeout(touched_timer)
    touched_documents.add(document)
    touched_timer = timers.setTimeout(update_touched_documents, 300)
  }
}
