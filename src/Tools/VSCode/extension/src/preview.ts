'use strict';

import { TextDocumentContentProvider, ExtensionContext, Event, EventEmitter, Uri, Position,
  workspace, window, commands } from 'vscode'

import * as library from './library'


/* generated content */

const uri_scheme = 'isabelle-preview';

export function encode_name(document_uri: Uri): Uri
{
  return Uri.parse(uri_scheme + ":Preview?" + JSON.stringify([document_uri.toString()]))
}

export function decode_name(preview_uri: Uri): Uri
{
  const [name] = <[string]>JSON.parse(preview_uri.query)
  return Uri.parse(name)
}

class Provider implements TextDocumentContentProvider
{
  dispose() { }

  private emitter = new EventEmitter<Uri>()
  private waiting: boolean = false;

  get onDidChange(): Event<Uri> { return this.emitter.event }

  public update(document_uri: Uri)
  {
    if (!this.waiting) {
      this.waiting = true
      setTimeout(() =>
      {
        this.waiting = false
        this.emitter.fire(encode_name(document_uri))
      }, 300)
    }
  }

  provideTextDocumentContent(preview_uri: Uri): string | Thenable<string>
  {
    const document_uri = decode_name(preview_uri)
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

export function init(context: ExtensionContext)
{
  const provider = new Provider()
  context.subscriptions.push(workspace.registerTextDocumentContentProvider(uri_scheme, provider))
  context.subscriptions.push(provider)

  context.subscriptions.push(
    commands.registerTextEditorCommand("isabelle.preview", editor =>
    {
      const preview_uri = encode_name(editor.document.uri)
      return workspace.openTextDocument(preview_uri).then(doc =>
        commands.executeCommand("vscode.previewHtml", preview_uri,
          library.other_column(window.activeTextEditor), "Isabelle Preview"))
    }))

  context.subscriptions.push(
    workspace.onDidChangeTextDocument(event =>
    {
      if (event.document.languageId === 'isabelle') {
        provider.update(event.document.uri)
      }
    }))
}
