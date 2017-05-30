'use strict';

import * as timers from 'timers'
import { TextDocument, TextEditor, TextDocumentContentProvider, ExtensionContext,
  Event, EventEmitter, Uri, Position, workspace, window, commands } from 'vscode'
import * as library from './library'


/* HTML content */

const preview_uri = Uri.parse("isabelle-preview:Preview")

const default_preview_content =
  `<html>
  <head>
    <meta http-equiv="Content-type" content="text/html; charset=UTF-8">
  </head>
  <body>
    <h1>Isabelle Preview</h1>
  </body>
  </html>`

let preview_content = default_preview_content

class Provider implements TextDocumentContentProvider
{
  dispose() { }

  private emitter = new EventEmitter<Uri>()
  public update() { this.emitter.fire(preview_uri) }
  get onDidChange(): Event<Uri> { return this.emitter.event }

  provideTextDocumentContent(uri: Uri): string { return preview_content }
}

export function update(content: string)
{
  preview_content = content === "" ? default_preview_content : content
  provider.update()
  commands.executeCommand("vscode.previewHtml", preview_uri,
    library.other_column(window.activeTextEditor), "Isabelle Preview")
}


/* init */

let provider: Provider

export function init(context: ExtensionContext)
{
  provider = new Provider()
  context.subscriptions.push(workspace.registerTextDocumentContentProvider(preview_uri.scheme, provider))
  context.subscriptions.push(provider)
}
