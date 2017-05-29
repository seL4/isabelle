'use strict';

import { TextDocumentContentProvider, ExtensionContext, Uri, Position, ViewColumn,
  workspace, window, commands } from 'vscode'


const uri_scheme = 'isabelle-preview';

class Provider implements TextDocumentContentProvider
{
  constructor() { }

  dispose() { }

  provideTextDocumentContent(uri: Uri): string | Thenable<string>
  {
    const [name, pos] = decode_location(uri)
    return `
      <html>
      <head>
        <meta http-equiv="Content-type" content="text/html; charset=UTF-8">
      </head>
      <body>
        <h1>Isabelle Preview</h1>
        <p>${JSON.stringify([name, pos])}</p>
      </body>
      </html>`
  }
}

export function encode_location(uri: Uri, pos: Position): Uri
{
  const query = JSON.stringify([uri.toString(), pos.line, pos.character])
  return Uri.parse(uri_scheme + ":Preview?" + query)
}

export function decode_location(uri: Uri): [Uri, Position]
{
  let [name, line, character] = <[string, number, number]>JSON.parse(uri.query)
  return [Uri.parse(name), new Position(line, character)]
}

function view_column(side_by_side: boolean = true): ViewColumn | undefined
{
  const active = window.activeTextEditor
  if (!active) { return ViewColumn.One }
  if (!side_by_side) { return active.viewColumn }

  if (active.viewColumn == ViewColumn.One) return ViewColumn.Two
  else if (active.viewColumn == ViewColumn.Two) return ViewColumn.Three
  else return ViewColumn.One
}

export function init(context: ExtensionContext)
{
  const provider = new Provider()

  const provider_registration =
    workspace.registerTextDocumentContentProvider(uri_scheme, provider)

  const command_registration =
    commands.registerTextEditorCommand("isabelle.preview", editor =>
    {
      const uri = encode_location(editor.document.uri, editor.selection.active)
      return workspace.openTextDocument(uri).then(doc =>
        commands.executeCommand("vscode.previewHtml", uri, view_column(), "Isabelle Preview"))
    })

  context.subscriptions.push(provider, provider_registration, command_registration)
}
