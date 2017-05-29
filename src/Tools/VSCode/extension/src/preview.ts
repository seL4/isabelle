'use strict';

import { TextDocumentContentProvider, ExtensionContext, Uri, Position,
  workspace, window, commands } from 'vscode'


const uri_scheme = 'isabelle-preview';

class Provider implements TextDocumentContentProvider
{
	constructor() { }

  dispose() { }

  provideTextDocumentContent(uri: Uri): string | Thenable<string>
  {
    const [name, pos] = decode_location(uri)
    return "Isabelle Preview: " + JSON.stringify([name, pos])
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

export function init(context: ExtensionContext)
{
  const provider = new Provider()

  const provider_registration =
    workspace.registerTextDocumentContentProvider(uri_scheme, provider)

 	const command_registration =
    commands.registerTextEditorCommand("isabelle.preview", editor =>
    {
      const uri = encode_location(editor.document.uri, editor.selection.active)
      return workspace.openTextDocument(uri).then(doc => window.showTextDocument(doc, editor.viewColumn + 1))
  	})

  context.subscriptions.push(provider, provider_registration, command_registration)
}
