'use strict';

import * as vscode from 'vscode'
import { Range, MarkedString, DecorationOptions, DecorationRenderOptions,
  TextEditorDecorationType, ExtensionContext, Uri } from 'vscode'


/* known decoration types */

export interface Decorations
{
  test: TextEditorDecorationType
}

export let types: Readonly<Decorations>

export function init(context: ExtensionContext)
{
  function decoration(options: DecorationRenderOptions): TextEditorDecorationType
  {
    const typ = vscode.window.createTextEditorDecorationType(options)
    context.subscriptions.push(typ)
    return typ
  }

  if (!types)
    types =
    {
      test: decoration({ backgroundColor: 'rgba(255,0,0,0.3)' })
    }
}


/* decoration for document node */

export interface Decoration
{
  uri: string,
  "type": string,
  content: DecorationOptions[]
}

export function apply(decoration: Decoration)
{
  let typ = types[decoration.type]
  if (typ) {
    let editor =
      vscode.window.visibleTextEditors.find(
        function (editor) { return decoration.uri == editor.document.uri.toString() })
    if (editor) editor.setDecorations(typ, decoration.content)
  }
}