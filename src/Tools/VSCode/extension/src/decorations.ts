'use strict';

import * as vscode from 'vscode'
import { Range, MarkedString, DecorationOptions, DecorationRenderOptions,
  TextEditorDecorationType, ExtensionContext, Uri } from 'vscode'


/* known decoration types */

export const types = new Map<string, TextEditorDecorationType>()

const background_colors = [
  "unprocessed1",
  "running1",
  "bad",
  "intensify",
  "entity",
  "quoted",
  "antiquoted",
  "active",
  "active_result",
  "markdown_item1",
  "markdown_item2",
  "markdown_item3",
  "markdown_item4"
]

const foreground_colors = [
  "quoted",
  "antiquoted"
]

function property(prop: string, config: string): Object
{
  let res = {}
  res[prop] = vscode.workspace.getConfiguration("isabelle").get<string>(config)
  return res
}

export function init(context: ExtensionContext)
{
  function decoration(options: DecorationRenderOptions): TextEditorDecorationType
  {
    const typ = vscode.window.createTextEditorDecorationType(options)
    context.subscriptions.push(typ)
    return typ
  }

  function background(color: string): TextEditorDecorationType
  {
    const prop = "backgroundColor"
    const light = property(prop, color.concat("_light_color"))
    const dark = property(prop, color.concat("_dark_color"))
    return decoration({ light: light, dark: dark })
  }

  types.clear
  for (let color of background_colors) {
    types["background_".concat(color)] = background(color)
  }
  for (let color of foreground_colors) {
    types["foreground_".concat(color)] = background(color) // approximation
  }
  types["hover_message"] = decoration({})
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
    let uri = Uri.parse(decoration.uri).toString()
    let editor =
      vscode.window.visibleTextEditors.find(
        function (editor) { return uri == editor.document.uri.toString() })
    if (editor) editor.setDecorations(typ, decoration.content)
  }
}