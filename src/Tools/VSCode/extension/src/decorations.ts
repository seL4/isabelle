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

const dotted_colors = [
  "writeln",
  "information",
  "warning"
]

function get_color(color: string, light: boolean): string
{
  const config = color.concat(light ? "_light" : "_dark").concat("_color")
  return vscode.workspace.getConfiguration("isabelle").get<string>(config)
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
    return decoration(
      { light: { backgroundColor: get_color(color, true) },
        dark: { backgroundColor: get_color(color, false) } })
  }

  function dotted(color: string): TextEditorDecorationType
  {
    const border = "2px none; border-bottom-style: dotted; border-color: "
    return decoration(
      { light: { border: border.concat(get_color(color, true)) },
        dark: { border: border.concat(get_color(color, false)) } })
  }

  types.clear
  for (let color of background_colors) {
    types["background_".concat(color)] = background(color)
  }
  for (let color of foreground_colors) {
    types["foreground_".concat(color)] = background(color) // approximation
  }
  for (let color of dotted_colors) {
    types["dotted_".concat(color)] = dotted(color)
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
    let uri = Uri.parse(decoration.uri).toString()
    let editor =
      vscode.window.visibleTextEditors.find(
        function (editor) { return uri == editor.document.uri.toString() })
    if (editor) editor.setDecorations(typ, decoration.content)
  }
}