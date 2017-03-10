'use strict';

import * as vscode from 'vscode'
import { Range, MarkedString, DecorationOptions, DecorationRenderOptions,
  TextDocument, TextEditor, TextEditorDecorationType, ExtensionContext, Uri } from 'vscode'


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

const text_colors = [
  "keyword1",
  "keyword2",
  "keyword3",
  "quasi_keyword",
  "improper",
  "operator",
  "tfree",
  "tvar",
  "free",
  "skolem",
  "bound",
  "var",
  "inner_numeral",
  "inner_quoted",
  "inner_cartouche",
  "inner_comment",
  "dynamic",
  "class_parameter",
  "antiquote"
]

function get_color(color: string, light: boolean): string
{
  const config = color + (light ? "_light" : "_dark") + "_color"
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

  function text_color(color: string): TextEditorDecorationType
  {
    return decoration(
      { light: { color: get_color(color, true) },
        dark: { color: get_color(color, false) } })
  }

  function bottom_border(width: string, style: string, color: string): TextEditorDecorationType
  {
    const border = `${width} none; border-bottom-style: ${style}; border-color: `
    return decoration(
      { light: { border: border + get_color(color, true) },
        dark: { border: border + get_color(color, false) } })
  }

  types.clear
  for (const color of background_colors) {
    types["background_" + color] = background(color)
  }
  for (const color of foreground_colors) {
    types["foreground_" + color] = background(color) // approximation
  }
  for (const color of dotted_colors) {
    types["dotted_" + color] = bottom_border("2px", "dotted", color)
  }
  for (const color of text_colors) {
    types["text_" + color] = text_color(color)
  }
  types["spell_checker"] = bottom_border("1px", "solid", "spell_checker")
}


/* decoration for document node */

export interface Decoration
{
  uri: string,
  "type": string,
  content: DecorationOptions[]
}

type Content = Range[] | DecorationOptions[]
const document_decorations = new Map<string, Map<string, Content>>()

export function close_document(document: TextDocument)
{
  document_decorations.delete(document.uri.toString())
}

export function apply_decoration(decoration0: Decoration)
{
  const typ = types[decoration0.type]
  if (typ) {
    const decoration =
    {
      uri: Uri.parse(decoration0.uri).toString(),
      "type": decoration0.type,
      content: decoration0.content
    }

    const document = document_decorations.get(decoration.uri) || new Map<string, Content>()
    document.set(decoration.type, decoration.content)
    document_decorations.set(decoration.uri, document)

    for (const editor of vscode.window.visibleTextEditors) {
      if (decoration.uri === editor.document.uri.toString()) {
        editor.setDecorations(typ, decoration.content)
      }
    }
  }
}

export function update_editor(editor: TextEditor)
{
  if (editor) {
    const decorations = document_decorations.get(editor.document.uri.toString())
    if (decorations) {
      for (const [typ, content] of decorations) {
        editor.setDecorations(types[typ], content)
      }
    }
  }
}
