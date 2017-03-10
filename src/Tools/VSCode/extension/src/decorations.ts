'use strict';

import * as vscode from 'vscode'
import { Position, Range, MarkedString, DecorationOptions, DecorationRenderOptions,
  TextDocument, TextEditor, TextEditorDecorationType, ExtensionContext, Uri } from 'vscode'


/* known decoration types */

export const types = new Map<string, TextEditorDecorationType>()

const background_colors = [
  "unprocessed1",
  "running1",
  "bad",
  "intensify",
  "quoted",
  "antiquoted",
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

interface DecorationOpts {
  range: number[],
  hover_message?: MarkedString | MarkedString[]
}

export interface Decoration
{
  uri: string,
  "type": string,
  content: DecorationOpts[]
}

type Content = Range[] | DecorationOptions[]
const document_decorations = new Map<string, Map<string, Content>>()

export function close_document(document: TextDocument)
{
  document_decorations.delete(document.uri.toString())
}

export function apply_decoration(decoration: Decoration)
{
  const typ = types[decoration.type]
  if (typ) {
    const uri = Uri.parse(decoration.uri).toString()
    const content: DecorationOptions[] = decoration.content.map(opt =>
      {
        const r = opt.range
        return {
          range: new Range(new Position(r[0], r[1]), new Position(r[2], r[3])),
          hoverMessage: opt.hover_message
        }
      })

    const document = document_decorations.get(uri) || new Map<string, Content>()
    document.set(decoration.type, content)
    document_decorations.set(uri, document)

    for (const editor of vscode.window.visibleTextEditors) {
      if (uri === editor.document.uri.toString()) {
        editor.setDecorations(typ, content)
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
