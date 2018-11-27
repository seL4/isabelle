'use strict';

import * as timers from 'timers'
import { window, OverviewRulerLane } from 'vscode'
import { Position, Range, MarkedString, DecorationOptions, DecorationRenderOptions,
  TextDocument, TextEditor, TextEditorDecorationType, ExtensionContext, Uri } from 'vscode'
import { Decoration } from './protocol'
import * as library from './library'


/* known decoration types */

const background_colors = [
  "unprocessed1",
  "running1",
  "canceled",
  "bad",
  "intensify",
  "quoted",
  "antiquoted",
  "markdown_bullet1",
  "markdown_bullet2",
  "markdown_bullet3",
  "markdown_bullet4"
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
  "main",
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
  "comment1",
  "comment2",
  "comment3",
  "dynamic",
  "class_parameter",
  "antiquote"
]

const text_overview_colors = [
  "unprocessed",
  "running",
  "error",
  "warning"
]


/* setup */

const types = new Map<string, TextEditorDecorationType>()

export function setup(context: ExtensionContext)
{
  function decoration(options: DecorationRenderOptions): TextEditorDecorationType
  {
    const typ = window.createTextEditorDecorationType(options)
    context.subscriptions.push(typ)
    return typ
  }

  function background(color: string): TextEditorDecorationType
  {
    return decoration(
      { light: { backgroundColor: library.get_color(color, true) },
        dark: { backgroundColor: library.get_color(color, false) } })
  }

  function text_color(color: string): TextEditorDecorationType
  {
    return decoration(
      { light: { color: library.get_color(color, true) },
        dark: { color: library.get_color(color, false) } })
  }

  function text_overview_color(color: string): TextEditorDecorationType
  {
    return decoration(
      { overviewRulerLane: OverviewRulerLane.Right,
        light: { overviewRulerColor: library.get_color(color, true) },
        dark: { overviewRulerColor: library.get_color(color, false) } })
  }

  function bottom_border(width: string, style: string, color: string): TextEditorDecorationType
  {
    const border = `${width} none; border-bottom-style: ${style}; border-color: `
    return decoration(
      { light: { border: border + library.get_color(color, true) },
        dark: { border: border + library.get_color(color, false) } })
  }


  /* reset */

  types.forEach(typ =>
  {
    for (const editor of window.visibleTextEditors) {
      editor.setDecorations(typ, [])
    }
    const i = context.subscriptions.indexOf(typ)
    if (i >= 0) context.subscriptions.splice(i, 1)
    typ.dispose()
  })
  types.clear()


  /* init */

  for (const color of background_colors) {
    types.set("background_" + color, background(color))
  }
  for (const color of foreground_colors) {
    types.set("foreground_" + color, background(color)) // approximation
  }
  for (const color of dotted_colors) {
    types.set("dotted_" + color, bottom_border("2px", "dotted", color))
  }
  for (const color of text_colors) {
    types.set("text_" + color, text_color(color))
  }
  for (const color of text_overview_colors) {
    types.set("text_overview_" + color, text_overview_color(color))
  }
  types.set("spell_checker", bottom_border("1px", "solid", "spell_checker"))


  /* update editors */

  for (const editor of window.visibleTextEditors) {
    update_editor(editor)
  }
}


/* decoration for document node */

type Content = Range[] | DecorationOptions[]
const document_decorations = new Map<string, Map<string, Content>>()

export function close_document(document: TextDocument)
{
  document_decorations.delete(document.uri.toString())
}

export function apply_decoration(decoration: Decoration)
{
  const typ = types.get(decoration.type)
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

    for (const editor of window.visibleTextEditors) {
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
        editor.setDecorations(types.get(typ), content)
      }
    }
  }
}


/* handle document changes */

const touched_documents = new Set<TextDocument>()
let touched_timer: NodeJS.Timer

function update_touched_documents()
{
  const touched_editors: TextEditor[] = []
  for (const editor of window.visibleTextEditors) {
    if (touched_documents.has(editor.document)) {
      touched_editors.push(editor)
    }
  }
  touched_documents.clear
  touched_editors.forEach(update_editor)
}

export function touch_document(document: TextDocument)
{
  if (touched_timer) timers.clearTimeout(touched_timer)
  touched_documents.add(document)
  touched_timer = timers.setTimeout(update_touched_documents, 1000)
}
