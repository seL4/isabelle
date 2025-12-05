/*  Author:     Denis Paluca, TU Muenchen

Non-unicode Isabelle symbols as text decorations.
*/

'use strict';

import { DecorationRangeBehavior, ExtensionContext, Range,
  TextDocument, TextEditor, window, workspace } from 'vscode'

const arrows = {
  sub: '\u21e9',
  sup: '\u21e7',
  bsub: '\u21d8',
  esub: '\u21d9',
  bsup: '\u21d7',
  esup: '\u21d6',
  bold: '\u2759'
}
const no_hide_list = [' ', '\n', '\r', ...Object.values(arrows)]

function should_hide(next_char: string): boolean
{
  return !no_hide_list.includes(next_char)
}

function find_closing(close: string, text: string, open_index: number): number | undefined
{
  let close_index = open_index
  let counter = 1
  const open = text[open_index]
  while (counter > 0) {
    let c = text[++close_index]

    if (c === undefined) return

    if (c === open) {
      counter++
    }
    else if (c === close) {
      counter--
    }
  }
  return close_index
}



function extract_ranges(doc: TextDocument)
{
  const text = doc.getText()
  const hide_ranges: Range[] = []
  const sup_ranges: Range[] = []
  const sub_ranges: Range[] = []
  const bold_ranges: Range[] = []

  for (let i = 0; i < text.length - 1; i++) {
    switch (text[i]) {
      case arrows.sup:
      case arrows.sub:
      case arrows.bold:
        if (should_hide(text[i + 1])) {
          const pos_mid = doc.positionAt(i + 1)
          hide_ranges.push(new Range(doc.positionAt(i), pos_mid));
          (text[i] === arrows.sub ? sub_ranges : (text[i] === arrows.sup ? sup_ranges : bold_ranges))
            .push(new Range(pos_mid, doc.positionAt(i + 2)))
          i++
        }
        break
      case arrows.bsup:
      case arrows.bsub:
        const close = text[i] === arrows.bsub ? arrows.esub : arrows.bsup
        const script_ranges = text[i] === arrows.bsub ? sub_ranges : sup_ranges
        const close_index = find_closing(close, text, i)

        if (close_index && close_index - i > 1) {
          const pos_start = doc.positionAt(i + 1)
          const pos_end = doc.positionAt(close_index)
          hide_ranges.push(
            new Range(doc.positionAt(i), pos_start),
            new Range(pos_end, doc.positionAt(close_index + 1))
          )
          script_ranges.push(new Range(pos_start, pos_end))
          i = close_index
        }
        break
      default:
        break
    }
  }

  return { hide_ranges: hide_ranges, superscript_ranges: sup_ranges, subscript_ranges: sub_ranges, bold_ranges: bold_ranges }
}

export function register_script_decorations(context: ExtensionContext)
{
  const hide = window.createTextEditorDecorationType({
    textDecoration: 'none; font-size: 0.001em',
    rangeBehavior: DecorationRangeBehavior.ClosedClosed
  })

  const superscript = window.createTextEditorDecorationType({
    textDecoration: 'none; position: relative; top: -0.5em; font-size: 80%'
  })

  const subscript = window.createTextEditorDecorationType({
    textDecoration: 'none; position: relative; bottom: -0.5em; font-size: 80%'
  })

  const bold = window.createTextEditorDecorationType({
    textDecoration: 'none; font-weight: bold'
  })

  const set_editor_decorations = (editor: TextEditor, doc: TextDocument) =>
    {
      const { hide_ranges: hideRanges, superscript_ranges: superscriptRanges, subscript_ranges: subscriptRanges, bold_ranges: boldRanges } = extract_ranges(doc)

      editor.setDecorations(hide, hideRanges)
      editor.setDecorations(superscript, superscriptRanges)
      editor.setDecorations(subscript, subscriptRanges)
      editor.setDecorations(bold, boldRanges)
    }

  context.subscriptions.push(
    hide, superscript, subscript, bold,

    window.onDidChangeActiveTextEditor(editor =>
      {
        if (!editor) {
          return
        }

        const doc = editor.document
        set_editor_decorations(editor, doc)
      }),

    workspace.onDidChangeTextDocument(({ document}) =>
      {
        for (const editor of window.visibleTextEditors) {
          if (editor.document.uri.toString() === document.uri.toString()) {
            set_editor_decorations(editor, document)
          }
        }
      })
  )
}
