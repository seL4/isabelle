/*  Author:     Denis Paluca, TU Muenchen

Input abbreviation and autocompletion of Isabelle symbols.
*/

'use strict';

import { ExtensionContext, Range, TextDocumentContentChangeEvent, workspace, WorkspaceEdit } from 'vscode'
import { Prefix_Tree } from './prefix_tree'
import * as library from './library'
import * as vscode_lib from './vscode_lib'
import * as symbol from './symbol'

const entries: Record<string, string> = {}
const prefix_tree: Prefix_Tree = new Prefix_Tree()

function register_abbreviations(data: symbol.Entry[], context: ExtensionContext)
{
  const [min_length, max_length] = set_abbrevs(data)
  const alphanumeric_regex = /[^A-Za-z0-9 ]/
  context.subscriptions.push(
    workspace.onDidChangeTextDocument(e =>
    {
      const doc = e.document
      const mode = vscode_lib.get_replacement_mode()
      if (
        mode === 'none' ||
        doc.languageId !== 'isabelle' ||
        doc.uri.scheme !== 'isabelle'
      ) { return; }
      const edits = new WorkspaceEdit()

      const changes = e.contentChanges.slice(0)
      changes.sort((c1, c2) => c1.rangeOffset - c2.rangeOffset)

      let c: TextDocumentContentChangeEvent
      while (c = changes.pop()) {
        if (c.rangeLength === 1 || library.has_newline(c.text)) {
          return
        }

        const end_offset = c.rangeOffset + c.text.length +
          changes.reduce((a,b) => a + b.text.length, 0)

        if (end_offset < min_length) {
          continue
        }

        const start_offset = end_offset < max_length ? 0 : end_offset - max_length

        const end_pos = doc.positionAt(end_offset)
        let start_pos = doc.positionAt(start_offset)
        let range = new Range(start_pos, end_pos)
        const text = library.reverse(doc.getText(range))

        const node = prefix_tree.get_end_or_value(text)
        if (!node || !node.value) {
          continue
        }

        const word = node.get_word().join('')
        if (mode === 'non-alphanumeric' && !alphanumeric_regex.test(word)) {
          continue
        }

        start_pos = doc.positionAt(end_offset - word.length)
        range = new Range(start_pos, end_pos)

        edits.replace(doc.uri, range, node.value as string)
      }

      apply_edits(edits)
    })
  )
}

async function apply_edits(edit: WorkspaceEdit)
{
  await waitForNextTick()
  await workspace.applyEdit(edit)
}

function waitForNextTick(): Promise<void> {
  return new Promise((res) => setTimeout(res, 0));
}

function get_unique_abbrevs(data: symbol.Entry[]): Set<string>
{
  const unique = new Set<string>()
  const non_unique = new Set<string>()
  for (const {code, abbrevs} of data) {
    for (const abbrev of abbrevs) {
      if (abbrev.length === 1 || non_unique.has(abbrev)) {
        continue
      }

      if (unique.has(abbrev)) {
        non_unique.add(abbrev)
        unique.delete(abbrev)
        entries[abbrev] = undefined
        continue
      }


      entries[abbrev] = String.fromCharCode(code)
      unique.add(abbrev)
    }
  }
  return unique
}

function set_abbrevs(data: symbol.Entry[]): [number, number]
{
  const unique = get_unique_abbrevs(data)

  // Add white space to abbrevs which are prefix of other abbrevs
  for (const a1 of unique) {
    for (const a2 of unique) {
      if (a1 === a2) {
        continue
      }

      if (a2.startsWith(a1)) {
        const val = entries[a1]
        delete entries[a1]
        entries[a1 + ' '] = val
        break
      }
    }
  }

  let min_length: number
  let max_length: number
  for (const entry in entries) {
    if (!min_length || min_length > entry.length)
      min_length = entry.length

    if (!max_length || max_length< entry.length)
      max_length = entry.length

    // add reverse because we check the abbrevs from the end
    prefix_tree.insert(library.reverse(entry), entries[entry])
  }

  return [min_length, max_length]
}

export { register_abbreviations }
