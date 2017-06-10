'use strict';

import * as symbol from './symbol'
import { CompletionItemProvider, CompletionItem, TextDocument, Range, Position,
  CancellationToken, CompletionList } from 'vscode'

export class Completion_Provider implements CompletionItemProvider
{
  public provideCompletionItems(
    document: TextDocument, position: Position, token: CancellationToken): CompletionList
  {
    const line_text = document.lineAt(position).text

    let i = position.character
    while (i > 0 && line_text.charAt(i - 1) !== "\\") { i = i - 1 }
    const start = i - 1

    let result = undefined as CompletionList
    if (start >= 0 && line_text.charAt(start) == "\\") {
      const s = line_text.substring(start + 1, position.character)
      if (symbol.is_ascii_identifier(s)) {
        const items =
          symbol.complete_name(s).map((sym) =>
          {
            return {
              label: sym,
              detail: `(symbol ${symbol.get_unicode(sym)})`,
              range: new Range(new Position(position.line, start), position)
            }
          })
        result = new CompletionList(items)
      }
    }
    return result
  }
}
