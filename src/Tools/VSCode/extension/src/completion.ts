'use strict';

import { CompletionItemProvider, CompletionItem, TextDocument, Range, Position,
  CancellationToken, CompletionList } from 'vscode'

export class Completion_Provider implements CompletionItemProvider
{
  public provideCompletionItems(
    document: TextDocument, position: Position, token: CancellationToken): CompletionList
  {
    const line_text = document.lineAt(position).text

    return new CompletionList([])
  }
}
