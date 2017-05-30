'use strict';

import { ViewColumn, TextEditor } from 'vscode'


export function other_column(active_editor: TextEditor | null): ViewColumn
{
  if (!active_editor || active_editor.viewColumn === ViewColumn.Three) return ViewColumn.One
  else if (active_editor.viewColumn === ViewColumn.One) return ViewColumn.Two
  else return ViewColumn.Three
}
