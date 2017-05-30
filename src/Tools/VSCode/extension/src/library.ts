'use strict';

import { ViewColumn, window } from 'vscode'


export function other_column(): ViewColumn
{
  const active = window.activeTextEditor
  if (!active || active.viewColumn === ViewColumn.Three) return ViewColumn.One
  else if (active.viewColumn === ViewColumn.One) return ViewColumn.Two
  else return ViewColumn.Three
}
