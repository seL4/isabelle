'use strict';

import { ViewColumn, TextEditor, workspace } from 'vscode'


/* Isabelle configuration */

export function get_configuration<T>(name: string): T
{
  return workspace.getConfiguration("isabelle").get<T>(name)
}

export function get_color(color: string, light: boolean): string
{
  const config = color + (light ? "_light" : "_dark") + "_color"
  return get_configuration<string>(config)
}


/* text editor column */

export function other_column(active_editor: TextEditor | null): ViewColumn
{
  if (!active_editor || active_editor.viewColumn === ViewColumn.Three) return ViewColumn.One
  else if (active_editor.viewColumn === ViewColumn.One) return ViewColumn.Two
  else return ViewColumn.Three
}
