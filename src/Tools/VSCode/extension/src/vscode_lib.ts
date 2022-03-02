/*  Author:     Makarius

Misc library functions for VSCode.
*/

import {Isabelle_Workspace} from './isabelle_filesystem/isabelle_workspace'
import {TextEditor, Uri, ViewColumn, window, workspace} from 'vscode'


/* files */

export function is_file(uri: Uri): boolean
{
  return uri.scheme === "file" || uri.scheme === Isabelle_Workspace.scheme
}

export function find_file_editor(uri: Uri): TextEditor | undefined
{
  function check(editor: TextEditor): boolean
  { return editor && is_file(editor.document.uri) && editor.document.uri.fsPath === uri.fsPath }

  if (is_file(uri)) {
    if (check(window.activeTextEditor)) return window.activeTextEditor
    else return window.visibleTextEditors.find(check)
  }
  else return undefined
}


/* GUI */

export function adjacent_editor_column(editor: TextEditor, split: boolean): ViewColumn
{
  if (!editor) return ViewColumn.One
  else if (!split) return editor.viewColumn
  else if (editor.viewColumn === ViewColumn.One || editor.viewColumn === ViewColumn.Three)
    return ViewColumn.Two
  else return ViewColumn.Three
}


/* Isabelle configuration */

export function get_configuration<T>(name: string): T
{
  return workspace.getConfiguration("isabelle").get<T>(name)
}

export function set_configuration<T>(name: string, configuration: T)
{
  workspace.getConfiguration("isabelle").update(name, configuration)
}

export function get_replacement_mode()
{
  return get_configuration<"none" | "non-alphanumeric" | "all">("replacement")
}

export function get_color(color: string, light: boolean): string
{
  const colors = get_configuration<object>("text_color")
  return colors[color + (light ? "_light" : "_dark")]
}
