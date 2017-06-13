'use strict';

import * as os from 'os';
import { TextEditor, Uri, ViewColumn, workspace } from 'vscode'


/* regular expressions */

export function escape_regex(s: string): string
{
  return s.replace(/[|\\{}()[\]^$+*?.]/g, "\\$&")
}


/* platform information */

export function platform_is_windows(): boolean
{
  return os.type().startsWith("Windows")
}


/* file URIs */

export function is_file(uri: Uri): boolean
{
  return uri.scheme === "file"
}


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


/* GUI */

export function adjacent_editor_column(editor: TextEditor, split: boolean): ViewColumn
{
  if (!editor) return ViewColumn.One
  else if (!split) return editor.viewColumn
  else if (editor.viewColumn === ViewColumn.One || editor.viewColumn === ViewColumn.Three)
    return ViewColumn.Two
  else return ViewColumn.Three
}
