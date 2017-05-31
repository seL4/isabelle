'use strict';

import * as os from 'os';
import { TextEditor, Uri, workspace } from 'vscode'


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
