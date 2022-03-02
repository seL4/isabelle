/*  Author:     Makarius

File-system operations (see Pure/General/file.scala)
*/

'use strict';

import * as path from 'path'
import * as fs from 'fs/promises'
import { Buffer } from 'buffer'
import * as platform from './platform'
import * as library from './library'


/* Windows/Cygwin */

export function cygwin_root(): string
{
  if (platform.is_windows) {
    return library.getenv_strict("CYGWIN_ROOT")
  }
  else { return "" }
}

export function cygwin_bash(): string
{
  return cygwin_root() + "\\bin\\bash"
}


/* standard path (Cygwin or Posix) */

function slashes(s: string): string
{
  return s.replace(/\\/g, "/")
}

export function standard_path(platform_path: string): string
{
  if (platform.is_windows()) {
    const backslashes = platform_path.replace(/\//g, "\\")

    const root_pattern = new RegExp(library.escape_regex(cygwin_root()) + "(?:\\\\+|\\z)(.*)", "i")
    const root_match = backslashes.match(root_pattern)

    const drive_pattern = new RegExp("([a-zA-Z]):\\\\*(.*)")
    const drive_match = backslashes.match(drive_pattern)

    if (root_match) {
      const rest = root_match[1]
      return "/" + slashes(rest)
    }
    else if (drive_match) {
      const letter = drive_match[1].toLowerCase()
      const rest = drive_match[2]
      return "/cygdrive/" + letter + (!rest ? "" : "/" + slashes(rest))
    }
    else { return slashes(backslashes) }
  }
  else { return platform_path }
}


export function platform_path(standard_path: string): string
{
  var _result = []
  function result(): string { return _result.join("") }

  function clear(): void { _result = [] }
  function add(s: string): void { _result.push(s) }
  function separator(): void
  {
    const n = _result.length
    if (n > 0 && _result[n - 1] !== path.sep) {
      add(path.sep)
    }
  }


  // check root

  var rest = standard_path
  const is_root = standard_path.startsWith("/")

  if (platform.is_windows) {
    const cygdrive_pattern = new RegExp("/cygdrive/([a-zA-Z])($|/.*)")
    const cygdrive_match = standard_path.match(cygdrive_pattern)

    const named_root_pattern = new RegExp("//+([^/]*)(.*)")
    const named_root_match = standard_path.match(named_root_pattern)

    if (cygdrive_match) {
      const drive = cygdrive_match[1].toUpperCase()
      rest = cygdrive_match[2]
      clear()
      add(drive)
      add(":")
      add(path.sep)
    }
    else if (named_root_match) {
      const root = named_root_match[1]
      rest = named_root_match[2]
      clear()
      add(path.sep)
      add(path.sep)
      add(root)
    }
    else if (is_root) {
      clear()
      add(cygwin_root())
    }
  }
  else if (is_root) {
    clear()
    add(path.sep)
  }


  // check rest

  for (const p of rest.split("/")) {
    if (p) {
      separator()
      add(p)
    }
  }

  return result()
}


/* read */

export async function read_bytes(path: string): Promise<Buffer>
{
    return fs.readFile(path)
}

export async function read(path: string): Promise<string>
{
    return read_bytes(path).then(buffer => buffer.toString())
}

export async function read_json<T>(path: string): Promise<T>
{
    return read(path).then(JSON.parse) as Promise<T>
}
