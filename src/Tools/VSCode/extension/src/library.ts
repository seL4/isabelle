/*  Author:     Makarius

Basic library (see Pure/library.scala).
*/

'use strict';

import * as platform from './platform'
import * as path from 'path'


/* regular expressions */

export function escape_regex(s: string): string
{
  return s.replace(/[|\\{}()[\]^$+*?.]/g, "\\$&").replace(/-/g, "\\x2d")
}


/* strings */

export function quote(s: string): string
{
  return "\"" + s + "\""
}

export function reverse(s: string): string
{
  return s.split("").reverse().join("")
}

export function has_newline(text: string)
{
  return text.includes("\n") || text.includes("\r")
}


/* settings environment */

export function getenv(name: string): string
{
  const s = process.env[name]
  return s || ""
}

export function getenv_strict(name: string): string
{
  const s = getenv(name)
  if (s) return s
  else throw new Error("Undefined Isabelle environment variable: " + quote(name))
}


/* system path representations */

export function cygwin_root(): string
{
  if (platform.is_windows) {
    return getenv_strict("CYGWIN_ROOT")
  }
  else { return "" }
}

function slashes(s: string): string
{
  return s.replace(/\\/g, "/")
}

export function standard_path(platform_path: string): string
{
  if (platform.is_windows()) {
    const backslashes = platform_path.replace(/\//g, "\\")

    const root_pattern = new RegExp(escape_regex(cygwin_root()) + "(?:\\\\+|\\z)(.*)", "i")
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
