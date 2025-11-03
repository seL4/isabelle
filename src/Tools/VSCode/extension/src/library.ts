/*  Author:     Makarius

Basic library (see Pure/library.scala).
*/

'use strict';

import * as platform from './platform'


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
