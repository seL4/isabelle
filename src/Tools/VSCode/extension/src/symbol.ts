/*  Author:     Makarius

Isabelle text symbols versus UTF-8/Unicode encoding. See also:

  - Pure/General/symbol.scala
  - Pure/General/utf8.scala
  - https://encoding.spec.whatwg.org
*/

'use strict';

import * as file from './file'
import * as library from './library'


/* ASCII characters */

export type Symbol = string

export function is_char(s: Symbol): boolean
{ return s.length === 1 }

export function is_ascii_letter(s: Symbol): boolean
{ return is_char(s) && "A" <= s && s <= "Z" || "a" <= s && s <= "z" }

export function is_ascii_digit(s: Symbol): boolean
{ return is_char(s) && "0" <= s && s <= "9" }

export function is_ascii_quasi(s: Symbol): boolean
{ return s === "_" || s === "'" }

export function is_ascii_letdig(s: Symbol): boolean
{ return is_ascii_letter(s) || is_ascii_digit(s) || is_ascii_quasi(s) }

export function is_ascii_identifier(s: Symbol): boolean
{
  const n = s.length

  let all_letdig = true
  for (const c of s) { all_letdig = all_letdig && is_ascii_letdig(c) }

  return n > 0 && is_ascii_letter(s.charAt(0)) && all_letdig
}


/* defined symbols */

export interface Entry {
  symbol: string;
  name: string;
  decoded: string;
  argument: string;
  abbrevs: string[];
  groups: string[];
  code?: number;
}

export class Symbols
{
  entries: Entry[]
  private entries_map: Map<Symbol, Entry>

  constructor(entries: Entry[])
  {
    this.entries = entries
    this.entries_map = new Map<Symbol, Entry>()
    for (const entry of entries) {
      this.entries_map.set(entry.symbol, entry)
    }
  }

  public get(sym: Symbol): Entry | undefined
  {
    return this.entries_map.get(sym)
  }

  public defined(sym: Symbol): boolean
  {
    return this.entries_map.has(sym)
  }
}

function load_symbols(): Entry[]
{
  const vscodium_resources = library.getenv("ISABELLE_VSCODIUM_RESOURCES")
  if (vscodium_resources) {
    const path = vscodium_resources + "/vscodium/out/vs/base/browser/ui/fonts/symbols.json"
    return file.read_json_sync(file.platform_path(path))
  }
  else { return [] }
}

export const symbols: Symbols = new Symbols(load_symbols())


/* control symbols */

export interface Control {
  sub: Entry,
  sup: Entry,
  bold: Entry,
  emph: Entry,
  bsub: Entry,
  esub: Entry,
  bsup: Entry,
  esup: Entry
}

export const control: Control = {
  sub: symbols.get("\\<^sub>"),
  sup: symbols.get("\\<^sup>"),
  bold: symbols.get("\\<^bold>"),
  emph: symbols.get("\\<^emph>"),
  bsub: symbols.get("\\<^bsub>"),
  esub: symbols.get("\\<^esub>"),
  bsup: symbols.get("\\<^bsup>"),
  esup: symbols.get("\\<^esup>")
}
