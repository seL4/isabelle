'use strict';

export type Symbol = string


/* ASCII characters */

export function is_char(s: string): boolean
{ return s.length == 1 }

export function is_ascii_letter(s: string): boolean
{ return is_char(s) && "A" <= s && s <= "Z" || "a" <= s && s <= "z" }

export function is_ascii_digit(s: string): boolean
{ return is_char(s) && "0" <= s && s <= "9" }

export function is_ascii_quasi(s: string): boolean
{ return s == "_" || s == "'" }

export function is_ascii_letdig(s: string): boolean
{ return is_ascii_letter(s) || is_ascii_digit(s) || is_ascii_quasi(s) }

export function is_ascii_identifier(s: String): boolean
{
  const n = s.length

  let all_letdig = true
  for (const c of s) { all_letdig = all_letdig && is_ascii_letdig(c) }

  return n > 0 && is_ascii_letter(s.charAt(0)) && all_letdig
}


/* named symbols */

export interface Entry
{
  symbol: Symbol,
  name: string,
  code: number
}

let symbol_entries: [Entry]
const names = new Map<Symbol, string>()
const codes = new Map<Symbol, number>()

export function get_name(sym: Symbol): string | undefined
{
  return names.get(sym)
}

export function get_code(sym: Symbol): number | undefined
{
  return codes.get(sym)
}

export function get_unicode(sym: Symbol): string
{
  const code = get_code(sym)
  return code ? String.fromCharCode(code) : ""
}

export function update(entries: [Entry])
{
  symbol_entries = entries
  names.clear
  codes.clear
  for (const entry of entries) {
    names.set(entry.symbol, entry.name)
    codes.set(entry.symbol, entry.code)
  }
}


/* completion */

export function complete_name(prefix: string): [string]
{
  let result = [] as [string]
  for (const entry of names) {
    if (entry[1].startsWith(prefix)) { result.push(entry[0]) }
  }
  return result.sort()
}