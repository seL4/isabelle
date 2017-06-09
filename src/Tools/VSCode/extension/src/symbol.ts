'use strict';

export type Symbol = string

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