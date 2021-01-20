'use strict';

import * as library from './library'
import { Disposable, DocumentSelector, ExtensionContext, extensions, window } from 'vscode'


/* ASCII characters */

export type Symbol = string

export function is_char(s: Symbol): boolean
{ return s.length == 1 }

export function is_ascii_letter(s: Symbol): boolean
{ return is_char(s) && "A" <= s && s <= "Z" || "a" <= s && s <= "z" }

export function is_ascii_digit(s: Symbol): boolean
{ return is_char(s) && "0" <= s && s <= "9" }

export function is_ascii_quasi(s: Symbol): boolean
{ return s == "_" || s == "'" }

export function is_ascii_letdig(s: Symbol): boolean
{ return is_ascii_letter(s) || is_ascii_digit(s) || is_ascii_quasi(s) }

export function is_ascii_identifier(s: Symbol): boolean
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

function update_entries(entries: [Entry])
{
  symbol_entries = entries
  names.clear
  codes.clear
  for (const entry of entries) {
    names.set(entry.symbol, entry.name)
    codes.set(entry.symbol, entry.code)
  }
}


/* prettify symbols mode */

interface PrettyStyleProperties
{
  border?: string
  textDecoration?: string
  color?: string
  backgroundColor?: string
}

interface PrettyStyle extends PrettyStyleProperties
{
  dark?: PrettyStyleProperties
  light?: PrettyStyleProperties
}

interface Substitution
{
  ugly: string
  pretty: string
  pre?: string
  post?: string
  style?: PrettyStyle
}

interface LanguageEntry
{
  language: DocumentSelector
  substitutions: Substitution[]
}

interface PrettifySymbolsMode
{
  onDidEnabledChange: (handler: (enabled: boolean) => void) => Disposable
  isEnabled: () => boolean,
  registerSubstitutions: (substitutions: LanguageEntry) => Disposable
}

export function setup(context: ExtensionContext, entries: [Entry])
{
  update_entries(entries)

  const prettify_symbols_mode =
    extensions.getExtension<PrettifySymbolsMode>("siegebell.prettify-symbols-mode")
  if (prettify_symbols_mode) {
    prettify_symbols_mode.activate().then(() =>
    {
      const substitutions: Substitution[] = []
      for (const entry of names) {
        const sym = entry[0]
        substitutions.push(
          {
            ugly: library.escape_regex(sym),
            pretty: library.escape_regex(get_unicode(sym))
          })
      }
      for (const language of ["isabelle", "isabelle-ml", "isabelle-output"]) {
        context.subscriptions.push(
          prettify_symbols_mode.exports.registerSubstitutions(
            {
              language: language,
              substitutions: substitutions
            }))
      }
    })
  }
  else {
    window.showWarningMessage("Please install extension \"Prettify Symbols Model\" and restart!")
  }
}