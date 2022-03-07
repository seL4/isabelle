/*  Author:     Makarius

UTF-8-Isabelle symbol encoding: minimal dependencies, for use inside VSCode.
*/

'use strict';

import * as fs from 'fs'
import { TextEncoder, TextDecoder } from 'util'


/* defined symbols */

export interface Symbol_Entry
{
  symbol: string,
  name: string,
  code: number,
  abbrevs: string[]
}

const symbols_file = process.env["ISABELLE_VSCODE_SYMBOLS"]

export const symbols: [Symbol_Entry] =
  symbols_file ? JSON.parse(fs.readFileSync(symbols_file).toString()) : []

export const symbols_decode: Map<string, string> =
  new Map(symbols.map((s: Symbol_Entry) => [s.symbol, String.fromCharCode(s.code)]))

export const symbols_encode: Map<string, string> =
  new Map(symbols.map((s: Symbol_Entry) => [String.fromCharCode(s.code), s.symbol]))


/* encoding */

export const UTF8_Isabelle = 'utf8-isabelle'

export interface Options {
  stripBOM?: boolean;
  addBOM?: boolean;
  defaultEncoding?: string;
}

export interface EncoderStream {
  write(str: string): Uint8Array
  end(): Uint8Array | undefined
}

export interface DecoderStream {
  write(buf: Uint8Array): string
  end(): string | undefined
}

export function getEncoder(encoding: string, options?: Options): EncoderStream
{
  const utf8_encoder = new TextEncoder
  return null
}

export function getDecoder(encoding: string, options?: Options): DecoderStream
{
  const utf8_decoder = new TextDecoder
  return null
}
