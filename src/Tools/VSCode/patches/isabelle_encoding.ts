/*  Author:     Makarius

UTF-8-Isabelle symbol encoding: for use inside VSCode.
*/

'use strict';


/* VSCode interfaces */

export interface Options {
  stripBOM?: boolean;
  addBOM?: boolean;
  defaultEncoding?: string;
}

export interface IDecoderStream {
  write(input: Uint8Array): string;
  end(): string | undefined;
}

export interface IEncoderStream {
  write(input: string): Uint8Array;
  end(): Uint8Array | undefined;
}


/* ASCII characters */

function is_ascii(c: number): boolean {
  return 0 <= c && c <= 127;
}

function is_ascii_letter(c: number): boolean {
  return 65 <= c && c <= 90 || 97 <= c && c <= 122;
}

function is_ascii_digit(c: number): boolean {
  return 48 <= c && c <= 57;
}

function is_ascii_quasi(c: number): boolean {
  return c === 95 || c === 39;
}

function is_ascii_letdig(c: number): boolean {
  return is_ascii_letter(c) || is_ascii_digit(c) || is_ascii_quasi(c);
}


/* string buffer */

class String_Buffer {
  state: string[]

  constructor() {
    this.state = [];
  }

  add(s: string) {
    this.state.push(s);
  }

  end(): string {
    const s = this.state.join('');
    this.state = [];
    return s;
  }
}


/* Isabelle symbol codes */

function codepoint_string(c: number): string {
  return String.fromCodePoint(c);
}

const backslash: number = 92;
const caret: number = 94;
const bg_symbol: number = 60;
const en_symbol: number = 62;

interface Symbol_Code {
  symbol: string;
  code: number;
}

export class Symbol_Codes {
  decode_table: Map<string, string>;
  encode_table: Map<string, string>;

  constructor(symbols: Symbol_Code[]) {
    this.decode_table = new Map(symbols.map(s => [s.symbol, codepoint_string(s.code)]));
    this.encode_table = new Map(symbols.map(s => [codepoint_string(s.code), s.symbol]));
  }

  recode(str: string, do_encode: boolean): string {
    function ok(i: number): boolean {
      return 0 <= i && i < str.length;
    }
    function char(i: number): number {
      return ok(i) ? str.charCodeAt(i) : 0;
    }
    function maybe_char(c: number, i: number): number {
      return char(i) === c ? i + 1 : i;
    }

    function many_ascii_letdig(i: number): number {
      let k = i;
      while (is_ascii_letdig(char(k))) { k += 1 };
      return k;
    }
    function maybe_ascii_id(i: number): number {
      return is_ascii_letter(char(i)) ? many_ascii_letdig(i + 1) : i
    }

    function scan_ascii(start: number): string {
      let i = start;
      while (ok(i)) {
        const a = char(i);
        const b = char(i + 1);
        if (!is_ascii(a) || a === backslash && b === bg_symbol) { break; }
        else { i += 1; }
      }
      return str.substring(start, i);
    }

    function scan_symbol(i: number): string {
      const a = char(i);
      const b = char(i + 1);
      if (a === backslash && b === bg_symbol) {
        const j = maybe_char(en_symbol, maybe_ascii_id(maybe_char(caret, i + 2)));
        return str.substring(i, j);
      }
      else { return ''; }
    }

    function scan_codepoint(i: number): string {
      const c = str.codePointAt(i);
      return c === undefined ? '' : codepoint_string(c);
    }


    const table = do_encode ? this.encode_table : this.decode_table;
    const result = new String_Buffer();
    let i = 0;
    while (ok(i)) {
      const ascii = scan_ascii(i)
      if (ascii) {
        result.add(ascii)
        i += ascii.length
      }
      else {
        const s = scan_symbol(i) || scan_codepoint(i);
        if (s) {
          const r = table.get(s);
          result.add(r === undefined ? s : r);
          i += s.length;
        }
      }
    }
    return result.end();
  }
}

const symbol_codes: Symbol_Codes = new Symbol_Codes([/*symbols*/]);


/* main API */

export const ENCODING = 'utf8isabelle';
export const LABEL = 'UTF-8-Isabelle';

export function getDecoder(): IDecoderStream {
  const utf8_decoder = new TextDecoder();
  const buffer = new String_Buffer();
  return {
    write(input: Uint8Array): string {
      buffer.add(utf8_decoder.decode(input, { stream: true }));
      return '';
    },
    end(): string | undefined {
      buffer.add(utf8_decoder.decode());
      const s = buffer.end();
      return symbol_codes.recode(s, false);
    }
  };
}

export function getEncoder(): IEncoderStream {
  const utf8_encoder = new TextEncoder();
  const empty = new Uint8Array(0);
  const buffer = new String_Buffer();
  return {
    write(input: string): Uint8Array {
      buffer.add(input);
      return empty;
    },
    end(): Uint8Array | undefined {
      const s = buffer.end();
      return utf8_encoder.encode(symbol_codes.recode(s, true));
    }
  }
}
