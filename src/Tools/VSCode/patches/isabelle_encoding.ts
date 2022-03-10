/*  Author:     Makarius

UTF-8-Isabelle symbol encoding: for use inside VSCode.
*/

'use strict';


/* defined symbols */

export interface Symbol_Code {
  symbol: string;
  code: number;
}

export const static_symbols: Symbol_Code[] = [/*symbols*/];

export const symbols_decode: Map<string, string> =
  new Map(static_symbols.map((s: Symbol_Code) => [s.symbol, String.fromCharCode(s.code)]));

export const symbols_encode: Map<string, string> =
  new Map(static_symbols.map((s: Symbol_Code) => [String.fromCharCode(s.code), s.symbol]));


/* encoding */

export const ENCODING = 'utf8isabelle';
export const LABEL = 'UTF-8-Isabelle';

export interface Options {
  stripBOM?: boolean;
  addBOM?: boolean;
  defaultEncoding?: string;
}

export interface IEncoderStream {
  write(input: string): Uint8Array;
  end(): Uint8Array | undefined;
}

export interface IDecoderStream {
  write(input: Uint8Array): string;
  end(): string | undefined;
}

export function getEncoder(): IEncoderStream {
  const utf8_encoder = new TextEncoder();
  return {
    write(input: string): Uint8Array {
      return utf8_encoder.encode(input);
    },
    end(): Uint8Array | undefined {
      return utf8_encoder.encode();
    }
  };
}

export function getDecoder(): IDecoderStream {
  const utf8TextDecoder = new TextDecoder();
  return {
    write(input: Uint8Array): string {
      return utf8TextDecoder.decode(input, { stream: true });
    },
    end(): string | undefined {
      return utf8TextDecoder.decode();
    }
  };
}
