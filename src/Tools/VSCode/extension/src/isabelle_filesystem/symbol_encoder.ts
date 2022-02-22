'use strict';

import { TextEncoder } from 'util'
import * as symbol from '../symbol'
import { Prefix_Tree, Tree_Node } from './prefix_tree'

class Encode_Data
{
  prefix_tree: Prefix_Tree
  min_length: number
  max_length: number

  constructor(origin: Uint8Array[], replacement: Uint8Array[])
  {
    this.prefix_tree = new Prefix_Tree()

    for (let i = 0; i < origin.length; i++) {
      const entry = origin[i]
      if (!this.min_length || this.min_length > entry.length)
        this.min_length = entry.length

      if (!this.max_length || this.max_length< entry.length)
        this.max_length = entry.length

      this.prefix_tree.insert(Array.from(entry), Array.from(replacement[i]))
    }
  }
}

export class Symbol_Encoder
{
  private symbols: Encode_Data
  private sequences: Encode_Data

  constructor(entries: symbol.Entry[])
  {
    let syms: Uint8Array[] = []
    let seqs: Uint8Array[] = []
    const encoder = new TextEncoder()
    for (const {symbol, code} of entries) {
      seqs.push(encoder.encode(symbol))
      syms.push(encoder.encode(String.fromCharCode(code)))
    }
    this.symbols = new Encode_Data(syms, seqs)
    this.sequences = new Encode_Data(seqs, syms)
  }

  encode(content: Uint8Array): Uint8Array
  {
    return this.code(content, this.sequences, this.symbols)
  }

  decode(content: Uint8Array): Uint8Array
  {
    return this.code(content, this.symbols, this.sequences)
  }

  private code(content: Uint8Array, origin: Encode_Data, replacements: Encode_Data): Uint8Array
  {
    const result: number[] = []

    for (let i = 0; i < content.length; i++) {
      if (i > content.length - origin.min_length) {
        result.push(content[i])
        continue
      }

      let word: number[] = []
      let node: Tree_Node
      for (let j = i; j < i + origin.max_length; j++) {
        word.push(content[j])
        node = origin.prefix_tree.get_node(word)
        if (!node || node.end) {
          break
        }
      }

      if (node && node.end) {
        result.push(...(node.value as number[]))
        i += word.length - 1
        continue
      }
      result.push(content[i])
    }

    return new Uint8Array(result)
  }
}
