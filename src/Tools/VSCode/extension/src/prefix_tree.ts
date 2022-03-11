/*  Author:     Denis Paluca, TU Muenchen

Prefix tree for symbol autocompletion.
*/

'use strict';

class Tree_Node
{
  public key: number | string
  public parent: Tree_Node = null
  public end: boolean = false
  public value: number[] | string
  public children: Record<number | string, Tree_Node> = {}
  constructor(key: number | string)
  {
    this.key = key
  }

  public get_word(): number[] | string[]
  {
    let output = []
    let node: Tree_Node = this

    while (node.key !== null) {
      output.unshift(node.key)
      node = node.parent
    }

    return output
  }
}

class Prefix_Tree
{
  private root: Tree_Node

  constructor()
  {
    this.root = new Tree_Node(null)
  }

  public insert(word: number[] | string, value: number[] | string)
  {
    let node = this.root
    for (var i = 0; i < word.length; i++) {
      if (!node.children[word[i]]) {
        node.children[word[i]] = new Tree_Node(word[i])

        node.children[word[i]].parent = node
      }

      node = node.children[word[i]]
      node.end = false

      if (i === word.length-1) {
        node.end = true
        node.value = value
      }
    }
  }

  public get_node(prefix: number[] | string): Tree_Node | undefined
  {
    let node = this.root

    for (let i = 0; i < prefix.length; i++) {
      if (!node.children[prefix[i]]) {
        return
      }
      node = node.children[prefix[i]]
    }
    return node
  }

  public get_end_or_value(prefix: number[] | string): Tree_Node | undefined
  {
    let node = this.root
    let resNode: Tree_Node
    for (let i = 0; i < prefix.length; i++) {
      if (!node.children[prefix[i]]) {
        return resNode
      }
      node = node.children[prefix[i]]
      if (node.value) {
        resNode = node
      }

      if (node.end) {
        return node
      }
    }
    return node
  }
}

export { Prefix_Tree, Tree_Node }
