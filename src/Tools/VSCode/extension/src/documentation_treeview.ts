/*  Author:     Fabian Huch

Isabelle documentation as a tree view.
*/

"use strict";

import { EventEmitter, TreeDataProvider, TreeItem, TreeItemCollapsibleState, Uri,
  window, workspace, commands } from "vscode"
import { LanguageClient } from "vscode-languageclient/node"

import * as LSP from "./lsp"


export const view_type = "isabelle-documentation"
export const open_document_command = "isabelle.open-documentation"

interface Node {
  name?: string
  path?: string
  title: string
  important?: boolean
  children: Node[]
}

export class Provider implements TreeDataProvider<Node> {
  private _nodes: Node[] = []
  private readonly _changed = new EventEmitter<void>()

  readonly onDidChangeTreeData = this._changed.event;

  public setup(language_client: LanguageClient) {
    language_client.onNotification(LSP.documentation_response_type, msg =>
      this.update_nodes(msg.sections))
    language_client.sendNotification(LSP.documentation_request_type)
  }

  private update_nodes(sections: LSP.Doc_Section[]): void {
    function map_entry(entry: LSP.Doc_Entry): Node {
      return {
        name: entry.name,
        path: entry.path,
        title: entry.title,
        children: [],
      }
    }
    function map_section(section: LSP.Doc_Section): Node {
      return {
        title: section.title,
        important: section.important,
        children: section.entries.map(map_entry)
      }
    }
    this._nodes = sections.map(map_section)
    this._changed.fire()
  }

  getChildren(element?: Node): Node[] {
    return element ? element.children : this._nodes
  }

  getTreeItem(element: Node): TreeItem {
    const label = element.name && element.title ? element.name + ":" : ""

    function state(important?: Boolean): TreeItemCollapsibleState {
      if (important == undefined) return TreeItemCollapsibleState.None
      else return important ? TreeItemCollapsibleState.Expanded : TreeItemCollapsibleState.Collapsed
    }

    const item = new TreeItem(label, state(element.important))

    item.id = (element.name ? element.name + (element.title ? ": " : "") : "") + element.title
    item.description = element.name ? (element.title ? element.title : element.name) : element.title

    if (element.path) {
      item.resourceUri = Uri.file(element.path)
      item.command = {
        command: open_document_command,
        title: "Open Documentation",
        arguments: [Uri.file(element.path)]
      }
    }
    else item.tooltip = element.title

    return item
  }

  public async open_document(uri: Uri) {
    if (uri.path.endsWith(".pdf")) await commands.executeCommand("vscode.open", uri)
    else {
      const document = await workspace.openTextDocument(uri)
      await window.showTextDocument(document)
    }
  }
}
