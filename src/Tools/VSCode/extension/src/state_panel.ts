'use strict';

import * as library from './library'
import * as protocol from './protocol'
import { Content_Provider } from './content_provider'
import { LanguageClient, VersionedTextDocumentIdentifier } from 'vscode-languageclient';
import { Uri, ExtensionContext, workspace, commands, window, Webview, WebviewPanel, ViewColumn } from 'vscode'
import { create } from 'domain';


let language_client: LanguageClient

class Panel
{
  private state_id: number
  private webview_panel: WebviewPanel

  public get_id(): number { return this.state_id}
  public check_id(id: number): boolean { return this.state_id == id }

  public set_content(id: number, html: string)
  {
    this.state_id = id
    this.webview_panel.webview.html = html
  }

  constructor(column: ViewColumn)
  {
    this.webview_panel =
      window.createWebviewPanel("isabelle-state", "State", column,
        {
          enableScripts: true,
          enableCommandUris: true,
          retainContextWhenHidden: true,
        });
    this.webview_panel.onDidDispose(exit_panel)
  }

  public locate()
  {
    language_client.sendNotification(protocol.state_locate_type, { id: this.state_id })
  }

  public update()
  {
    language_client.sendNotification(protocol.state_update_type, { id: this.state_id })
  }

  public auto_update(enabled: boolean)
  {
    language_client.sendNotification(
    protocol.state_auto_update_type, { id: this.state_id, enabled: enabled })
  }
}


/* global panel */

let panel: Panel

function check_panel(id: number): boolean
{
  return panel && panel.check_id(id)
}

function exit_panel()
{
  if (panel) {
    language_client.sendNotification(protocol.state_exit_type, { id: panel.get_id() })
    panel = null
  }
}

export function setup(context: ExtensionContext, client: LanguageClient)
{
  language_client = client
  language_client.onNotification(protocol.state_output_type, params =>
    {
      if (!panel) {
        const column = library.adjacent_editor_column(window.activeTextEditor, true)
        panel = new Panel(column)
      }
      panel.set_content(params.id, params.content)
    })
}


/* commands */

export function init(uri: Uri) {
  language_client.sendNotification(protocol.state_init_type)
}

export function locate(id: number) { if (check_panel(id)) panel.locate() }

export function update(id: number) { if (check_panel(id)) panel.update() }

export function auto_update(id: number, enabled: boolean)
{
  if (check_panel(id)) { panel.auto_update(enabled) }
}
