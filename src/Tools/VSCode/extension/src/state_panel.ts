'use strict';

import * as library from './library'
import * as protocol from './protocol'
import { Content_Provider } from './content_provider'
import { LanguageClient, VersionedTextDocumentIdentifier } from 'vscode-languageclient';
import { Uri, ExtensionContext, workspace, commands, window, Webview, WebviewPanel } from 'vscode'


/* HTML content */

const content_provider = new Content_Provider("isabelle-state")

function encode_state(id: number | undefined): Uri | undefined
{
  return id ? content_provider.uri_template.with({ fragment: id.toString() }) : undefined
}

function decode_state(uri: Uri | undefined): number | undefined
{
  if (uri && uri.scheme === content_provider.uri_scheme) {
    const id = parseInt(uri.fragment)
    return id ? id : undefined
  }
  else undefined
}


/* setup */

let language_client: LanguageClient

export function setup(context: ExtensionContext, client: LanguageClient)
{
  context.subscriptions.push(content_provider.register())

  var panel: WebviewPanel
  language_client = client
  language_client.onNotification(protocol.state_output_type, params =>
    {
      const uri = encode_state(params.id)
      if (!panel) {
        const column = library.adjacent_editor_column(window.activeTextEditor, true)
        panel = window.createWebviewPanel(
          uri.fsPath,
          "State",
          column,
          {
            enableScripts: true,
            retainContextWhenHidden: true
          }
        );
      }
      panel.webview.html = params.content;
    })
}


/* commands */

export function init(uri: Uri)
{
  if (language_client) language_client.sendNotification(protocol.state_init_type)
}

export function exit(id: number)
{
  if (language_client) language_client.sendNotification(protocol.state_exit_type, { id: id })
}

export function exit_uri(uri: Uri)
{
  const id = decode_state(uri)
  if (id) exit(id)
}

export function locate(id: number)
{
  if (language_client) language_client.sendNotification(protocol.state_locate_type, { id: id })
}

export function update(id: number)
{
  if (language_client) language_client.sendNotification(protocol.state_update_type, { id: id })
}

export function auto_update(id: number, enabled: boolean)
{
  if (language_client)
    language_client.sendNotification(protocol.state_auto_update_type, { id: id, enabled: enabled })
}
