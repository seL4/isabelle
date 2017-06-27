'use strict';

import * as library from './library'
import * as protocol from './protocol'
import { Content_Provider } from './content_provider'
import { LanguageClient } from 'vscode-languageclient';
import { Uri, ExtensionContext, workspace, commands, window } from 'vscode'


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

  language_client = client
  language_client.onNotification(protocol.state_output_type, params =>
    {
      const uri = encode_state(params.id)
      if (uri) {
        content_provider.set_content(uri, params.content)
        content_provider.update(uri)

        const existing_document =
          workspace.textDocuments.find(document =>
            document.uri.scheme === uri.scheme &&
            document.uri.fragment === uri.fragment)
        if (!existing_document) {
          const column = library.adjacent_editor_column(window.activeTextEditor, true)
          commands.executeCommand("vscode.previewHtml", uri, column, "State")
        }
      }
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

export function locate(id: number)
{
  if (language_client) language_client.sendNotification(protocol.state_locate_type, { id: id })
}

export function update(id: number)
{
  if (language_client) language_client.sendNotification(protocol.state_update_type, { id: id })
}
