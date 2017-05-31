'use strict';

import * as path from 'path';
import * as fs from 'fs';
import * as library from './library'
import * as decorations from './decorations';
import * as preview from './preview';
import * as protocol from './protocol';
import { ExtensionContext, workspace, window, commands } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions, TransportKind, NotificationType }
  from 'vscode-languageclient';


let last_caret_update: protocol.Caret_Update = {}

export function activate(context: ExtensionContext)
{
  const isabelle_home = library.get_configuration<string>("home")
  const isabelle_args = library.get_configuration<Array<string>>("args")
  const cygwin_root = library.get_configuration<string>("cygwin_root")


  /* server */

  if (isabelle_home === "")
    window.showErrorMessage("Missing user settings: isabelle.home")
  else {
    const isabelle_tool = isabelle_home + "/bin/isabelle"
    const standard_args = ["-o", "vscode_unicode_symbols", "-o", "vscode_pide_extensions"]

    const server_options: ServerOptions =
      library.platform_is_windows() ?
        { command:
            (cygwin_root === "" ? path.join(isabelle_home, "contrib", "cygwin") : cygwin_root) +
            "/bin/bash",
          args: ["-l", isabelle_tool, "vscode_server"].concat(standard_args, isabelle_args) } :
        { command: isabelle_tool,
          args: ["vscode_server"].concat(standard_args, isabelle_args) };
    const language_client_options: LanguageClientOptions = {
      documentSelector: ["isabelle", "isabelle-ml", "bibtex"]
    };

    const language_client =
      new LanguageClient("Isabelle", server_options, language_client_options, false)


    /* decorations */

    decorations.init(context)
    context.subscriptions.push(
      workspace.onDidChangeConfiguration(() => decorations.init(context)),
      workspace.onDidChangeTextDocument(event => decorations.touch_document(event.document)),
      window.onDidChangeActiveTextEditor(decorations.update_editor),
      workspace.onDidCloseTextDocument(decorations.close_document))

    language_client.onReady().then(() =>
      language_client.onNotification(protocol.decoration_type, decorations.apply_decoration))


    /* caret handling */

    function update_caret()
    {
      const editor = window.activeTextEditor
      let caret_update: protocol.Caret_Update = {}
      if (editor) {
        const uri = editor.document.uri
        const cursor = editor.selection.active
        if (library.is_file(uri) && cursor)
          caret_update = { uri: uri.toString(), line: cursor.line, character: cursor.character }
      }
      if (last_caret_update !== caret_update) {
        if (caret_update.uri)
          language_client.sendNotification(protocol.caret_update_type, caret_update)
        last_caret_update = caret_update
      }
    }

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        window.onDidChangeActiveTextEditor(_ => update_caret()),
        window.onDidChangeTextEditorSelection(_ => update_caret()))
      update_caret()
    })


    /* dynamic output */

    const dynamic_output = window.createOutputChannel("Isabelle Output")
    context.subscriptions.push(dynamic_output)
    dynamic_output.show(true)
    dynamic_output.hide()

    language_client.onReady().then(() =>
    {
      language_client.onNotification(protocol.dynamic_output_type,
        params => { dynamic_output.clear(); dynamic_output.appendLine(params.content) })
    })


    /* preview */

    context.subscriptions.push(
      commands.registerCommand("isabelle.preview", uri => preview.request(uri, false)),
      commands.registerCommand("isabelle.preview-split", uri => preview.request(uri, true)),
      commands.registerCommand("isabelle.preview-source", preview.source),
      commands.registerCommand("isabelle.preview-update", preview.update))

    language_client.onReady().then(() => preview.init(context, language_client))


    /* start server */

    context.subscriptions.push(language_client.start())
  }
}

export function deactivate() { }
