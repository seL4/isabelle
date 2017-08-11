'use strict';

import * as path from 'path';
import * as fs from 'fs';
import * as library from './library'
import * as decorations from './decorations';
import * as preview_panel from './preview_panel';
import * as protocol from './protocol';
import * as state_panel from './state_panel';
import * as symbol from './symbol';
import * as completion from './completion';
import { Uri, TextEditor, ViewColumn, Selection, Position, ExtensionContext, workspace, window,
  commands, languages } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions, TransportKind,
  NotificationType } from 'vscode-languageclient';


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

    decorations.setup(context)
    context.subscriptions.push(
      workspace.onDidChangeConfiguration(() => decorations.setup(context)),
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

    function goto_file(caret_update: protocol.Caret_Update)
    {
      function move_cursor(editor: TextEditor)
      {
        const pos = new Position(caret_update.line || 0, caret_update.character || 0)
        editor.selections = [new Selection(pos, pos)]
      }

      if (caret_update.uri) {
        workspace.openTextDocument(Uri.parse(caret_update.uri)).then(document =>
        {
          const editor = library.find_file_editor(document.uri)
          const column = editor ? editor.viewColumn : ViewColumn.One
          window.showTextDocument(document, column, !caret_update.focus).then(move_cursor)
        })
      }
    }

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        window.onDidChangeActiveTextEditor(_ => update_caret()),
        window.onDidChangeTextEditorSelection(_ => update_caret()))
      update_caret()

      language_client.onNotification(protocol.caret_update_type, goto_file)
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


    /* state panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.state", uri => state_panel.init(uri)),
      commands.registerCommand("_isabelle.state-locate", state_panel.locate),
      commands.registerCommand("_isabelle.state-update", state_panel.update),
      commands.registerCommand("_isabelle.state-auto-update", state_panel.auto_update),
      workspace.onDidCloseTextDocument(document => state_panel.exit_uri(document.uri)))

    language_client.onReady().then(() => state_panel.setup(context, language_client))


    /* preview panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.preview", uri => preview_panel.request(uri, false)),
      commands.registerCommand("isabelle.preview-split", uri => preview_panel.request(uri, true)),
      commands.registerCommand("isabelle.preview-source", preview_panel.source),
      commands.registerCommand("isabelle.preview-update", preview_panel.update))

    language_client.onReady().then(() => preview_panel.setup(context, language_client))


    /* Isabelle symbols */

    language_client.onReady().then(() =>
    {
      language_client.onNotification(protocol.symbols_type,
        params => symbol.setup(context, params.entries))
      language_client.sendNotification(protocol.symbols_request_type)
    })


    /* completion */

    const completion_provider = new completion.Completion_Provider
    for (const mode of ["isabelle", "isabelle-ml"]) {
      context.subscriptions.push(
        languages.registerCompletionItemProvider(mode, completion_provider))
    }


    /* spell checker */

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        commands.registerCommand("isabelle.include-word", uri =>
          language_client.sendNotification(protocol.include_word_type)),
        commands.registerCommand("isabelle.include-word-permanently", uri =>
          language_client.sendNotification(protocol.include_word_permanently_type)),
        commands.registerCommand("isabelle.exclude-word", uri =>
          language_client.sendNotification(protocol.exclude_word_type)),
        commands.registerCommand("isabelle.exclude-word-permanently", uri =>
          language_client.sendNotification(protocol.exclude_word_permanently_type)),
        commands.registerCommand("isabelle.reset-words", uri =>
          language_client.sendNotification(protocol.reset_words_type)))
    })


    /* start server */

    context.subscriptions.push(language_client.start())
  }
}

export function deactivate() { }
