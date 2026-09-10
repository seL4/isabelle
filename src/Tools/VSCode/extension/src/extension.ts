/*  Author:     Makarius
    Author:     Denis Paluca, TU Muenchen
    Author:     Fabian Huch, TU Muenchen

Isabelle/VSCode extension.
*/

"use strict";

import { Uri, TextEditor, ViewColumn, Selection, Position, ExtensionContext, workspace, window,
  commands, ProgressLocation, Range, TextEditorRevealType } from "vscode"
import { LanguageClient, LanguageClientOptions, ServerOptions,
  TextDocumentEdit } from "vscode-languageclient/node"
import {OptionalVersionedTextDocumentIdentifier} from "vscode-languageserver-types"

import * as Platform from "./platform"
import * as Library from "./library"
import * as File from "./file"
import * as VSCode_Lib from "./vscode_lib"
import * as Decorations from "./decorations"
import * as Preview_Panel from "./preview_panel"
import * as LSP from "./lsp"
import * as State_Panel from "./state_panel"
import * as Output_View from "./output_view"
import * as Symbols_View from "./symbols_view"
import * as Documentation_Panel from "./documentation_panel"
import * as Sledgehammer_Panel from "./sledgehammer_panel"
import * as Script_Decorations from "./script_decorations"


let last_caret_update: LSP.Caret_Update = {}


/* command-line arguments from "isabelle vscode" */

interface Args {
  options?: string[],
  logic?: string,
  logic_ancestor?: string,
  logic_requirements?: boolean,
  sesion_dirs?: string[],
  include_sessions?: string[],
  modes?: string[],
  log_file?: string,
  verbose?: boolean
}

function print_value(x: any): string {
  return typeof(x) === "string" ? x : JSON.stringify(x)
}

function isabelle_options(args: Args): string[] {
  let result: string[] = []
  function add(s: string) { result.push(s) }
  function add_value(opt: string, slot: string) {
    const x = args[slot]
    if (x) { add(opt); add(print_value(x)) }
  }
  function add_values(opt: string, slot: string) {
    const xs: any[] = args[slot]
    if (xs) { for (const x of xs) { add(opt); add(print_value(x)) } }
  }

  add_value("-A", "logic_ancestor")
  if (args.logic) { add_value(args.logic_requirements ? "-R" : "-l", "logic") }

  add_values("-d", "session_dirs")
  add_values("-i", "include_sessions")
  add_values("-m", "modes")
  add_value("-L", "log_file")
  if (args.verbose) { add("-v") }

  const config = workspace.getConfiguration("isabelle.options")
  Object.keys(config).forEach(key =>
    {
      const value = config[key]
      if (typeof value == "string" && value !== "") {
        add("-o"); add(`${key}=${value}`)
      }
    })
  add_values("-o", "options")

  return result
}


/* activate extension */

export async function activate(context: ExtensionContext) {
  /* server */

  try {
    const isabelle_home = Library.getenv_strict("ISABELLE_HOME")
    const isabelle_tool = isabelle_home + "/bin/isabelle"
    const args = JSON.parse(Library.getenv("ISABELLE_VSCODIUM_ARGS") || "{}")

    const server_opts = isabelle_options(args)
    const server_options: ServerOptions =
      Platform.is_windows() ?
        { command: File.cygwin_bash(),
          args: ["-l", isabelle_tool, "vscode_server"].concat(server_opts) } :
        { command: isabelle_tool,
          args: ["vscode_server"].concat(server_opts) }

    const language_client_options: LanguageClientOptions = {
      documentSelector: [
        { language: "isabelle", scheme: VSCode_Lib.file_scheme },
        { language: "isabelle-ml", scheme: VSCode_Lib.file_scheme },
        { language: "bibtex", scheme: VSCode_Lib.file_scheme }
      ]
    }

    const language_client =
      new LanguageClient("Isabelle", server_options, language_client_options, false)


    window.withProgress({location: ProgressLocation.Notification, cancellable: false},
      async (progress) =>
        {
          progress.report({ message: "Waiting for Isabelle language server..." })
          await language_client.onReady()
        })


    /* decorations */

    Decorations.setup(context)
    context.subscriptions.push(
      workspace.onDidChangeConfiguration(() => Decorations.setup(context)),
      workspace.onDidChangeTextDocument(event => Decorations.touch_document(event.document)),
      window.onDidChangeActiveTextEditor(Decorations.update_editor),
      workspace.onDidCloseTextDocument(Decorations.close_document))

    language_client.onReady().then(() =>
      language_client.onNotification(LSP.decoration_type, Decorations.apply_decoration))


    /* super-/subscript decorations */

    Script_Decorations.register_script_decorations(context)


    /* caret handling */

    function update_caret() {
      const editor = window.activeTextEditor
      let caret_update: LSP.Caret_Update = {}
      if (editor) {
        const uri = editor.document.uri
        const cursor = editor.selection.active
        if (VSCode_Lib.is_file(uri) && cursor)
          caret_update = { uri: uri.toString(), line: cursor.line, character: cursor.character }
      }
      if (last_caret_update !== caret_update) {
        if (caret_update.uri) {
          language_client.sendNotification(LSP.caret_update_type, caret_update)
        }
        last_caret_update = caret_update
      }
    }

    function goto_file(caret_update: LSP.Caret_Update) {
      const pos = new Position(caret_update.line || 0, caret_update.character || 0)

      function show_position(editor: TextEditor) {
        editor.revealRange(new Range(pos, pos), TextEditorRevealType.InCenterIfOutsideViewport)
      }

      function show_file(uri: Uri) {
        workspace.openTextDocument(uri).then(document =>
          {
            const editor = VSCode_Lib.find_file_editor(document.uri)
            const column = editor ? editor.viewColumn : ViewColumn.One
            const options =
              { viewColumn: column,
                preserveFocus: !caret_update.focus,
                selection: new Selection(pos, pos) }
            window.showTextDocument(document, options).then(show_position)
          })
      }

      if (caret_update.uri) {
        const uri = Uri.parse(caret_update.uri)
        workspace.fs.stat(uri).then(
          _ => show_file(uri),
          _ => show_file(uri.with({ scheme: "untitled" })))
      }
    }

    language_client.onReady().then(() =>
      {
        context.subscriptions.push(
          window.onDidChangeActiveTextEditor(update_caret),
          window.onDidChangeTextEditorSelection(update_caret))
        update_caret()

        language_client.onNotification(LSP.caret_update_type, goto_file)
      })


    /* edits */

    async function apply_edit(msg: LSP.Document_Edit) {
      const doc = OptionalVersionedTextDocumentIdentifier.create(msg.uri, msg.version)
      const edit =
        language_client.protocol2CodeConverter.asWorkspaceEdit(
          { documentChanges: [TextDocumentEdit.create(doc, [msg.edit])] })

      workspace.applyEdit(edit).then(() => goto_file({ ...msg, focus: true }))
    }

    language_client.onReady().then(() =>
      { language_client.onNotification(LSP.edit_command_type, apply_edit) })


    /* dynamic output */

    const output_provider = new Output_View.Provider(context.extensionUri, language_client)
    context.subscriptions.push(
      window.registerWebviewViewProvider(Output_View.view_type, output_provider))

    language_client.onReady().then(() =>
      {
        language_client.onNotification(LSP.dynamic_output_type,
          params => output_provider.update_content(params.content))
      })


    /* documentation panel */

    const documentation_provider =
      new Documentation_Panel.Provider(context.extensionUri, language_client)
    context.subscriptions.push(
      window.registerWebviewViewProvider(
        Documentation_Panel.view_type, documentation_provider))

    language_client.onReady().then(() =>
      {
        documentation_provider.request(language_client)
        documentation_provider.setupDocumentation(language_client)
      })


    /* symbols panel */

    const symbols_provider = new Symbols_View.Provider(context.extensionUri, language_client)
    context.subscriptions.push(
      window.registerWebviewViewProvider(Symbols_View.view_type, symbols_provider))

    language_client.onReady().then(() => symbols_provider.setup())


    /* sledgehammer panel */

    const sledgehammer_provider =
      new Sledgehammer_Panel.Provider(context.extensionUri, language_client)
    context.subscriptions.push(
      window.registerWebviewViewProvider(Sledgehammer_Panel.view_type, sledgehammer_provider))

    language_client.onReady().then(() => sledgehammer_provider.setup())


    /* state panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.state", uri => State_Panel.init(uri)))

    language_client.onReady().then(() => State_Panel.setup(context, language_client))


    /* preview panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.preview", uri => Preview_Panel.request(uri, false)),
      commands.registerCommand("isabelle.preview-split", uri => Preview_Panel.request(uri, true)))

    language_client.onReady().then(() => Preview_Panel.setup(context, language_client))


    /* spell checker */

    language_client.onReady().then(() =>
      {
        context.subscriptions.push(
          commands.registerCommand("isabelle.include-word", _uri =>
            language_client.sendNotification(LSP.include_word_type)),
          commands.registerCommand("isabelle.include-word-permanently", _uri =>
            language_client.sendNotification(LSP.include_word_permanently_type)),
          commands.registerCommand("isabelle.exclude-word", _uri =>
            language_client.sendNotification(LSP.exclude_word_type)),
          commands.registerCommand("isabelle.exclude-word-permanently", _uri =>
            language_client.sendNotification(LSP.exclude_word_permanently_type)),
          commands.registerCommand("isabelle.reset-words", _uri =>
            language_client.sendNotification(LSP.reset_words_type)))
      })


    /* start server */

    context.subscriptions.push(language_client.start())
  }
  catch (exn) { window.showErrorMessage(exn) }
}


export function deactivate() { }
