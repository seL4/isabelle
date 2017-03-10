'use strict';

import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import * as decorations from './decorations';
import { Decoration } from './decorations'
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions, TransportKind, NotificationType }
  from 'vscode-languageclient';


export function activate(context: vscode.ExtensionContext)
{
  const is_windows = os.type().startsWith("Windows")

  const isabelle_home = vscode.workspace.getConfiguration("isabelle").get<string>("home")
  const isabelle_args = vscode.workspace.getConfiguration("isabelle").get<Array<string>>("args")
  const cygwin_root = vscode.workspace.getConfiguration("isabelle").get<string>("cygwin_root")

  if (isabelle_home === "")
    vscode.window.showErrorMessage("Missing user settings: isabelle.home")
  else {
    const isabelle_tool = isabelle_home + "/bin/isabelle"
    const standard_args = ["-o", "vscode_unicode_symbols", "-o", "vscode_pide_extensions"]

    const server_options: ServerOptions =
      is_windows ?
        { command:
            (cygwin_root === "" ? path.join(isabelle_home, "contrib", "cygwin") : cygwin_root) +
            "/bin/bash",
          args: ["-l", isabelle_tool, "vscode_server"].concat(standard_args, isabelle_args) } :
        { command: isabelle_tool,
          args: ["vscode_server"].concat(standard_args, isabelle_args) };
    const client_options: LanguageClientOptions = {
      documentSelector: ["isabelle", "isabelle-ml", "bibtex"]
    };

    const client = new LanguageClient("Isabelle", server_options, client_options, false)

    decorations.init(context)
    vscode.window.onDidChangeActiveTextEditor(decorations.update_editor)
    vscode.workspace.onDidCloseTextDocument(decorations.close_document)
    client.onReady().then(() =>
      client.onNotification(
        new NotificationType<Decoration, void>("PIDE/decoration"), decorations.apply_decoration))

    context.subscriptions.push(client.start());
  }
}

export function deactivate() { }
