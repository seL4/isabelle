'use strict';

import * as vscode from 'vscode';
import * as path from 'path';
import * as os from 'os';
import * as decorations from './decorations';
import { Decoration } from './decorations'
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions, TransportKind }
  from 'vscode-languageclient';


export function activate(context: vscode.ExtensionContext)
{
  let is_windows = os.type().startsWith("Windows")

  let cygwin_root = vscode.workspace.getConfiguration("isabelle").get<string>("cygwin_root");
  let isabelle_home = vscode.workspace.getConfiguration("isabelle").get<string>("home");
  let isabelle_args = vscode.workspace.getConfiguration("isabelle").get<Array<string>>("args");

  if (is_windows && cygwin_root == "")
    vscode.window.showErrorMessage("Missing user settings: isabelle.cygwin_root")
  else if (isabelle_home == "")
    vscode.window.showErrorMessage("Missing user settings: isabelle.home")
  else {
    let isabelle_tool = isabelle_home.concat("/bin/isabelle")
    let standard_args = ["-o", "vscode_unicode_symbols"]
    let run =
      is_windows ?
        { command: cygwin_root.concat("/bin/bash"),
          args: ["-l", isabelle_tool, "vscode_server"].concat(standard_args, isabelle_args) } :
        { command: isabelle_tool,
          args: ["vscode_server"].concat(standard_args, isabelle_args) };

    let server_options: ServerOptions = { run: run, debug: run };
    let client_options: LanguageClientOptions = {
      documentSelector: ["isabelle", "isabelle-ml", "bibtex"]
    };

    let client = new LanguageClient("Isabelle", server_options, client_options, false)

    decorations.init(context)
    client.onNotification<Decoration>({method: "PIDE/decoration"},
      function (decoration: Decoration) { return decorations.apply(decoration) })

    context.subscriptions.push(client.start());
  }
}

export function deactivate() { }
