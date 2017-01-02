'use strict';

import * as vscode from 'vscode';
import * as path from 'path';

import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions, TransportKind }
  from 'vscode-languageclient';


export function activate(context: vscode.ExtensionContext)
{
  let isabelle_home = vscode.workspace.getConfiguration("isabelle").get<string>("home");
  let isabelle_args = vscode.workspace.getConfiguration("isabelle").get<Array<string>>("args");

  let run = {
    command: path.join(isabelle_home, "bin", "isabelle"),
    args: ["vscode_server"].concat(isabelle_args)
  };
  let server_options: ServerOptions =
  {
    run: run,
    debug: {
      command: run.command,
      args: run.args.concat(["-L", path.join(context.extensionPath, "protocol.log")]) }
  };
  let client_options: LanguageClientOptions = {
    documentSelector: ["isabelle", "isabelle-ml"]
  };

  let disposable = new LanguageClient("Isabelle", server_options, client_options, false).start();
  context.subscriptions.push(disposable);
}

export function deactivate() { }
