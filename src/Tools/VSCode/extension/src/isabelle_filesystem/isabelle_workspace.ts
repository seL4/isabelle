/*  Author:     Denis Paluca and Fabian Huch, TU Muenchen

Handling of theory files in VSCode workspace.
*/

'use strict';

import * as path from 'path';
import {
  commands,
  ExtensionContext, FileSystemError, languages, TextDocument,
  Uri, ViewColumn,
  window,
  workspace
} from 'vscode';
import * as vscode_lib from '../vscode_lib';
import { Session_Theories } from '../lsp';
import * as symbol from '../symbol';
import { Mapping_FSP } from './mapping_fsp';
import { Symbol_Encoder } from './symbol_encoder';
import { State_Key, Workspace_State } from './workspace_state';

export class Isabelle_Workspace
{
  private static instance: Isabelle_Workspace
  private static state: Workspace_State
  public static readonly draft_session = 'Draft'
  private static readonly session_dir = 'Isabelle Sessions'
  
  private fs: Mapping_FSP
  private session_theories: Session_Theories[] = []

  public static readonly scheme = 'isabelle'
  public static readonly isabelle_lang_id = 'isabelle'
  public static readonly theory_extension = '.thy'
  public static readonly theory_files_glob = '**/*.thy'

  public static register(context: ExtensionContext): Promise<string|undefined>
  {
    this.state = new Workspace_State(context)
    
    const encoder = new Symbol_Encoder(this.state.get(State_Key.symbol_entries) || [])
    this.instance = new Isabelle_Workspace()
    this.instance.fs = new Mapping_FSP(Isabelle_Workspace.theory_files_glob, Isabelle_Workspace.scheme, encoder)

    context.subscriptions.push(
      workspace.registerFileSystemProvider(this.scheme, this.instance.fs),

      workspace.onDidOpenTextDocument((doc) =>
        this.instance.open_workspace_document(doc)),

      window.onDidChangeActiveTextEditor(({ document}) =>
        this.instance.active_document_dialogue(document)),

      this.instance.fs.sync_subscription(),

      commands.registerTextEditorCommand('isabelle.reload-file',
        ({document}) => this.instance.reload(document.uri))
    )

    return this.instance.setup_workspace()
  }

  public get_dir_uri(session: string): Uri
  {
    return Uri.parse(`${Isabelle_Workspace.scheme}:/${session}`)
  }

  public get_uri(session: string, rel_path: String): Uri
  {
    return Uri.parse(`${Isabelle_Workspace.scheme}:/${session}/${rel_path}`)
  }

  public static async update_symbol_encoder(entries: symbol.Entry[])
  {
    this.instance.fs.update_symbol_encoder(new Symbol_Encoder(entries))
    await this.state.set(State_Key.symbol_entries, entries)
  }

  public static async update_sessions(sessions: Session_Theories[])
  {
    await Isabelle_Workspace.state.set(State_Key.sessions, sessions)
    await this.instance.load_tree_state(sessions)
    for (const doc of workspace.textDocuments) {
      await this.instance.open_workspace_document(doc)
    }
    if (window.activeTextEditor) {
      await this.instance.active_document_dialogue(window.activeTextEditor.document)
    }
  }

  public static get_isabelle(file_uri: Uri): Uri
  {
    return this.instance.fs.get_entry(file_uri) || file_uri
  }

  public static get_file(isabelle_uri: Uri): Uri
  {
    return this.instance.fs.get_file(isabelle_uri) || isabelle_uri
  }

  public async open_workspace_document(doc: TextDocument)
  {
    if (doc.uri.scheme === Isabelle_Workspace.scheme) {
      if (doc.languageId !== Isabelle_Workspace.isabelle_lang_id) {
        languages.setTextDocumentLanguage(doc, Isabelle_Workspace.isabelle_lang_id)
      }
    } else {
      if (doc.languageId === Isabelle_Workspace.isabelle_lang_id) {
        const isabelle_uri = this.fs.get_entry(doc.uri)
        if (!isabelle_uri) {
          await this.create_mapping_load_theory(doc.uri)
        } else if (!this.is_open_theory(isabelle_uri)) {
          await this.fs.reload(doc.uri, isabelle_uri)
        }
      }
    }
  }

  public async active_document_dialogue(doc: TextDocument)
  {
    if (doc.uri.scheme === Isabelle_Workspace.scheme) {
      if (!await this.is_workspace_theory(doc.uri)) {
        Isabelle_Workspace.warn_not_synchronized(doc.fileName)
      }
    } else if (doc.fileName.endsWith(Isabelle_Workspace.theory_extension)) {
      const isabelle_uri = this.fs.get_entry(doc.uri)
      if (!isabelle_uri || !this.is_open_theory(isabelle_uri)) {
        await this.open_theory_dialogue(doc.uri)
      }
    }
  }

  public async reload(doc: Uri)
  {
    if (doc.scheme === Isabelle_Workspace.scheme) {
      const file_uri = this.fs.get_file(doc)
      await this.fs.reload(file_uri, doc)
    }
  }

  private async setup_workspace(): Promise<string|undefined>
  {
    const { state } = Isabelle_Workspace
    let { sessions, workspace_dir, symbol_entries } = state.get_setup_data()

    const workspace_folders = workspace.workspaceFolders || []
    const isabelle_folder = workspace_folders.find(folder =>
       folder.name === Isabelle_Workspace.session_dir && folder.uri.scheme === Isabelle_Workspace.scheme)

    if (isabelle_folder === undefined) {
      workspace.updateWorkspaceFolders(0, 0,
        { uri: Isabelle_Workspace.instance.get_dir_uri(''), name: Isabelle_Workspace.session_dir })
    }

    if (sessions && workspace_dir && symbol_entries) {
      await Isabelle_Workspace.update_symbol_encoder(symbol_entries)
      await this.load_tree_state(sessions)
    } else {
      const default_folder = workspace_folders.find(folder => folder.uri.scheme !== Isabelle_Workspace.scheme)
      if (default_folder !== undefined) workspace_dir = default_folder.uri.fsPath
    }

    await state.set(State_Key.workspace_dir, workspace_dir)
    return workspace_dir
  }

  private async load_tree_state(sessions: Session_Theories[])
  {
    const root_entries = this.fs.list_dirs(this.get_dir_uri(''))
    for (const key of root_entries) {
      this.fs.remove(this.get_dir_uri(key))
    }

    for (const { session_name, theories: theories_uri } of sessions) {
      if (!session_name) continue
      if (session_name !== Isabelle_Workspace.draft_session) {
        this.session_theories.push({
          session_name,
          theories: theories_uri.map(t => Uri.parse(t).toString())
        })
      }

      this.fs.make_dir(this.get_dir_uri(session_name))

      for (const theory_uri of theories_uri) {
        await this.create_mapping_load_theory(Uri.parse(theory_uri))
      }
    }
  }

  private is_open_theory(isabelle_uri: Uri): boolean
  {
    const open_files = workspace.textDocuments
    return !!(open_files.find((doc) => doc.uri.toString() === isabelle_uri.toString()))
  }

  private async create_mapping_load_theory(file_uri: Uri): Promise<Uri>
  {
    const session = this.get_session(file_uri)
    const isabelle_uri = this.create_new_uri(file_uri, session)
    await this.fs.load(file_uri, isabelle_uri)
    return isabelle_uri
  }

  private async is_workspace_theory(isabelle_uri: Uri): Promise<boolean>
  {
    const file_uri = this.fs.get_file(isabelle_uri)
    const files = await workspace.findFiles(Isabelle_Workspace.theory_files_glob)
    return !!(files.find(uri => uri.toString() === file_uri.toString()))
  }

  private static warn_not_synchronized(file_name: string)
  {
     window.showWarningMessage(`Theory ${file_name} not in workspace.
      Changes to underlying theory file will be overwritten.`)
  }

  private async open_theory_dialogue(file_uri: Uri)
  {
    const always_open = vscode_lib.get_configuration<boolean>('always_open_thys')
    if (!always_open) {
      const answer = await window.showInformationMessage(
        'Would you like to open the Isabelle theory associated with this file?',
        'Yes',
        'Always yes'
      )
      if (answer === 'Always yes') {
        vscode_lib.set_configuration('always_open_thys', true)
      } else if (answer !== 'Yes') {
        return
      }
    }

    const isabelle_uri = await this.create_mapping_load_theory(file_uri)
    await commands.executeCommand('vscode.open', isabelle_uri, ViewColumn.Active)
  }


  public get_session(file_uri: Uri): string
  {
    let session = this.session_theories.find((s) => s.theories.includes(file_uri.toString()))
    if (!session) {
      this.fs.make_dir(this.get_dir_uri(Isabelle_Workspace.draft_session))
      return Isabelle_Workspace.draft_session
    }

    return session.session_name
  }

  private create_new_uri(file_uri: Uri, session_name: string): Uri
  {
    const file_name = path.basename(file_uri.fsPath, Isabelle_Workspace.theory_extension)
    let new_uri: Uri
    let extra = ''
    let fs_path = file_uri.fsPath
    while (true) {
      const discriminator = extra ? ` (${extra})` : ''
      new_uri = this.get_uri(session_name, file_name + discriminator)

      const old_uri = this.fs.get_file(new_uri)
      if (!old_uri || old_uri.toString() === file_uri.toString()) {
        return new_uri
      }

      if (fs_path === '/') {
        throw FileSystemError.FileExists(new_uri)
      }

      fs_path = path.posix.dirname(fs_path)
      extra = path.posix.join(path.posix.basename(fs_path), extra)
    }
  }
}