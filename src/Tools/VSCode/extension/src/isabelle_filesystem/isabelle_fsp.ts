'use strict';

import {
  commands,
  Disposable,
  Event,
  EventEmitter,
  ExtensionContext,
  FileChangeEvent,
  FileChangeType,
  FileStat,
  FileSystemError,
  FileSystemProvider,
  FileType,
  languages,
  TextDocument,
  Uri, ViewColumn,
  window,
  workspace
} from 'vscode';
import * as path from 'path';
import {Symbol_Encoder} from './symbol_encoder';
import {Session_Theories, session_theories_request_type} from '../protocol';
import {State_Key, Workspace_State} from './workspace_state';
import * as symbol from '../symbol'
import * as library from '../library';
import {Uri_Map} from './uri_map';

export class File implements FileStat
{
  type: FileType
  ctime: number
  mtime: number
  size: number

  name: string
  data?: Uint8Array

  constructor(name: string)
  {
    this.type = FileType.File
    this.ctime = Date.now()
    this.mtime = Date.now()
    this.size = 0
    this.name = name
  }
}

export class Directory implements FileStat
{
  type: FileType
  ctime: number
  mtime: number
  size: number

  name: string
  entries: Map<string, File | Directory>

  constructor(name: string)
  {
    this.type = FileType.Directory
    this.ctime = Date.now()
    this.mtime = Date.now()
    this.size = 0
    this.name = name
    this.entries = new Map()
  }
}

export type Entry = File | Directory

export class Isabelle_FSP implements FileSystemProvider
{
  private static instance: Isabelle_FSP
  private static state: Workspace_State
  private static readonly draft_session = 'Draft'
  private static readonly session_dir = 'Isabelle Sessions'

  //#region public static API

  public static readonly scheme = 'isabelle'
  public static readonly isabelle_lang_id = 'isabelle'
  public static readonly theory_extension = '.thy'
  public static readonly theory_files_glob = '**/*.thy'

  public static register(context: ExtensionContext): Promise<string|undefined>
  {
    this.instance = new Isabelle_FSP()
    this.state = new Workspace_State(context)
    context.subscriptions.push(
      workspace.registerFileSystemProvider(this.scheme, this.instance),

      workspace.onDidOpenTextDocument((doc) =>
        this.instance.open_workspace_document(doc)),

      window.onDidChangeActiveTextEditor(({ document}) =>
        this.instance.active_document_dialogue(document)),

      this.instance.sync_subscription(),

      commands.registerTextEditorCommand('isabelle.reload-file',
        ({document}) => this.instance.reload_document(document.uri))
    )

    return this.instance.setup_workspace()
  }

  public static async update_symbol_encoder(entries: symbol.Entry[])
  {
    this.instance.symbol_encoder = new Symbol_Encoder(entries)
    await this.state.set(State_Key.symbol_entries, entries)
  }

  public static async init_workspace(sessions: Session_Theories[])
  {
    await this.instance.init_filesystem(sessions)
    for (const doc of workspace.textDocuments) {
      await this.instance.open_workspace_document(doc)
    }
    if (window.activeTextEditor) {
      await this.instance.active_document_dialogue(window.activeTextEditor.document)
    }
  }

  public static get_isabelle(file_uri: Uri): Uri
  {
    return this.instance.file_to_isabelle.get_to(file_uri) || file_uri
  }

  public static get_file(isabelle_uri: Uri): Uri
  {
    return this.instance.file_to_isabelle.get_from(isabelle_uri) || isabelle_uri
  }

  //#endregion


  //#region subscriptions

  public async open_workspace_document(doc: TextDocument)
  {
    if (doc.uri.scheme === Isabelle_FSP.scheme) {
      if (doc.languageId !== Isabelle_FSP.isabelle_lang_id) {
        languages.setTextDocumentLanguage(doc, Isabelle_FSP.isabelle_lang_id)
      }
    } else {
      if (doc.languageId === Isabelle_FSP.isabelle_lang_id) {
        const isabelle_uri = this.file_to_isabelle.get_to(doc.uri)
        if (!isabelle_uri) {
          await this.create_mapping_load_theory(doc.uri)
        } else if (!this.is_open_theory(isabelle_uri)) {
          await this.load_theory(doc.uri, isabelle_uri)
        }
      }
    }
  }

  public async active_document_dialogue(doc: TextDocument)
  {
    if (doc.uri.scheme === Isabelle_FSP.scheme) {
      if (!await this.is_workspace_theory(doc.uri)) {
        Isabelle_FSP.warn_not_synchronized(doc.fileName)
      }
    } else if (doc.fileName.endsWith(Isabelle_FSP.theory_extension)) {
      const isabelle_uri = this.file_to_isabelle.get_to(doc.uri)
      if (!isabelle_uri || !this.is_open_theory(isabelle_uri)) {
        await this.open_theory_dialogue(doc.uri)
      }
    }
  }

  public sync_subscription(): Disposable
  {
    const watcher = workspace.createFileSystemWatcher(Isabelle_FSP.theory_files_glob)
    watcher.onDidChange(file => this.reload_file_theory(file))
    watcher.onDidDelete(file => this._delete(this.file_to_isabelle.get_to(file)))
    return watcher
  }

  public async reload_document(doc: Uri)
  {
    if (doc.scheme === Isabelle_FSP.scheme) {
      const file_uri = this.file_to_isabelle.get_from(doc)
      await this.reload_theory(file_uri, doc)
    }
  }

  public async reload_file_theory(file_uri: Uri)
  {
    const isabelle_uri = this.file_to_isabelle.get_to(file_uri)
    await this.reload_theory(file_uri, isabelle_uri)
  }

  //#endregion


  private symbol_encoder: Symbol_Encoder
  private root = new Directory('')
  private file_to_isabelle = new Uri_Map()
  private session_theories: Session_Theories[] = []


  //#region util

  private static get_dir_uri(session: string): Uri
  {
    return Uri.parse(`${Isabelle_FSP.scheme}:/${session}`)
  }
  private static get_uri(session: string, rel_path: String): Uri
  {
    return Uri.parse(`${Isabelle_FSP.scheme}:/${session}/${rel_path}`)
  }

  //#endregion


  //#region initialization

  private async setup_workspace(): Promise<string|undefined>
  {
    const { state } = Isabelle_FSP
    let { sessions, workspace_dir, symbol_entries } = state.get_setup_data()

    const workspace_folders = workspace.workspaceFolders || []
    const isabelle_folder = workspace_folders.find(folder =>
       folder.name === Isabelle_FSP.session_dir && folder.uri.scheme === Isabelle_FSP.scheme)

    if (isabelle_folder === undefined) {
      workspace.updateWorkspaceFolders(0, 0,
        { uri: Isabelle_FSP.get_dir_uri(''), name: Isabelle_FSP.session_dir })
    }

    if (sessions && workspace_dir && symbol_entries) {
      await Isabelle_FSP.update_symbol_encoder(symbol_entries)
      await this.init_filesystem(sessions)
    } else {
      const default_folder = workspace_folders.find(folder => folder.uri.scheme !== Isabelle_FSP.scheme)
      if (default_folder !== undefined) workspace_dir = default_folder.uri.fsPath
    }

    await state.set(State_Key.workspace_dir, workspace_dir)
    await this.save_tree_state()
    this.onDidChangeFile(events => {
      for (const e of events) {
        if (e.type === FileChangeType.Changed) continue

        this.save_tree_state()
        return
      }
    })
    return workspace_dir
  }

  private async init_filesystem(sessions: Session_Theories[])
  {
    const all_theory_uris = sessions
      .map(s => s.theories)
      .reduce((acc,x) => acc.concat(x), [])

    const root_entries = Array.from(this.root.entries.keys())

    // clean old files
    for (const key of root_entries) {
      if (key === Isabelle_FSP.draft_session) {
        const draft = this.root.entries.get(key)

        if (draft instanceof Directory) {
          for (const draft_thy of draft.entries.keys()) {
            const isabelle_uri = Isabelle_FSP.get_uri(Isabelle_FSP.draft_session, draft_thy)
            const file_uri = this.file_to_isabelle.get_from(isabelle_uri)

            if (file_uri && all_theory_uris.includes(file_uri.toString())) {
              this._delete(isabelle_uri)
            }
          }
        }
      } else {
        this._delete(Isabelle_FSP.get_dir_uri(key), true)
      }
    }

    // create new
    for (const { session_name, theories: theories_uri } of sessions) {
      if (!session_name) continue
      if (session_name !== Isabelle_FSP.draft_session) {
        this.session_theories.push({
          session_name,
          theories: theories_uri.map(t => Uri.parse(t).toString())
        })
      }

      if (!root_entries.includes(session_name)) {
        this._create_directory(Isabelle_FSP.get_dir_uri(session_name))
      }

      for (const theory_uri of theories_uri) {
        await this.create_mapping_load_theory(Uri.parse(theory_uri))
      }
    }
  }

  //#endregion


  //#region fsp implementation

  private _emitter = new EventEmitter<FileChangeEvent[]>()

  readonly onDidChangeFile: Event<FileChangeEvent[]> = this._emitter.event

  watch(_resource: Uri): Disposable
  {
    // ignore, fires for all changes...
    return new Disposable(() => { })
  }

  stat(uri: Uri): FileStat
  {
    return this._lookup(uri, false)
  }

  readDirectory(uri: Uri): [string, FileType][]
  {
    const entry = this._lookup_directory(uri, false)
    const result: [string, FileType][] = []
    for (const [name, child] of entry.entries) {
      result.push([name, child.type])
    }
    return result
  }

  createDirectory(uri: Uri): void
  {
    throw FileSystemError.NoPermissions('No permission to create on Isabelle File System')
  }

  readFile(uri: Uri): Uint8Array
  {
    const data = this._lookup_file(uri, false).data
    if (data) {
      return data
    }
    throw FileSystemError.FileNotFound()
  }

  async writeFile(isabelle_uri: Uri, content: Uint8Array, options: { create: boolean, overwrite: boolean }): Promise<void>
  {
    if (!this.symbol_encoder) return
    if (!this.file_to_isabelle.get_from(isabelle_uri)) {
      throw FileSystemError.NoPermissions('No permission to create on Isabelle File System')
    }

    const basename = path.posix.basename(isabelle_uri.path)
    const [parent, parent_uri] = this._get_parent_data(isabelle_uri)
    let entry = parent.entries.get(basename)
    if (entry instanceof Directory) {
      throw FileSystemError.FileIsADirectory(isabelle_uri)
    }
    if (!entry && !options.create) {
      throw FileSystemError.FileNotFound(isabelle_uri)
    }
    if (entry && options.create && !options.overwrite) {
      throw FileSystemError.FileExists(isabelle_uri)
    }

    if (entry) {
      if (options.create) {
        return this.sync_original(isabelle_uri, content)
      }

      entry.mtime = Date.now()
      entry.size = content.byteLength
      entry.data = content

      this._fire_soon({ type: FileChangeType.Changed, uri: isabelle_uri })
      return
    }

    entry = new File(basename)
    entry.mtime = Date.now()
    entry.size = content.byteLength
    entry.data = content

    parent.entries.set(basename, entry)
    parent.mtime = Date.now()
    parent.size++
    this._fire_soon(
      { type: FileChangeType.Changed, uri: parent_uri },
      { type: FileChangeType.Created, uri: isabelle_uri }
    )
  }

  delete(uri: Uri): void
  {
    const [parent, parent_uri] = this._get_parent_data(uri)
    if (parent && parent.name === Isabelle_FSP.draft_session) {
      if (parent.size === 1) {
        this._delete(parent_uri)
        return
      }

      this._delete(uri)
      return
    }

    throw FileSystemError.NoPermissions('No permission to delete on Isabelle File System')
  }

  rename(oldUri: Uri, newUri: Uri, options: { overwrite: boolean }): void
  {
    throw FileSystemError.NoPermissions('No permission to rename on Isabelle File System')
  }

  //#endregion


  //#region implementation

  private is_open_theory(isabelle_uri: Uri): boolean
  {
    const open_files = workspace.textDocuments
    return !!(open_files.find((doc) => doc.uri.toString() === isabelle_uri.toString()))
  }

  private async load_theory(file_uri: Uri, isabelle_uri: Uri)
  {
    if (!this.symbol_encoder) return
    const data = await workspace.fs.readFile(file_uri)
    const encoded_data = this.symbol_encoder.encode(data)
    await this.writeFile(isabelle_uri, encoded_data, { create: true, overwrite: true })
  }

  private async create_mapping_load_theory(file_uri: Uri): Promise<Uri>
  {
    const session = this.get_session(file_uri)
    const isabelle_uri = this.create_new_uri(file_uri, session)
    this.file_to_isabelle.add(file_uri, isabelle_uri)

    await this.load_theory(file_uri, isabelle_uri)
    return isabelle_uri
  }

  private async is_workspace_theory(isabelle_uri: Uri): Promise<boolean>
  {
    const file_uri = this.file_to_isabelle.get_from(isabelle_uri)
    const files = await workspace.findFiles(Isabelle_FSP.theory_files_glob)
    return !!(files.find(uri => uri.toString() === file_uri.toString()))
  }

  private static warn_not_synchronized(file_name: string)
  {
     window.showWarningMessage(`Theory ${file_name} not in workspace.
      Changes to underlying theory file will be overwritten.`)
  }

  private async open_theory_dialogue(file_uri: Uri)
  {
    if (!this.symbol_encoder) return
    const always_open = library.get_configuration<boolean>('always_open_thys')
    if (!always_open) {
      const answer = await window.showInformationMessage(
        'Would you like to open the Isabelle theory associated with this file?',
        'Yes',
        'Always yes'
      )
      if (answer === 'Always yes') {
        library.set_configuration('always_open_thys', true)
      } else if (answer !== 'Yes') {
        return
      }
    }

    const isabelle_uri = await this.create_mapping_load_theory(file_uri)
    await commands.executeCommand('vscode.open', isabelle_uri, ViewColumn.Active)
  }

  private async reload_theory(file_uri: Uri, isabelle_uri: Uri)
  {
    if (!this.symbol_encoder) return
    const data = await workspace.fs.readFile(file_uri)
    const encoded_data = this.symbol_encoder.encode(data)
    await this.writeFile(isabelle_uri, encoded_data, { create: false, overwrite: true })
  }

  public get_session(file_uri: Uri): string
  {
    let session = this.session_theories.find((s) => s.theories.includes(file_uri.toString()))
    if (!session) {
      if (!this.root.entries.get(Isabelle_FSP.draft_session)) {
        this._create_directory(Isabelle_FSP.get_uri(Isabelle_FSP.draft_session, ''))
      }
      return Isabelle_FSP.draft_session
    }

    return session.session_name
  }

  private create_new_uri(file_uri: Uri, session_name: string): Uri
  {
    const file_name = path.basename(file_uri.fsPath, Isabelle_FSP.theory_extension)
    let new_uri: Uri
    let extra = ''
    let fs_path = file_uri.fsPath
    while (true) {
      const discriminator = extra ? ` (${extra})` : ''
      new_uri = Isabelle_FSP.get_uri(session_name, file_name + discriminator)

      const old_uri = this.file_to_isabelle.get_from(new_uri)
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

  private async save_tree_state()
  {
    const sessions: Session_Theories[] = []
    for (const [session_name, val] of this.root.entries) {
      if (!(val instanceof Directory)) return
      const theories: string[] = []

      for (const fileName of val.entries.keys()) {
        const file = this.file_to_isabelle.get_from(Isabelle_FSP.get_uri(session_name, fileName))
        theories.push(file.toString())
      }

      sessions.push({session_name, theories})
    }

    await Isabelle_FSP.state.set(State_Key.sessions, sessions)
  }

  private sync_deletion(isabelle_uri: Uri, silent: boolean)
  {
    const dir = this._lookup(isabelle_uri, silent)
    if (!dir) {
      if (silent)
        return
      else
        throw FileSystemError.FileNotFound(isabelle_uri)
    }

    const uri_string = isabelle_uri.toString()
    if (dir instanceof Directory) {
      for (const key of dir.entries.keys()) {
        this.remove_mapping(Uri.parse(uri_string + `/${key}`))
      }
    }
    this.remove_mapping(isabelle_uri)
  }

  private remove_mapping(isabelle_uri: Uri)
  {
    const file = this.file_to_isabelle.get_from(isabelle_uri)
    if (file) {
      this.file_to_isabelle.delete(file, isabelle_uri)
    }
  }

  private async sync_original(uri: Uri, content: Uint8Array)
  {
    if (!this.symbol_encoder) return
    const origin_uri = this.file_to_isabelle.get_from(uri)
    const decoded_content = this.symbol_encoder.decode(content)
    workspace.fs.writeFile(origin_uri, decoded_content)
  }

  private _delete(uri: Uri, silent: boolean = false): void
  {
    const dirname = uri.with({ path: path.posix.dirname(uri.path) })
    const basename = path.posix.basename(uri.path)
    const parent = this._lookup_directory(dirname, silent)

    if (!parent) return
    if (!parent.entries.has(basename)) {
      if (!silent)
        throw FileSystemError.FileNotFound(uri)
      else
        return
    }

    this.sync_deletion(uri, silent)
    parent.entries.delete(basename)
    parent.mtime = Date.now()
    parent.size -= 1

    this._fire_soon({ type: FileChangeType.Changed, uri: dirname }, { uri, type: FileChangeType.Deleted })
  }

  private _create_directory(uri: Uri): void
  {
    const basename = path.posix.basename(uri.path)
    const [parent, parent_uri] = this._get_parent_data(uri)

    const entry = new Directory(basename)
    parent.entries.set(entry.name, entry)
    parent.mtime = Date.now()
    parent.size += 1
    this._fire_soon(
      { type: FileChangeType.Changed, uri: parent_uri },
      { type: FileChangeType.Created, uri }
    )
  }

  private _get_parent_data(uri: Uri): [Directory, Uri]
  {
    const parent_uri = uri.with({ path: path.posix.dirname(uri.path) })
    const parent = this._lookup_directory(parent_uri, false)

    return [parent, parent_uri]
  }

  // --- lookup

  private _lookup(uri: Uri, silent: false): Entry
  private _lookup(uri: Uri, silent: boolean): Entry | undefined
  private _lookup(uri: Uri, silent: boolean): Entry | undefined {
    const parts = uri.path.split('/')
    let entry: Entry = this.root
    for (const part of parts) {
      if (!part) {
        continue
      }
      let child: Entry | undefined
      if (entry instanceof Directory) {
        child = entry.entries.get(part)
      }
      if (!child) {
        if (!silent) {
          throw FileSystemError.FileNotFound(uri)
        } else {
          return undefined
        }
      }
      entry = child
    }
    return entry
  }

  private _lookup_directory(uri: Uri, silent: boolean): Directory
  {
    const entry = this._lookup(uri, silent)
    if (entry instanceof Directory) {
      return entry
    }
    throw FileSystemError.FileNotADirectory(uri)
  }

  private _lookup_file(uri: Uri, silent: boolean): File
  {
    const entry = this._lookup(uri, silent)
    if (entry instanceof File) {
      return entry
    }
    throw FileSystemError.FileIsADirectory(uri)
  }

  // --- manage file events

  private _buffered_events: FileChangeEvent[] = []
  private _fire_soon_handle?: NodeJS.Timer

  private _fire_soon(...events: FileChangeEvent[]): void
  {
    this._buffered_events.push(...events)

    if (this._fire_soon_handle) {
      clearTimeout(this._fire_soon_handle)
    }

    this._fire_soon_handle = setTimeout(() => {
      this._emitter.fire(this._buffered_events)
      this._buffered_events.length = 0
    }, 5)
  }
}
