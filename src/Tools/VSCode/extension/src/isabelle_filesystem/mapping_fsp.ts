'use strict';

import * as path from 'path';
import {
  Disposable,
  Event,
  EventEmitter, FileChangeEvent,
  FileChangeType,
  FileStat,
  FileSystemError,
  FileSystemProvider,
  FileType, GlobPattern, Uri, workspace
} from 'vscode';
import { Session_Theories } from '../protocol';
import { Symbol_Encoder } from './symbol_encoder';
import { Uri_Map } from './uri_map';


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


export class Mapping_FSP implements FileSystemProvider
{
  private root = new Directory('')
  file_to_entry = new Uri_Map()
  private symbol_encoder: Symbol_Encoder
  private readonly scheme: string
  private readonly glob: GlobPattern

  constructor(glob: GlobPattern, scheme: string, encoder: Symbol_Encoder) 
  {
    this.scheme = scheme
    this.symbol_encoder = encoder
  }

  public update_symbol_encoder(encoder: Symbol_Encoder)
  {
    this.symbol_encoder = encoder
  }

  public sync_subscription(): Disposable
  {
    const watcher = workspace.createFileSystemWatcher(this.glob)
    watcher.onDidChange(file => {
      const entry = this.file_to_entry.get_to(file)
      if (entry) this.reload(file, entry)
    })
    watcher.onDidDelete(file => this._delete(this.file_to_entry.get_to(file)))
    return watcher
  }

  private async sync_original(uri: Uri, content: Uint8Array)
  {
    const origin_uri = this.file_to_entry.get_from(uri)
    const decoded_content = this.symbol_encoder.decode(content)
    workspace.fs.writeFile(origin_uri, decoded_content)
  }

  public get_dir_uri(session: string): Uri
  {
    return Uri.parse(`${this.scheme}:/${session}`)
  }

  public get_uri(session: string, rel_path: String): Uri
  {
    return Uri.parse(`${this.scheme}:/${session}/${rel_path}`)
  }
  

  // #region create
  
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

  public make_dir(name: string)
  {
    const root_entries = Array.from(this.root.entries.keys())

    if (!root_entries.includes(name)) {
      this._create_directory(this.get_dir_uri(name))
    }
  }

  // #endregion


  // #region read

  public async load(file_uri: Uri, isabelle_uri: Uri)
  {
    const data = await workspace.fs.readFile(file_uri)
    const encoded_data = this.symbol_encoder.encode(data)
    await this.writeFile(isabelle_uri, encoded_data, { create: true, overwrite: true })
  }

  public async reload(file_uri: Uri, isabelle_uri: Uri)
  {
    const data = await workspace.fs.readFile(file_uri)
    const encoded_data = this.symbol_encoder.encode(data)
    await this.writeFile(isabelle_uri, encoded_data, { create: false, overwrite: true })
  }

  // #endregion


  // #region delete

  _delete(uri: Uri, silent: boolean = false): void
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
    const file = this.file_to_entry.get_from(isabelle_uri)
    if (file) {
      this.file_to_entry.delete(file, isabelle_uri)
    }
  }

  public clear(all_theory_uris: string[])
  {
    const root_entries = Array.from(this.root.entries.keys())

    for (const key of root_entries) {
      if (key === 'Draft') {
        const draft = this.root.entries.get(key)

        if (draft instanceof Directory) {
          for (const draft_thy of draft.entries.keys()) {
            const isabelle_uri = this.get_uri('Draft', draft_thy)
            const file_uri = this.file_to_entry.get_from(isabelle_uri)

            if (file_uri && all_theory_uris.includes(file_uri.toString())) {
              this._delete(isabelle_uri)
            }
          }
        }
      } else {
        this._delete(this.get_dir_uri(key), true)
      }
    }
  }

  // #endregion

  private _get_parent_data(uri: Uri): [Directory, Uri]
  {
    const parent_uri = uri.with({ path: path.posix.dirname(uri.path) })
    const parent = this._lookup_directory(parent_uri, false)

    return [parent, parent_uri]
  }

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

  public get_tree_state(): Session_Theories[]
  {
    const sessions: Session_Theories[] = []
    for (const [session_name, val] of this.root.entries) {
      if (!(val instanceof Directory)) return
      const theories: string[] = []

      for (const fileName of val.entries.keys()) {
        const file = this.file_to_entry.get_from(this.get_uri(session_name, fileName))
        theories.push(file.toString())
      }

      sessions.push({session_name, theories})
    }
    return sessions
  }


  //#region events

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

  private _emitter = new EventEmitter<FileChangeEvent[]>()

  //#endregion


  //#region fsp implementation

  readonly onDidChangeFile: Event<FileChangeEvent[]> = this._emitter.event

  watch(_resource: Uri): Disposable
  {
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
    if (!this.file_to_entry.get_from(isabelle_uri)) {
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
    if (parent && parent.name === 'Draft') {
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
  // #endregion
}