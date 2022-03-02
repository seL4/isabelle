/*  Author:     Denis Paluca and Fabian Huch, TU Muenchen

Memory-mapped virtual filesystem with symbol encoding.
*/

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
  private file_to_entry = new Uri_Map()
  private symbol_encoder: Symbol_Encoder
  private readonly scheme: string
  private readonly glob: GlobPattern

  
  constructor(glob: GlobPattern, scheme: string, encoder: Symbol_Encoder) 
  {
    this.glob = glob
    this.scheme = scheme
    this.symbol_encoder = encoder
  }


  public async update_symbol_encoder(encoder: Symbol_Encoder): Promise<void>
  {
    this.symbol_encoder = encoder
    await Promise.all(this.file_to_entry.keys().map(file =>
       this.reload(file, this.file_to_entry.get_to(file))))
  }

  public sync_subscription(): Disposable
  {
    const watcher = workspace.createFileSystemWatcher(this.glob)
    watcher.onDidChange(file => {
      const entry = this.file_to_entry.get_to(file)
      if (entry) this.reload(file, entry)
    })
    watcher.onDidDelete(file => this.remove(this.file_to_entry.get_to(file), true))
    return watcher
  }


  public get_entry(file: Uri): Uri | undefined
  {
    return this.file_to_entry.get_to(file)
  }

  public get_file(entry: Uri): Uri | undefined
  {
    return this.file_to_entry.get_from(entry)
  }


  private get_parent_data(uri: Uri): [Directory, Uri]
  {
    const parent_uri = uri.with({ path: path.posix.dirname(uri.path) })
    const parent = this.lookup_directory(parent_uri, false)

    return [parent, parent_uri]
  }

  private lookup(uri: Uri, silent: false): Entry
  private lookup(uri: Uri, silent: boolean): Entry | undefined
  private lookup(uri: Uri, silent: boolean): Entry | undefined {
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

  private lookup_directory(uri: Uri, silent: boolean): Directory
  {
    const entry = this.lookup(uri, silent)
    if (entry instanceof Directory) {
      return entry
    }
    throw FileSystemError.FileNotADirectory(uri)
  }

  private lookup_file(uri: Uri, silent: boolean): File
  {
    const entry = this.lookup(uri, silent)
    if (entry instanceof File) {
      return entry
    }
    throw FileSystemError.FileIsADirectory(uri)
  }

  public list_dirs(uri: Uri): string[]
  {
    const res: string[] = []
    for (const [name, dir] of this.lookup_directory(uri, false).entries) {
      if (dir instanceof Directory) {
        res.push(dir.name)
      }
    }
    
    return res
  }

  public list_files(uri: Uri): string[]
  {
    const res: string[] = []
    for (const [name, dir] of this.lookup_directory(uri, false).entries) {
      if (dir instanceof File) {
        res.push(dir.name)
      }
    }
    
    return res
  }


  public make_dir(uri: Uri): void
  {
    const basename = path.posix.basename(uri.path)
    const [parent, parent_uri] = this.get_parent_data(uri)

    if (!parent.entries.has(basename)) {
      const entry = new Directory(basename)
      parent.entries.set(entry.name, entry)
      parent.mtime = Date.now()
      parent.size += 1
      this.fire_soon(
        { type: FileChangeType.Changed, uri: parent_uri },
        { type: FileChangeType.Created, uri }
      )
    }
  }


  public async load(file_uri: Uri, isabelle_uri: Uri)
  {
    this.file_to_entry.add(file_uri, isabelle_uri)
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

  private async sync_original(uri: Uri, content: Uint8Array)
  {
    const origin_uri = this.file_to_entry.get_from(uri)
    const decoded_content = this.symbol_encoder.decode(content)
    workspace.fs.writeFile(origin_uri, decoded_content)
  }


  remove(uri: Uri, silent: boolean = false): void
  {
    const dirname = uri.with({ path: path.posix.dirname(uri.path) })
    const basename = path.posix.basename(uri.path)
    const parent = this.lookup_directory(dirname, silent)

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

    this.fire_soon({ type: FileChangeType.Changed, uri: dirname }, { uri, type: FileChangeType.Deleted })
  }

  private sync_deletion(isabelle_uri: Uri, silent: boolean)
  {
    const dir = this.lookup(isabelle_uri, silent)
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


  private buffered_events: FileChangeEvent[] = []
  private fire_soon_handle?: NodeJS.Timer

  private fire_soon(...events: FileChangeEvent[]): void
  {
    this.buffered_events.push(...events)

    if (this.fire_soon_handle) {
      clearTimeout(this.fire_soon_handle)
    }

    this.fire_soon_handle = setTimeout(() => {
      this.emitter.fire(this.buffered_events)
      this.buffered_events.length = 0
    }, 5)
  }

  private emitter = new EventEmitter<FileChangeEvent[]>()


  //#region fsp implementation

  readonly onDidChangeFile: Event<FileChangeEvent[]> = this.emitter.event

  watch(_resource: Uri): Disposable
  {
    return new Disposable(() => { })
  }

  stat(uri: Uri): FileStat
  {
    return this.lookup(uri, false)
  }

  readDirectory(uri: Uri): [string, FileType][]
  {
    const entry = this.lookup_directory(uri, false)
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
    const data = this.lookup_file(uri, false).data
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
    const [parent, parent_uri] = this.get_parent_data(isabelle_uri)
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

      this.fire_soon({ type: FileChangeType.Changed, uri: isabelle_uri })
      return
    }

    entry = new File(basename)
    entry.mtime = Date.now()
    entry.size = content.byteLength
    entry.data = content

    parent.entries.set(basename, entry)
    parent.mtime = Date.now()
    parent.size++
    this.fire_soon(
      { type: FileChangeType.Changed, uri: parent_uri },
      { type: FileChangeType.Created, uri: isabelle_uri }
    )
  }

  delete(uri: Uri): void
  {
    const [parent, parent_uri] = this.get_parent_data(uri)
    if (parent && parent.name === 'Draft') {
      if (parent.size === 1) {
        this.remove(parent_uri)
        return
      }

      this.remove(uri)
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