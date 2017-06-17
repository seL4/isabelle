'use strict'

import { Event, EventEmitter, Uri, TextDocumentContentProvider, Disposable,
  workspace } from 'vscode'


export class Content_Provider implements TextDocumentContentProvider
{
  private _uri_template: Uri
  get uri_template(): Uri { return this._uri_template }
  get uri_scheme(): string { return this.uri_template.scheme }

  constructor(uri_scheme: string)
  {
    this._uri_template = Uri.parse("scheme:").with({ scheme: uri_scheme })
  }
  dispose() { }

  private emitter = new EventEmitter<Uri>()
  public update(uri: Uri) { this.emitter.fire(uri) }
  get onDidChange(): Event<Uri> { return this.emitter.event }

  private content = new Map<string, string>()
  public set_content(uri: Uri, content: string) { this.content.set(uri.toString(), content)}

  provideTextDocumentContent(uri: Uri): string
  {
    return this.content.get(uri.toString()) || ""
  }

  public register(): Disposable
  {
    return workspace.registerTextDocumentContentProvider(this.uri_scheme, this)
  }
}
