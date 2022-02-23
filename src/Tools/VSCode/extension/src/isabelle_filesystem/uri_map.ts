'use strict';

import {Uri} from 'vscode';

export class Uri_Map
{
  private map = new Map<string, Uri>()
  private rev_map = new Map<string, Uri>()

  private static normalize(uri: Uri): Uri
  {
    return Uri.parse(uri.toString())
  }

  public keys(): Uri[]
  {
    return [...this.rev_map.values()]
  }

  public add(from: Uri, to: Uri)
  {
    const norm_from = Uri_Map.normalize(from)
    const norm_to = Uri_Map.normalize(to)
    this.map.set(norm_from.toString(), norm_to)
    this.rev_map.set(norm_to.toString(), norm_from)
  }

  public delete(from: Uri, to: Uri)
  {
    this.map.delete(Uri_Map.normalize(from).toString())
    this.rev_map.delete(Uri_Map.normalize(to).toString())
  }

  public get_to(from: Uri): Uri
  {
    return this.map.get(Uri_Map.normalize(from).toString())
  }

  public get_from(to: Uri): Uri
  {
    return this.rev_map.get(Uri_Map.normalize(to).toString())
  }
}