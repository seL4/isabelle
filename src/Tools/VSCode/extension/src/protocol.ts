'use strict';

import { Position, Range, MarkedString, DecorationOptions, DecorationRenderOptions } from 'vscode'
import { NotificationType } from 'vscode-languageclient';


/* decorations */

export interface DecorationOpts {
  range: number[],
  hover_message?: MarkedString | MarkedString[]
}

export interface Decoration
{
  uri: string,
  "type": string,
  content: DecorationOpts[]
}

export const decoration_type =
  new NotificationType<Decoration, void>("PIDE/decoration")


/* caret handling */

export interface Caret_Update
{
  uri?: string
  line?: number
  character?: number
}

export const caret_update_type =
  new NotificationType<Caret_Update, void>("PIDE/caret_update")


/* dynamic output */

export interface Dynamic_Output
{
  content: string
}

export const dynamic_output_type =
  new NotificationType<Dynamic_Output, void>("PIDE/dynamic_output")


/* dynamic preview */

export interface Dynamic_Preview
{
  content: string
}

export const dynamic_preview_type =
  new NotificationType<Dynamic_Preview, void>("PIDE/dynamic_preview")
