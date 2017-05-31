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


/* preview */

export interface Preview_Request
{
  uri: string
  column: number
}

export interface Preview_Response
{
  uri: string
  column: number
  label: string
  content: string
}

export const preview_request_type =
  new NotificationType<Preview_Request, void>("PIDE/preview_request")

export const preview_response_type =
  new NotificationType<Preview_Response, void>("PIDE/preview_response")
