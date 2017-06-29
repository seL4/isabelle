'use strict';

import { Position, Range, MarkedString, DecorationOptions, DecorationRenderOptions } from 'vscode'
import { NotificationType } from 'vscode-languageclient';
import * as symbol from './symbol'


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
  focus?: boolean
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


/* state */

export interface State_Output
{
  id: number
  content: string
}

export const state_output_type =
  new NotificationType<State_Output, void>("PIDE/state_output")

export interface State_Id
{
  id: number
}

export interface Auto_Update
{
  id: number
  enabled: boolean
}

export const state_init_type = new NotificationType<void, void>("PIDE/state_init")
export const state_exit_type = new NotificationType<State_Id, void>("PIDE/state_exit")
export const state_locate_type = new NotificationType<State_Id, void>("PIDE/state_locate")
export const state_update_type = new NotificationType<State_Id, void>("PIDE/state_update")
export const state_auto_update_type =
  new NotificationType<Auto_Update, void>("PIDE/state_auto_update")


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


/* Isabelle symbols */

export interface Symbols
{
  entries: [symbol.Entry]
}

export const symbols_type =
  new NotificationType<Symbols, void>("PIDE/symbols")

export const symbols_request_type =
  new NotificationType<void, void>("PIDE/symbols_request")


/* spell checker */

export const include_word_type =
  new NotificationType<void, void>("PIDE/include_word")

export const include_word_permanently_type =
  new NotificationType<void, void>("PIDE/include_word_permanently")

export const exclude_word_type =
  new NotificationType<void, void>("PIDE/exclude_word")

export const exclude_word_permanently_type =
  new NotificationType<void, void>("PIDE/exclude_word_permanently")

export const reset_words_type =
  new NotificationType<void, void>("PIDE/reset_words")
