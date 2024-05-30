/*  Author:     Makarius

Message formats for Language Server Protocol, with adhoc PIDE extensions
(see Tools/VSCode/src/lsp.scala).
*/

'use strict';

import { MarkdownString } from 'vscode'
import { NotificationType, RequestType0 } from 'vscode-languageclient'


/* decorations */

export interface Decoration_Options {
  range: number[],
  hover_message?: MarkdownString | MarkdownString[]
}

export interface Decoration
{
  "type": string
  content: Decoration_Options[]
}

export interface Document_Decorations {
  uri: string
  entries: Decoration[]
}

export const decoration_type =
  new NotificationType<Document_Decorations>("PIDE/decoration")


/* caret handling */

export interface Caret_Update
{
  uri?: string
  line?: number
  character?: number
  focus?: boolean
}

export const caret_update_type =
  new NotificationType<Caret_Update>("PIDE/caret_update")


/* dynamic output */

export interface Dynamic_Output
{
  content: string
}

export const dynamic_output_type =
  new NotificationType<Dynamic_Output>("PIDE/dynamic_output")

export interface Output_Set_Margin
{
  margin: number
}

export const output_set_margin_type =
  new NotificationType<Output_Set_Margin>("PIDE/output_set_margin")

/* state */

export interface State_Output
{
  id: number
  content: string
  auto_update: boolean
}

export const state_output_type =
  new NotificationType<State_Output>("PIDE/state_output")

export interface State_Set_Margin
{
  id: number
  margin: number
}

export const state_set_margin_type =
  new NotificationType<State_Set_Margin>("PIDE/state_set_margin")

export interface State_Id
{
  id: number
}

export interface Auto_Update
{
  id: number
  enabled: boolean
}

export const state_init_type = new RequestType0("PIDE/state_init")
export const state_exit_type = new NotificationType<State_Id>("PIDE/state_exit")
export const state_locate_type = new NotificationType<State_Id>("PIDE/state_locate")
export const state_update_type = new NotificationType<State_Id>("PIDE/state_update")
export const state_auto_update_type =
  new NotificationType<Auto_Update>("PIDE/state_auto_update")


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
  new NotificationType<Preview_Request>("PIDE/preview_request")

export const preview_response_type =
  new NotificationType<Preview_Response>("PIDE/preview_response")


/* spell checker */

export const include_word_type =
  new NotificationType<void>("PIDE/include_word")

export const include_word_permanently_type =
  new NotificationType<void>("PIDE/include_word_permanently")

export const exclude_word_type =
  new NotificationType<void>("PIDE/exclude_word")

export const exclude_word_permanently_type =
  new NotificationType<void>("PIDE/exclude_word_permanently")

export const reset_words_type =
  new NotificationType<void>("PIDE/reset_words")
