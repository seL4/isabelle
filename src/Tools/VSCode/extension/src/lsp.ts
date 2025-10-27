/*  Author:     Makarius
    Author:     Thomas Lindae, TU Muenchen
    Author:     Diana Korchmar, LMU Muenchen

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


export interface Decoration_Request
{
  uri: string
}

export const decoration_request_type =
  new NotificationType<Decoration_Request>("PIDE/decoration_request")


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
export const state_auto_update_type = new NotificationType<Auto_Update>("PIDE/state_auto_update")


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


/* symbols */

export interface Symbol_Entry {
  name: string;
  abbrevs: string[];
  groups: string[];
  code?: number;
  font?: string;
  symbol: string;
  argument: string;
  decoded: string;
}

export interface Symbols_Response {
  symbols: Symbol_Entry [];
  abbrevs_from_Thy: [string, string][];
}

export const symbols_response_type =
  new NotificationType<Symbols_Response>("PIDE/symbols_response");

export const symbols_request_type =
  new NotificationType<void>("PIDE/symbols_panel_request")


/* documentation */

export const documentation_request_type =
  new NotificationType<void>("PIDE/documentation_request")

export interface Doc_Entry {
  print_html: string;
  platform_path: string;
}

export interface Doc_Section {
  title: string;
  important: boolean;
  entries: Array<Doc_Entry>;
}

export interface Documentation_Response {
  sections: Array<Doc_Section>;
}

export const documentation_response_type =
  new NotificationType<Documentation_Response>("PIDE/documentation_response");


/* Sledgehammer */

export interface SledgehammerApplyRequest {
  provers: string;
  isar: boolean;
  try0: boolean;
  purpose: number;
}

export interface SledgehammerApplyResult {
  content: string;
  position: {
    uri: string;
    line: number;
    character: number;
  };
  sendback_id: number;
  state_location: {
    uri: string;
    line: number;
    character: number;
  };
}

export interface Sledgehammer_Locate {
  position: {
    uri: string;
    line: number;
    character: number;
  };
}

export interface SledgehammerInsertPosition {
  position: {
    uri: string;
    line: number;
    character: number;
  };
}

export interface Sledgehammer_Status {
  message: string;
}

export interface Sledgehammer_Provers {
  provers: string;
}

export const sledgehammer_request_type =
  new NotificationType<SledgehammerApplyRequest>("PIDE/sledgehammer_request");

export const sledgehammer_cancel_type =
  new NotificationType<void>("PIDE/sledgehammer_cancel");

export const sledgehammer_provers_request_type =
  new NotificationType<void>("PIDE/sledgehammer_provers_request");

export const sledgehammer_provers_response_type =
  new NotificationType<Sledgehammer_Provers>("PIDE/sledgehammer_provers_response");

export const sledgehammer_status_response_type =
  new NotificationType<Sledgehammer_Status>("PIDE/sledgehammer_status_response");

export const sledgehammer_apply_response_type =
  new NotificationType<SledgehammerApplyResult>("PIDE/sledgehammer_apply_response");

export const sledgehammer_locate_response_type =
  new NotificationType<Sledgehammer_Locate>("PIDE/sledgehammer_locate_response");

export const sledgehammer_insert_position_response_type =
  new NotificationType<SledgehammerInsertPosition>("PIDE/sledgehammer_insert_position_response");

export const sledgehammer_no_proof_response_type =
  new NotificationType<void>("PIDE/sledgehammer_no_proof_resonse");


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
