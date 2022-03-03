/*  Author:     Denis Paluca and Fabian Huch, TU Muenchen

Persistent workspace state.
*/

'use strict';

import { ExtensionContext } from 'vscode'
import { Session_Theories } from '../lsp'
import * as symbol from '../symbol'

interface Setup_Data
{
  workspace_dir: string
  sessions: Session_Theories[]
  symbol_entries: symbol.Entry[]
}

enum State_Key
{
  workspace_dir = 'workspace_dir',
  sessions = 'sessions',
  symbol_entries = 'symbol_entries'
}

class Workspace_State
{
  constructor(private context: ExtensionContext) { }

  public get_setup_data(): Setup_Data
  {
    return {
      workspace_dir: this.get(State_Key.workspace_dir),
      sessions: this.get<Session_Theories[]>(State_Key.sessions),
      symbol_entries: this.get<symbol.Entry[]>(State_Key.symbol_entries)
    }
  }

  public set_setup_date(setup_data: Setup_Data)
  {
    const {workspace_dir: workspace_dir, sessions } = setup_data
    this.set(State_Key.workspace_dir, workspace_dir) // TODO await?
    this.set(State_Key.sessions, sessions) // TODO await?
  }

  public get<T = string>(key: State_Key): T
  {
    return this.context.workspaceState.get(key)
  }

  public async set(key: State_Key, value: any)
  {
    await this.context.workspaceState.update(key, value)
  }
}

export { Workspace_State, State_Key, Setup_Data }
