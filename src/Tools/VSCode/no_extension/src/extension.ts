'use strict';

import { ExtensionContext, window } from 'vscode'

export function activate(context: ExtensionContext)
{
  window.showErrorMessage("Obsolete extension: use bundled Isabelle/VSCode from the Isabelle distribution")
}

export function deactivate() { }
