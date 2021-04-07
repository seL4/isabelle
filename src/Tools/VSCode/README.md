# Isabelle/PIDE for Visual Studio Code editor #

## Debug ##

* shell> `code src/Tools/VSCode/extension`

* Preferences / User settings / edit settings.json: e.g.
    `"isabelle.home": "/home/makarius/isabelle/repos"`

* View / Debug / Launch Extension

* File / Open Folder: e.g. `src/HOL/Examples/` then open .thy files


## Build ##

* shell> `isabelle build_vscode`

* Extensions / ... / Install from VSIX: `src/Tools/VSCode/extension/isabelle-X.Y.Z.vsix`
