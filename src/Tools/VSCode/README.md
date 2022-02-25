# Isabelle/VSCode development #

## System setup ##

* install default node.js (e.g. via Ubuntu package)

* update to recent stable version:

    sudo npm cache clean -f
    sudo npm install -g n
    sudo n stable

* install vsce:

    sudo npm install -g vsce


## Edit and debug ##

* Shell commands within $ISABELLE_HOME directory:

    isabelle vscode --uninstall-extension makarius.Isabelle
    isabelle vscode src/Tools/VSCode/extension

* VSCode commands:
    Run / Start Debugging (F5)
    File / Open Folder: e.g. `src/HOL/Examples/` then open .thy files


## Build and install ##

    isabelle build_vscode -I
