# Isabelle/VSCode development #

## System requirements ##

* install default node.js (e.g. via Ubuntu package)

* update to recent stable version:

    sudo npm cache clean -f
    sudo npm install -g n
    sudo n stable

* install add-on tools:

    sudo npm install -g yarn vsce


## Edit and debug ##

* Shell commands within $ISABELLE_HOME directory:

    isabelle component_vscode_extension -U
    isabelle vscode src/Tools/VSCode/extension

* VSCode commands:
    Run / Start Debugging (F5)
    File / Open Folder: e.g. `src/HOL/Examples/` then open .thy files


## Build and install ##

    isabelle component_vscode_extension -I
