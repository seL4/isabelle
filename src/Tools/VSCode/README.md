# Isabelle/PIDE for Visual Studio Code editor #

* Extension for the editor ([TypeScript](extension/src/extension.ts))
* Language Server protocol implementation ([Isabelle/Scala](src/server.scala))


## Run ##

* Extensions: search for "Isabelle", click "Install"

* Preferences / User settings / edit settings.json: e.g.
    `"isabelle.home": "/home/makarius/isabelle/repos"`

* File / Open Folder: e.g. `src/HOL/Isar_Examples/` then open .thy files


## Debug ##

* shell> `code src/Tools/VSCode/extension`

* View / Debug / Launch Extension

* File / Open Folder: e.g. `src/HOL/Isar_Examples/` then open .thy files


## Build ##

* shell> `cd src/Tools/VSCode/extension`

* shell> `isabelle vscode_grammar`

* shell> `isabelle vscode_symbols`

* shell> `vsce package`


## Relevant links ##

### VSCode editor ###

* https://code.visualstudio.com
* https://code.visualstudio.com/docs/extensionAPI/extension-points
* https://code.visualstudio.com/docs/extensions/example-language-server
* https://github.com/Microsoft/vscode-languageserver-node-example
* https://github.com/Microsoft/vscode


### Protocol ###

* https://code.visualstudio.com/blogs/2016/06/27/common-language-protocol
* https://github.com/Microsoft/vscode-languageserver-node
* https://github.com/Microsoft/language-server-protocol
* https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md
* http://www.jsonrpc.org/specification
* http://www.json.org


### Similar projects ###

* Lean Prover: https://github.com/leanprover/vscode-lean
* Coq: https://github.com/siegebell/vscoq
* OCaml: https://github.com/freebroccolo/vscode-reasonml
* Scala: https://github.com/dragos/dragos-vscode-scala
* Rust:
    * https://github.com/jonathandturner/rls
    * https://github.com/jonathandturner/rls_vscode
    * https://github.com/RustDT/RustLSP
