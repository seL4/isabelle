# Isabelle/VSCode Prover IDE

## General notes

This is the Isabelle/VSCode extension to connect VSCodium to
Isabelle/PIDE. The application is invoked via `isabelle vscode` on the
command-line. It takes care about configuring the extension and user
settings.

The implementation is centered around the VSCode Language Server
Protocol (LSP), but there are many add-ons that are specific to
Isabelle/PIDE. Moreover, there are important patches to the VSCodium
code-base itself, e.g. to support the UTF-8-Isabelle encoding for
mathematical symbols and to incorporate the corresponding Isabelle
fonts. It is unlikely that this extension will with regular VSCode nor
with any other LSP-based editor.

Isabelle/VSCode works best when opening an Isabelle project directory
as a "workspace", with explorer access to the sources.  Afterwards it
is possible to edit `.thy` and `.ML` files with semantic checking by
the prover in the background, similar to Isabelle/jEdit. There is also
support for other file formats, e.g. `bib` for bibliographic
databases, which may be combined with a regular VSCode extension for
LaTeX/BibTeX.


## Known limitations of Isabelle/VSCode

  * Lack of formal editor perspective in VSCode: only the cursor position is
  used (with some surrounding lines of text).

  * Lack of pretty-printing (logical line breaks) according to window and font
  dimensions.

  * Big theory files may cause problems to the VSCode rendering engine, since
  messages and text decorations are applied to the text as a whole (cf. the
  minimap view).

  * Overall lack of features and refinements compared to Isabelle/jEdit.
