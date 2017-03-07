# Isabelle Prover IDE support

This extension connects to the Isabelle Prover IDE infrastructure, using the
VSCode Language Server protocol. This requires a recent development version of
Isabelle from 2017, see also:

  * http://isabelle.in.tum.de/devel
  * http://isabelle.in.tum.de/repos/isabelle/file/tip/src/Tools/VSCode


## Important User Settings ##

  * On Linux and Mac OS X: `isabelle.home` points to the main Isabelle
    directory (`$ISABELLE_HOME`).

  * On Windows: `isabelle.home` as above, but in Windows path notation with
    drive-letter and backslashes.

    Moreover, `isabelle.cygwin_root` needs to point to a suitable Cygwin
    installation, e.g. `$ISABELLE_HOME\contrib\cygwin` for a regular Isabelle
    application bundle, or `C:\cygwin` for a stand-alone installation used
    with Isabelle repository snapshot.


## Isabelle symbols ##

Isabelle symbols like `\<forall>` may be rendered using the extension Prettify
Symbols Mode. It needs to be configured manually as follows:

$ISABELLE_HOME/src/Tools/VSCode/extension/isabelle-symbols.json contains a
configuration (generated via `isabelle build_vscode`). Its content needs to
be copied carefully into the regular VSCode User Preferences.
