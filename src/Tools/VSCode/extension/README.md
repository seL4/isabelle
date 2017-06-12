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


## Isabelle symbols ##

Isabelle symbols like `\<forall>` are rendered using the extension "Prettify
Symbols Mode", which needs to be installed separately.
