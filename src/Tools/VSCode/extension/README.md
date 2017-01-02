# Isabelle Prover IDE support

This extension connects to the Isabelle Prover IDE infrastructure, using the
VSCode Language Server protocol. This requires a recent development version of
Isabelle from 2017, see also:

  * http://isabelle.in.tum.de/devel
  * http://isabelle.in.tum.de/repos/isabelle/file/tip/src/Tools/VSCode


## Important User Settings ##

  * `isabelle.home` points to the main Isabelle directory (ISABELLE_HOME).
  * `isabelle.cygwin_root` (on Windows) points to the Cygwin installation,
    e.g. ISABELLE_HOME/cygwin for a regular Isabelle application bundle.
