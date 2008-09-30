theory Further
imports Setup
begin

section {* Further topics \label{sec:further} *}

subsection {* Further reading *}

text {*
  Do dive deeper into the issue of code generation, you should visit
  the Isabelle/Isar Reference Manual \cite{isabelle-isar-ref} which
  constains exhaustive syntax diagrams.
*}

subsection {* Modules *}

text {*
  When invoking the @{command export_code} command it is possible to leave
  out the @{keyword "module_name"} part;  then code is distributed over
  different modules, where the module name space roughly is induced
  by the @{text Isabelle} theory namespace.

  Then sometimes the awkward situation occurs that dependencies between
  definitions introduce cyclic dependencies between modules, which in the
  @{text Haskell} world leaves you to the mercy of the @{text Haskell} implementation
  you are using,  while for @{text SML}/@{text OCaml} code generation is not possible.

  A solution is to declare module names explicitly.
  Let use assume the three cyclically dependent
  modules are named \emph{A}, \emph{B} and \emph{C}.
  Then, by stating
*}

code_modulename SML
  A ABC
  B ABC
  C ABC

text {*
  we explicitly map all those modules on \emph{ABC},
  resulting in an ad-hoc merge of this three modules
  at serialisation time.
*}

subsection {* Evaluation oracle *}

subsection {* Code antiquotation *}

subsection {* Creating new targets *}

text {* extending targets, adding targets *}

subsection {* Imperative data structures *}

end
