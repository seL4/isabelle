
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator *}

theory Generate
imports Candidates
begin

subsection {* Check whether generated code compiles *}

text {*
  If any of the checks fails, inspect the code generated
  by a corresponding @{text export_code} command.
*}

export_code "*" checking SML OCaml? Haskell? Scala?

end
