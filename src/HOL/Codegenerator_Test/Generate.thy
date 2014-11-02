
(* Author: Florian Haftmann, TU Muenchen *)

section {* Pervasive test of code generator *}

theory Generate
imports
  Candidates
  "~~/src/HOL/Library/AList_Mapping"
  "~~/src/HOL/Library/Finite_Lattice"
begin

text {*
  If any of the checks fails, inspect the code generated
  by a corresponding @{text export_code} command.
*}

export_code _ checking SML OCaml? Haskell? Scala

end

