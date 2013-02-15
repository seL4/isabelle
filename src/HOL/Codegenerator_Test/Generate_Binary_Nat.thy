
(* Author: Florian Haftmann, TU Muenchen *)

header {* Pervasive test of code generator *}

theory Generate_Binary_Nat
imports
  Candidates
  "~~/src/HOL/Library/AList_Mapping"
  "~~/src/HOL/Library/Finite_Lattice"
  "~~/src/HOL/Library/Code_Binary_Nat"
begin

text {*
  If any of the checks fails, inspect the code generated
  by a corresponding @{text export_code} command.
*}

export_code _ checking SML OCaml? Haskell? Scala

end
