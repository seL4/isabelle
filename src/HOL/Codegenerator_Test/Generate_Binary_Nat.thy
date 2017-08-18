
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Pervasive test of code generator\<close>

theory Generate_Binary_Nat
imports
  Candidates
  "HOL-Library.AList_Mapping"
  "HOL-Library.Finite_Lattice"
  "HOL-Library.Code_Binary_Nat"
begin

text \<open>
  If any of the checks fails, inspect the code generated
  by a corresponding \<open>export_code\<close> command.
\<close>

export_code _ checking SML OCaml? Haskell? Scala

end
