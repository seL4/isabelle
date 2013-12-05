
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

text {* Formal joining of hierarchy of implicit definitions in Scala *}

class semiring_numeral_even_odd = semiring_numeral_div + even_odd

instance nat :: semiring_numeral_even_odd ..

definition semiring_numeral_even_odd :: "'a itself \<Rightarrow> 'a::semiring_numeral_even_odd"
where
  "semiring_numeral_even_odd TYPE('a) = undefined"

definition semiring_numeral_even_odd_nat :: "nat itself \<Rightarrow> nat"
where
  "semiring_numeral_even_odd_nat = semiring_numeral_even_odd"

export_code _ checking  SML OCaml? Haskell? Scala

end
