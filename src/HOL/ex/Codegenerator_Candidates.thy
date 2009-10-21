
(* Author: Florian Haftmann, TU Muenchen *)

header {* A huge collection of equations to generate code from *}

theory Codegenerator_Candidates
imports
  Complex_Main
  AssocList
  Binomial
  Fset
  Commutative_Ring
  Enum
  List_Prefix
  Nat_Infinity
  Nested_Environment
  Option_ord
  Permutation
  "~~/src/HOL/Number_Theory/Primes"
  Product_ord
  SetsAndFunctions
  Tree
  While_Combinator
  Word
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/ex/Records"
begin

(*avoid popular infix*)
code_reserved SML upto

end
