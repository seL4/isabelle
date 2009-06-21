
(* Author: Florian Haftmann, TU Muenchen *)

header {* A huge collection of equations to generate code from *}

theory Codegenerator_Candidates
imports
  Complex_Main
  AssocList
  Binomial
  Commutative_Ring
  Enum
  List_Prefix
  Nat_Infinity
  Nested_Environment
  Option_ord
  Permutation
  Primes
  Product_ord
  SetsAndFunctions
  Tree
  While_Combinator
  Word
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/ex/Records"
begin

(*avoid popular infixes*)
code_reserved SML union inter upto

end
