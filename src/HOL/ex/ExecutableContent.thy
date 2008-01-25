(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A huge set of executable constants *}

theory ExecutableContent
imports
  Main
  Eval
  Code_Index
  "~~/src/HOL/ex/Records"
  AssocList
  Binomial
  Commutative_Ring
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/Real/RealDef"
  GCD
  List_Prefix
  Nat_Infinity
  NatPair
  Nested_Environment
  Permutation
  Primes
  Product_ord
  SetsAndFunctions
  State_Monad
  While_Combinator
  Word
begin

declare term_of_index.simps [code func del]
declare fast_bv_to_nat_helper.simps [code func del]

end
