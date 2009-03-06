(*  Author:     Florian Haftmann, TU Muenchen
*)

header {* A huge set of executable constants *}

theory ExecutableContent
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
  While_Combinator
  Word
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/ex/Records"
begin

lemma [code, code del]: "(term_of \<Colon> 'a Predicate.pred \<Rightarrow> term) = term_of" ..

text {* However, some aren't executable *}

declare pair_leq_def[code del]
declare max_weak_def[code del]
declare min_weak_def[code del]
declare ms_weak_def[code del]

end
