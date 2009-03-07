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

lemma [code, code del]:
  "(size :: 'a::size Predicate.pred => nat) = size" ..
lemma [code, code del]:
  "pred_size = pred_size" ..
lemma [code, code del]:
  "pred_case = pred_case" ..
lemma [code, code del]:
  "pred_rec = pred_rec" ..
lemma [code, code del]:
  "(Code_Eval.term_of \<Colon> 'a::{type, term_of} Predicate.pred \<Rightarrow> Code_Eval.term) = Code_Eval.term_of" ..
lemma [code, code del]:
  "(Code_Eval.term_of \<Colon> 'a::{type, term_of} Predicate.seq \<Rightarrow> Code_Eval.term) = Code_Eval.term_of" ..

text {* However, some aren't executable *}

declare pair_leq_def[code del]
declare max_weak_def[code del]
declare min_weak_def[code del]
declare ms_weak_def[code del]

end
