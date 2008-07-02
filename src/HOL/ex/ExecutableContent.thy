(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A huge set of executable constants *}

theory ExecutableContent
imports
  Complex_Main
  AssocList
  Binomial
  Commutative_Ring
  Enum
  Eval
  List_Prefix
  Nat_Infinity
  NatPair
  Nested_Environment
  Option_ord
  Permutation
  Primes
  Product_ord
  SetsAndFunctions
  State_Monad
  While_Combinator
  Word
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/ex/Records"
begin

lemma [code func, code func del]: "(Eval.term_of \<Colon> index \<Rightarrow> term) = Eval.term_of" ..
declare fast_bv_to_nat_helper.simps [code func del]

(*FIXME distribute to theories*)
declare divides_def [code func del] -- "Univ_Poly"
declare star_minus_def [code func del] -- "StarDef"
declare Zseq_def [code func del]
declare Bseq_def [code func del]
declare monoseq_def [code func del]
declare Cauchy_def [code func del]
declare subseq_def [code func del]
declare powhr_def [code func del]
declare hlog_def [code func del]
declare scaleHR_def [code func del]
declare stc_def [code func del]
declare increment_def [code func del]
declare of_hypreal_def [code func del]
declare HInfinite_def [code func del]
declare is_starext_def [code func del]
declare isNSUCont_def [code func del]
declare isNSCont_def [code func del]
declare isUCont_def [code func del]
declare NSCauchy_def [code func del]
declare NSBseq_def [code func del]

setup {*
  Code.del_funcs
    (AxClass.param_of_inst @{theory} (@{const_name "Eval.term_of"}, @{type_name "env"}))
*}

end
