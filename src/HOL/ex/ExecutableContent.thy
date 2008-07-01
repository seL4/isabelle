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
declare unstar_def [code func del] -- "StarDef"
declare star_one_def [code func del] -- "StarDef"
declare star_mult_def [code func del] -- "StarDef"
declare star_add_def [code func del] -- "StarDef"
declare star_zero_def [code func del] -- "StarDef"
declare star_minus_def [code func del] -- "StarDef"
declare star_diff_def [code func del] -- "StarDef"
declare Reals_def [code func del] -- "RealVector"
declare star_scaleR_def [code func del] -- "HyperDef"
declare hyperpow_def [code func del] -- HyperDef
declare Infinitesimal_def [code func del] -- NSA
declare HFinite_def [code func del] -- NSA
declare floor_def [code func del] -- RComplete
declare LIMSEQ_def [code func del] -- SEQ
declare partition_def [code func del] -- Integration
declare Integral_def [code func del] -- Integration
declare tpart_def [code func del] -- Integration
declare psize_def [code func del] -- Integration
declare gauge_def [code func del] -- Integration
declare fine_def [code func del] -- Integration
declare sumhr_def [code func del] -- HSeries
declare NSsummable_def [code func del] -- HSeries
declare NSLIMSEQ_def [code func del] -- HSEQ
declare newInt.simps [code func del] -- ContNotDenum
declare LIM_def [code func del] -- Lim
declare NSLIM_def [code func del] -- HLim
declare HComplex_def [code func del]
declare of_hypnat_def [code func del]
declare InternalSets_def [code func del]
declare InternalFuns_def [code func del]
declare increment_def [code func del]
declare is_starext_def [code func del]
declare hrcis_def [code func del]
declare hexpi_def [code func del]
declare hsgn_def [code func del]
declare hcnj_def [code func del]
declare hcis_def [code func del]
declare harg_def [code func del]
declare isNSUCont_def [code func del]
declare hRe_def [code func del]
declare hIm_def [code func del]
declare HInfinite_def [code func del]
declare hSuc_def [code func del]
declare NSCauchy_def [code func del]
declare of_hypreal_def [code func del]
declare isNSCont_def [code func del]
declare monoseq_def [code func del]
declare scaleHR_def [code func del]
declare isUCont_def [code func del]
declare NSBseq_def [code func del]
declare subseq_def [code func del]
declare Cauchy_def [code func del]
declare powhr_def [code func del]
declare hlog_def [code func del]
declare Zseq_def [code func del]
declare Bseq_def [code func del]
declare stc_def [code func del]

setup {*
  Code.del_funcs
    (AxClass.param_of_inst @{theory} (@{const_name "Eval.term_of"}, @{type_name "env"}))
*}

end
