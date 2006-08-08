(*  Title:      HOL/Main.thy
    ID:         $Id$
*)

header {* Main HOL *}

theory Main
imports SAT Reconstruction ResAtpMethods
begin

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.
*}

text {* \medskip Late clause setup: installs \emph{all} simprules and
  claset rules into the clause cache; cf.\ theory @{text
  Reconstruction}. *}

setup ResAxioms.setup


(*The following declarations generate polymorphic Skolem functions for 
  these theorems. NOTE: We need an automatic mechanism to ensure that this
  happens for all theorems stored in descendant theories.*)

(*HOL*)
declare ext [skolem]

(*Finite_Set*)
declare setprod_nonneg [skolem]
declare setprod_pos [skolem]
declare setsum_bounded [skolem]
declare setsum_mono [skolem]
declare setsum_nonneg [skolem]
declare setsum_nonpos [skolem]
declare setsum_0' [skolem]
declare setprod_1' [skolem]

declare Fun.image_INT [skolem]

(*List. Only none look useful.*)
declare Cons_eq_append_conv [skolem]
declare Cons_eq_map_D [skolem]
declare Cons_eq_map_conv [skolem]
declare append_eq_Cons_conv [skolem]
declare map_eq_Cons_D [skolem]
declare map_eq_Cons_conv [skolem]

declare Orderings.max_leastL [skolem]
declare Orderings.max_leastR [skolem]

declare Product_Type.Sigma_mono [skolem]

(*Relation*)
declare Domain_iff [skolem]
declare Image_iff [skolem]
declare Range_iff [skolem]
declare antisym_def [skolem]
declare reflI [skolem]
declare rel_compEpair [skolem]
declare refl_def [skolem]
declare sym_def [skolem]
declare trans_def [skolem]
declare single_valued_def [skolem]  

(*Relation_Power*)
declare rel_pow_E2 [skolem]
declare rel_pow_E [skolem]
declare rel_pow_Suc_D2 [skolem]
declare rel_pow_Suc_D2' [skolem]
declare rel_pow_Suc_E [skolem]

(*Set*)
declare Collect_mono [skolem]
declare INT_anti_mono [skolem]
declare INT_greatest [skolem]
declare INT_subset_iff [skolem]
declare Int_Collect_mono [skolem]
declare Inter_greatest[skolem]
declare UN_least [skolem]
declare UN_mono [skolem]
declare UN_subset_iff [skolem]
declare Union_least [skolem]
declare Union_disjoint [skolem]
declare disjoint_iff_not_equal [skolem]
declare image_subsetI [skolem]
declare image_subset_iff [skolem]
declare subset_def [skolem]
declare subset_iff [skolem]

(*Transitive_Closure*)
declare converse_rtranclE [skolem]
declare irrefl_trancl_rD [skolem]
declare rtranclE [skolem]
declare tranclD [skolem]
declare tranclE [skolem]

(*Wellfounded_Recursion*)
declare acyclicI [skolem]
declare acyclic_def [skolem]
declare wfI [skolem]
declare wf_def [skolem]
declare wf_eq_minimal [skolem]

end
