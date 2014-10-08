(*  Title:      HOL/Tools/Transfer/transfer_bnf.ML
    Author:     Ondrej Kuncar, TU Muenchen

Setup for Lifting for types that are BNF.
*)

signature LIFTING_BNF =
sig
  val lifting_plugin: string
end

structure Lifting_BNF : LIFTING_BNF =
struct

open BNF_Util
open BNF_Def
open Transfer_BNF

val lifting_plugin = "lifting"

(* Quotient map theorem *)

fun Quotient_tac bnf ctxt i =
  let
    val rel_Grp = rel_Grp_of_bnf bnf
    fun get_lhs thm = thm |> concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
    val vars = get_lhs rel_Grp |> strip_comb |> snd |> map_filter (try (strip_comb #> snd #> hd))
    val UNIVs = map (fn var => HOLogic.mk_UNIV (var |> dest_Var |> snd |> dest_Type |> snd |> hd)) vars
    val inst = map2 (curry(pairself (certify ctxt))) vars UNIVs
    val rel_Grp_UNIV_sym = rel_Grp |> Drule.instantiate_normalize ([], inst) 
      |> Local_Defs.unfold ctxt @{thms subset_UNIV[THEN eqTrueI] UNIV_def[symmetric] simp_thms(21)}
      |> (fn thm => thm RS sym)
    val rel_mono = rel_mono_of_bnf bnf
    val rel_conversep_sym = rel_conversep_of_bnf bnf RS sym
  in
    EVERY' [SELECT_GOAL (Local_Defs.unfold_tac ctxt [@{thm Quotient_alt_def5}]), 
      REPEAT_DETERM o (etac conjE), rtac conjI, SELECT_GOAL (Local_Defs.unfold_tac ctxt [rel_Grp_UNIV_sym]),
      rtac rel_mono THEN_ALL_NEW atac, rtac conjI, SELECT_GOAL (Local_Defs.unfold_tac ctxt
        [rel_conversep_sym, rel_Grp_UNIV_sym]), rtac rel_mono THEN_ALL_NEW atac,
      SELECT_GOAL (Local_Defs.unfold_tac ctxt [rel_conversep_sym, rel_OO_of_bnf bnf RS sym]),
      hyp_subst_tac ctxt, rtac refl] i
  end

fun mk_Quotient args =
  let
    val argTs = map fastype_of args
  in
    list_comb (Const (@{const_name Quotient}, argTs ---> HOLogic.boolT), args)
  end

fun prove_Quotient_map bnf ctxt =
  let
    val live = live_of_bnf bnf
    val old_ctxt = ctxt
    val (((As, Bs), Ds), ctxt) = ctxt
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees (dead_of_bnf bnf)
    val argTss = map2 (fn a => fn b => [mk_pred2T a a, a --> b, b --> a,mk_pred2T a b]) As Bs
    val ((argss, argss'), ctxt) =
      @{fold_map 2} mk_Frees ["R", "Abs", "Rep", "T"] (transpose argTss) ctxt
      |>> `transpose
   
    val assms = map (mk_Quotient #> HOLogic.mk_Trueprop) argss
    val R_rel = list_comb (mk_rel_of_bnf Ds As As bnf, nth argss' 0)
    val Abs_map = list_comb (mk_map_of_bnf Ds As Bs bnf, nth argss' 1)
    val Rep_map = list_comb (mk_map_of_bnf Ds Bs As bnf, nth argss' 2)
    val T_rel = list_comb (mk_rel_of_bnf Ds As Bs bnf, nth argss' 3)
    val concl = mk_Quotient [R_rel, Abs_map, Rep_map, T_rel] |> HOLogic.mk_Trueprop
    val goal = Logic.list_implies (assms, concl)
    val thm = Goal.prove_sorry ctxt [] [] goal 
      (fn {context = ctxt, prems = _} => Quotient_tac bnf ctxt 1)
      |> Thm.close_derivation
  in
    Drule.zero_var_indexes (singleton (Variable.export ctxt old_ctxt) thm)
  end


fun Quotient_map bnf ctxt =
  let
    val Quotient = prove_Quotient_map bnf ctxt
    fun qualify defname suffix = Binding.qualified true suffix defname
    val Quotient_thm_name = qualify (base_name_of_bnf bnf) "Quotient"
    val notes = [((Quotient_thm_name, []), [([Quotient], @{attributes [quot_map]})])]
  in
    notes
  end

(* relator_eq_onp  *)

fun relator_eq_onp bnf ctxt =
  let
    val relator_eq_onp_thm = lookup_defined_pred_data ctxt (type_name_of_bnf bnf)
      |> Transfer.rel_eq_onp |> Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.arg1_conv 
          (Raw_Simplifier.rewrite ctxt false @{thms eq_onp_top_eq_eq[THEN eq_reflection]})))
  in
    [((Binding.empty, []), [([relator_eq_onp_thm], @{attributes [relator_eq_onp]})])]    
  end
  handle ERROR _ => [] (* the "lifting" plugin should work even if "quotient" is disabled *)

(* relator_mono  *)

fun relator_mono bnf =
  [((Binding.empty, []), [([rel_mono_of_bnf bnf], @{attributes [relator_mono]})])]    
  
(* relator_distr  *)

fun relator_distr bnf =
  [((Binding.empty, []), [([rel_OO_of_bnf bnf RS sym], @{attributes [relator_distr]})])]

(* interpretation *)

fun lifting_bnf_interpretation bnf lthy =
  if dead_of_bnf bnf > 0 then lthy
  else
    let
      val notess = [relator_eq_onp bnf lthy, Quotient_map bnf lthy, relator_mono bnf,
        relator_distr bnf]
    in
      lthy |> fold (perhaps o try o (snd oo Local_Theory.notes)) notess
    end

val _ = Theory.setup (bnf_interpretation lifting_plugin
  (bnf_only_type_ctr (BNF_Util.map_local_theory o lifting_bnf_interpretation))
  (bnf_only_type_ctr lifting_bnf_interpretation))

end
