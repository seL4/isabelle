(*  Title:      HOL/Tools/Lifting/lifting_bnf.ML
    Author:     Ondrej Kuncar, TU Muenchen

Setup for Lifting for types that are BNF.
*)

signature LIFTING_BNF =
sig
end

structure Lifting_BNF : LIFTING_BNF =
struct

open BNF_Util
open BNF_Def
open Transfer_BNF

(* Quotient map theorem *)

fun Quotient_tac bnf ctxt i =
  let
    val rel_Grp = rel_Grp_of_bnf bnf
    fun get_lhs thm = thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
    val vars = get_lhs rel_Grp |> strip_comb |> snd |> map_filter (try (strip_comb #> snd #> hd))
    val UNIVs = map (fn var => HOLogic.mk_UNIV (var |> dest_Var |> snd |> dest_Type |> snd |> hd)) vars
    val inst = map dest_Var vars ~~ map (Thm.cterm_of ctxt) UNIVs
    val rel_Grp_UNIV_sym = rel_Grp |> Drule.instantiate_normalize (TVars.empty, Vars.make inst) 
      |> Local_Defs.unfold0 ctxt @{thms subset_UNIV[THEN eqTrueI] UNIV_def[symmetric] simp_thms(21)}
      |> (fn thm => thm RS sym)
    val rel_mono = rel_mono_of_bnf bnf
    val rel_conversep_sym = rel_conversep_of_bnf bnf RS sym
  in
    EVERY' [SELECT_GOAL (Local_Defs.unfold0_tac ctxt [@{thm Quotient_alt_def5}]), 
      REPEAT_DETERM o (etac ctxt conjE), rtac ctxt conjI, SELECT_GOAL (Local_Defs.unfold0_tac ctxt [rel_Grp_UNIV_sym]),
      rtac ctxt rel_mono THEN_ALL_NEW assume_tac ctxt, rtac ctxt conjI, SELECT_GOAL (Local_Defs.unfold0_tac ctxt
        [rel_conversep_sym, rel_Grp_UNIV_sym]), rtac ctxt rel_mono THEN_ALL_NEW assume_tac ctxt,
      SELECT_GOAL (Local_Defs.unfold0_tac ctxt [rel_conversep_sym, rel_OO_of_bnf bnf RS sym]),
      hyp_subst_tac ctxt, rtac ctxt refl] i
  end

fun mk_Quotient args =
  let
    val argTs = map fastype_of args
  in
    list_comb (Const (\<^const_name>\<open>Quotient\<close>, argTs ---> HOLogic.boolT), args)
  end

fun prove_Quotient_map bnf ctxt =
  let
    val live = live_of_bnf bnf
    val (((As, Bs), Ds), ctxt') = ctxt
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees (dead_of_bnf bnf)
    val argTss = map2 (fn a => fn b => [mk_pred2T a a, a --> b, b --> a,mk_pred2T a b]) As Bs
    val ((argss, argss'), ctxt'') = ctxt'
      |> @{fold_map 2} mk_Frees ["R", "Abs", "Rep", "T"] (transpose argTss)
      |>> `transpose
   
    val assms = map (mk_Quotient #> HOLogic.mk_Trueprop) argss
    val R_rel = list_comb (mk_rel_of_bnf Ds As As bnf, nth argss' 0)
    val Abs_map = list_comb (mk_map_of_bnf Ds As Bs bnf, nth argss' 1)
    val Rep_map = list_comb (mk_map_of_bnf Ds Bs As bnf, nth argss' 2)
    val T_rel = list_comb (mk_rel_of_bnf Ds As Bs bnf, nth argss' 3)
    val concl = mk_Quotient [R_rel, Abs_map, Rep_map, T_rel] |> HOLogic.mk_Trueprop
    val goal = Logic.list_implies (assms, concl)
  in
    Goal.prove_sorry ctxt'' [] [] goal
      (fn {context = goal_ctxt, ...} => Quotient_tac bnf goal_ctxt 1)
    |> Thm.close_derivation \<^here>
    |> singleton (Variable.export ctxt'' ctxt)
    |> Drule.zero_var_indexes
  end


fun Quotient_map bnf ctxt =
  let
    val Quotient = prove_Quotient_map bnf ctxt
    val Quotient_thm_name = Binding.qualify_name true (base_name_of_bnf bnf) "Quotient"
  in [((Quotient_thm_name, []), [([Quotient], @{attributes [quot_map]})])] end

(* relator_eq_onp  *)

fun relator_eq_onp bnf =
  [(Binding.empty_atts, [([rel_eq_onp_of_bnf bnf], @{attributes [relator_eq_onp]})])]

(* relator_mono  *)

fun relator_mono bnf =
  [(Binding.empty_atts, [([rel_mono_of_bnf bnf], @{attributes [relator_mono]})])]    
  
(* relator_distr  *)

fun relator_distr bnf =
  [(Binding.empty_atts, [([rel_OO_of_bnf bnf RS sym], @{attributes [relator_distr]})])]

(* interpretation *)

fun lifting_bnf_interpretation bnf lthy =
  if dead_of_bnf bnf > 0 then lthy
  else
    let
      val notess = [relator_eq_onp bnf, Quotient_map bnf lthy, relator_mono bnf,
        relator_distr bnf]
    in
      lthy |> fold (perhaps o try o (snd oo Local_Theory.notes)) notess
    end

val lifting_plugin = Plugin_Name.declare_setup \<^binding>\<open>lifting\<close>

val _ =
  Theory.setup
    (bnf_interpretation lifting_plugin (bnf_only_type_ctr lifting_bnf_interpretation))

end
