(*  Title:      HOL/Tools/BNF/bnf_fp_n2m_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Tactics for mutualization of nested (co)datatypes.
*)

signature BNF_FP_N2M_TACTICS =
sig
  val mk_rel_xtor_co_induct_tac: BNF_Util.fp_kind -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> {prems: thm list, context: Proof.context} -> tactic
  val mk_xtor_un_fold_unique_tac: BNF_Util.fp_kind -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm list -> thm list ->
    {context: Proof.context, prems: thm list} -> tactic
  val mk_xtor_un_fold_tac: Proof.context -> int -> thm list -> thm list -> tactic
  val mk_xtor_un_fold_transfer_tac: Proof.context -> int -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> tactic
end;

structure BNF_FP_N2M_Tactics : BNF_FP_N2M_TACTICS =
struct

open BNF_Util
open BNF_Tactics
open BNF_FP_Util

val vimage2p_unfolds = o_apply :: @{thms vimage2p_def};

fun unfold_at_most_once_tac ctxt thms =
  CONVERSION (Conv.top_sweep_rewrs_conv thms ctxt);
val unfold_once_tac = CHANGED ooo unfold_at_most_once_tac;

fun mk_rel_xtor_co_induct_tac fp abs_inverses co_inducts0 rel_defs rel_monos nesting_rel_eqs0
  nesting_rel_monos0 {context = ctxt, prems = raw_C_IHs} =
  let
    val nesting_rel_eqs = @{thms prod.rel_eq sum.rel_eq} @ nesting_rel_eqs0;
    val nesting_rel_monos = map (fn thm => rotate_prems ~1 (thm RS @{thm predicate2D}))
      (@{thms prod.rel_mono sum.rel_mono} @ nesting_rel_monos0);
    val co_inducts = map (unfold_thms ctxt (vimage2p_unfolds @ nesting_rel_eqs)) co_inducts0;
    val unfolds = map (fn def =>
      unfold_thms ctxt (id_apply :: vimage2p_unfolds @ abs_inverses @ no_reflexive [def])) rel_defs;
    val folded_C_IHs = map (fn thm => thm RS @{thm spec2} RS mp) raw_C_IHs;
    val C_IHs = map2 (curry op |>) folded_C_IHs unfolds;
    val C_IH_monos =
      @{map 3} (fn C_IH => fn mono => fn unfold =>
        (mono RSN (2, @{thm vimage2p_mono}), C_IH)
        |> fp = Greatest_FP ? swap
        |> op RS
        |> unfold)
      folded_C_IHs rel_monos unfolds;

    val sym_nested_rel_eqs = map mk_sym nesting_rel_eqs;
  in
    unfold_thms_tac ctxt vimage2p_unfolds THEN
    HEADGOAL (CONJ_WRAP_GEN' (rtac ctxt @{thm context_conjI})
      (fn thm => rtac ctxt thm THEN_ALL_NEW (rotate_tac ~1 THEN'
         REPEAT_ALL_NEW (FIRST' [eresolve_tac ctxt C_IHs, eresolve_tac ctxt C_IH_monos,
           SELECT_GOAL (unfold_thms_tac ctxt nesting_rel_eqs) THEN' rtac ctxt @{thm order_refl},
           assume_tac ctxt, resolve_tac ctxt co_inducts,
           resolve_tac ctxt C_IH_monos THEN_ALL_NEW (TRY o FIRST'
             [SELECT_GOAL (unfold_thms_tac ctxt sym_nested_rel_eqs) THEN' assume_tac ctxt,
              rtac ctxt @{thm order_refl},
              REPEAT_ALL_NEW (eresolve_tac ctxt nesting_rel_monos)])])))
    co_inducts)
  end;

fun mk_xtor_un_fold_unique_tac fp xtor_un_fold_defs map_arg_congs xtor_un_fold_o_maps
   Rep_o_Abss fp_un_fold_uniques simp_thms map_thms map_defs cache_defs {context = ctxt, prems} =
  unfold_thms_tac ctxt xtor_un_fold_defs THEN
  HEADGOAL (REPEAT_DETERM o FIRST' [hyp_subst_tac_thin true ctxt, rtac ctxt refl,
    rtac ctxt conjI,
    rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<circ>)", OF refl]},
    rtac ctxt @{thm arg_cong2[of _ _ _ _ "(\<circ>)", OF _ refl]},
    resolve_tac ctxt map_arg_congs,
    resolve_tac ctxt fp_un_fold_uniques THEN_ALL_NEW case_fp fp (K all_tac) (rtac ctxt sym),
    SELECT_GOAL (CHANGED (unfold_thms_tac ctxt (flat [simp_thms, map_thms, map_defs,
      xtor_un_fold_defs, xtor_un_fold_o_maps, Rep_o_Abss, prems]))),
    unfold_once_tac ctxt cache_defs]);

fun mk_xtor_un_fold_tac ctxt n simps cache_defs =
  REPEAT_DETERM (CHANGED (unfold_thms_tac ctxt simps) ORELSE
    CHANGED (ALLGOALS (unfold_at_most_once_tac ctxt cache_defs))) THEN
  CONJ_WRAP (K (HEADGOAL (rtac ctxt refl))) (1 upto n);

fun mk_xtor_un_fold_transfer_tac ctxt n xtor_un_fold_defs rel_defs fp_un_fold_transfers
    map_transfers Abs_transfers fp_or_nesting_rel_eqs cache_defs =
  let
    val unfold = SELECT_GOAL (unfold_thms_tac ctxt fp_or_nesting_rel_eqs);
  in
    unfold_thms_tac ctxt (xtor_un_fold_defs @ rel_defs) THEN
    HEADGOAL (CONJ_WRAP'
      (fn thm => EVERY' [REPEAT_DETERM_N n o rtac ctxt rel_funI, rtac ctxt thm THEN_ALL_NEW
        REPEAT_DETERM o (FIRST' [assume_tac ctxt, rtac ctxt @{thm id_transfer},
            rtac ctxt @{thm rel_funD[OF rel_funD[OF comp_transfer]]},
            resolve_tac ctxt fp_un_fold_transfers, resolve_tac ctxt map_transfers,
            unfold_once_tac ctxt cache_defs,
            resolve_tac ctxt Abs_transfers, rtac ctxt @{thm vimage2p_rel_fun},
            unfold THEN' rtac ctxt @{thm vimage2p_rel_fun}])])
      fp_un_fold_transfers)
  end;

end;
