(*  Title:      HOL/Tools/BNF/bnf_fp_util_tactics.ML
    Author:     Dmitriy Traytel, ETH Zürich
    Copyright   2016

Common tactics for datatype and codatatype constructions.
*)

signature BNF_FP_UTIL_TACTICS =
sig

val mk_xtor_un_fold_xtor_tac: Proof.context -> thm -> thm list -> thm list -> tactic
val mk_xtor_co_rec_id_tac: Proof.context -> thm list -> thm -> thm list -> thm list -> tactic
val mk_xtor_co_rec_tac: Proof.context -> thm -> thm list -> thm list -> tactic
val mk_xtor_co_rec_unique_tac: Proof.context -> BNF_Util.fp_kind -> thm list -> thm list -> thm ->
  thm list -> thm list -> tactic
val mk_xtor_co_rec_transfer_tac: Proof.context -> BNF_Util.fp_kind -> int -> int -> thm list ->
  thm list -> thm list -> thm list -> tactic

end

structure BNF_FP_Util_Tactics =
struct

open BNF_Tactics
open BNF_Util

fun mk_xtor_un_fold_xtor_tac ctxt xtor_un_fold_unique map_id0s inverses =
  HEADGOAL (rtac ctxt xtor_un_fold_unique THEN_ALL_NEW rtac ctxt ext) THEN
  unfold_thms_tac ctxt (@{thms o_apply id_o o_id} @ map_id0s @ inverses) THEN
  ALLGOALS (rtac ctxt refl);

fun mk_conj_arg_congN 1 = @{thm DEADID.rel_mono_strong}
  | mk_conj_arg_congN n = mk_conj_arg_congN (n - 1) RSN (2, @{thm arg_cong2[of _ _ _ _ "(\<and>)"]});

fun mk_xtor_co_rec_id_tac ctxt xtor_un_fold_xtors xtor_un_fold_unique xtor_un_folds map_comps =
  HEADGOAL (rtac ctxt (mk_conj_arg_congN (length xtor_un_fold_xtors) RS iffD1 OF
    (map (fn thm => @{thm DEADID.rel_cong} OF [refl, thm]) xtor_un_fold_xtors)) THEN'
    rtac ctxt xtor_un_fold_unique THEN_ALL_NEW EVERY' [rtac ctxt ext,
      SELECT_GOAL (unfold_thms_tac ctxt
        (o_apply :: @{thms fst_convol' id_o sum.case} @ map_comps @ xtor_un_folds)),
      rtac ctxt refl]);

fun mk_xtor_co_rec_tac ctxt un_fold co_rec_defs co_rec_expand_thms =
  unfold_thms_tac ctxt (un_fold ::
    @{thms o_apply sum.case snd_convol' case_sum_o_inj(2)} @ co_rec_defs @ co_rec_expand_thms) THEN
    HEADGOAL (rtac ctxt refl);

fun mk_xtor_co_rec_unique_tac ctxt fp co_rec_defs co_rec_expand's un_fold_unique map_ids map_comps
    inverses =
  unfold_thms_tac ctxt (co_rec_defs @ co_rec_expand's) THEN
  HEADGOAL (EVERY' [rtac ctxt un_fold_unique]) THEN
  unfold_thms_tac ctxt (map_ids @ map_comps @ inverses @ case_fp fp
    @{thms id_o o_id convol_o fst_convol o_assoc[symmetric]}
    @{thms id_o o_id o_case_sum case_sum_o_inj(1) o_assoc}) THEN
  ALLGOALS (etac ctxt (case_fp fp
    @{thm arg_cong2[of _ _ _ _ BNF_Def.convol, OF refl]}
    @{thm arg_cong2[of _ _ _ _ case_sum, OF refl]}));

fun mk_xtor_co_rec_transfer_tac ctxt fp n m defs un_fold_transfers pre_T_map_transfers xtor_rels =
  case_fp fp
    (CONJ_WRAP (fn (def, un_fold_transfer) =>
        REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
        unfold_thms_tac ctxt [def, o_apply] THEN
        HEADGOAL (rtac ctxt @{thm rel_funD[OF snd_transfer]} THEN'
          etac ctxt (mk_rel_funDN_rotated (n + 1) un_fold_transfer) THEN'
          EVERY' (map2 (fn pre_T_map_transfer => fn xtor_rel =>
            etac ctxt (mk_rel_funDN_rotated 2 @{thm convol_transfer}) THEN'
            rtac ctxt (mk_rel_funDN_rotated 2 @{thm comp_transfer}) THEN'
            rtac ctxt (mk_rel_funDN (m + n) pre_T_map_transfer) THEN'
            REPEAT_DETERM_N m o rtac ctxt @{thm id_transfer} THEN'
            REPEAT_DETERM o rtac ctxt @{thm fst_transfer} THEN'
            rtac ctxt rel_funI THEN'
            etac ctxt (xtor_rel RS iffD2)) pre_T_map_transfers xtor_rels)))
      (defs ~~ un_fold_transfers))
    (CONJ_WRAP (fn (def, un_fold_transfer) =>
        REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
        unfold_thms_tac ctxt [def, o_apply] THEN
        HEADGOAL (rtac ctxt (mk_rel_funDN (n + 1) un_fold_transfer) THEN'
          EVERY' (map2 (fn pre_T_map_transfer => fn xtor_rel =>
            etac ctxt (mk_rel_funDN_rotated 2 @{thm case_sum_transfer}) THEN'
            rtac ctxt (mk_rel_funDN 2 @{thm comp_transfer}) THEN'
            rtac ctxt (mk_rel_funDN (m + n) pre_T_map_transfer) THEN'
            REPEAT_DETERM_N m o rtac ctxt @{thm id_transfer} THEN'
            REPEAT_DETERM_N n o rtac ctxt @{thm Inl_transfer} THEN'
            rtac ctxt rel_funI THEN'
            etac ctxt (xtor_rel RS iffD1)) pre_T_map_transfers xtor_rels) THEN'
          etac ctxt (mk_rel_funDN 1 @{thm Inr_transfer})))
      (defs ~~ un_fold_transfers));

end
