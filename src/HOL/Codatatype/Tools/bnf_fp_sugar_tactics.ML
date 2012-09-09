(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for the LFP/GFP sugar.
*)

signature BNF_FP_SUGAR_TACTICS =
sig
  val mk_case_tac: Proof.context -> int -> int -> int -> thm -> thm -> thm -> tactic
  val mk_coiter_like_tac: thm list -> thm list -> thm -> thm -> thm -> Proof.context -> tactic
  val mk_exhaust_tac: Proof.context -> int -> thm list -> thm -> thm -> tactic
  val mk_fld_iff_unf_tac: Proof.context -> ctyp option list -> cterm -> cterm -> thm -> thm
    -> tactic
  val mk_half_distinct_tac: Proof.context -> thm -> thm list -> tactic
  val mk_inject_tac: Proof.context -> thm -> thm -> tactic
  val mk_iter_like_tac: thm list -> thm list -> thm list -> thm -> thm -> Proof.context -> tactic
end;

structure BNF_FP_Sugar_Tactics : BNF_FP_SUGAR_TACTICS =
struct

open BNF_Tactics
open BNF_Util

fun mk_case_tac ctxt n k m case_def ctr_def unf_fld =
  Local_Defs.unfold_tac ctxt [case_def, ctr_def, unf_fld] THEN
  (rtac (BNF_FP_Util.mk_sum_casesN n k RS ssubst) THEN'
   REPEAT_DETERM_N (Int.max (0, m - 1)) o rtac (@{thm split} RS ssubst) THEN'
   rtac refl) 1;

fun mk_exhaust_tac ctxt n ctr_defs fld_iff_unf sumEN' =
  Local_Defs.unfold_tac ctxt (fld_iff_unf :: ctr_defs) THEN rtac sumEN' 1 THEN
  Local_Defs.unfold_tac ctxt @{thms all_prod_eq} THEN
  EVERY' (maps (fn k => [select_prem_tac n (rotate_tac 1) k, REPEAT_DETERM o dtac @{thm meta_spec},
    etac @{thm meta_mp}, atac]) (1 upto n)) 1;

fun mk_fld_iff_unf_tac ctxt cTs cfld cunf fld_unf unf_fld =
  (rtac iffI THEN'
   EVERY' (map3 (fn cTs => fn cx => fn th =>
     dtac (Drule.instantiate' cTs [NONE, NONE, SOME cx] arg_cong) THEN'
     SELECT_GOAL (Local_Defs.unfold_tac ctxt [th]) THEN'
     atac) [rev cTs, cTs] [cunf, cfld] [unf_fld, fld_unf])) 1;

fun mk_half_distinct_tac ctxt fld_inject ctr_defs =
  Local_Defs.unfold_tac ctxt (fld_inject :: @{thms sum.inject} @ ctr_defs) THEN
  rtac @{thm sum.distinct(1)} 1;

fun mk_inject_tac ctxt ctr_def fld_inject =
  Local_Defs.unfold_tac ctxt [ctr_def] THEN rtac (fld_inject RS ssubst) 1 THEN
  Local_Defs.unfold_tac ctxt @{thms sum.inject Pair_eq conj_assoc} THEN rtac refl 1;

val iter_like_thms =
  @{thms case_unit comp_def convol_def id_apply map_pair_def sum.simps(5,6) sum_map.simps
      split_conv};

fun mk_iter_like_tac pre_map_defs map_ids iter_like_defs fld_iter_like ctr_def ctxt =
  Local_Defs.unfold_tac ctxt (ctr_def :: fld_iter_like :: iter_like_defs @ pre_map_defs @ map_ids @
    iter_like_thms) THEN Local_Defs.unfold_tac ctxt @{thms id_def} THEN rtac refl 1;

val coiter_like_ss = ss_only @{thms if_True if_False};
val coiter_like_thms = @{thms id_apply map_pair_def sum_map.simps prod.cases};

fun mk_coiter_like_tac coiter_like_defs map_ids fld_unf_coiter_like pre_map_def ctr_def ctxt =
  Local_Defs.unfold_tac ctxt (ctr_def :: coiter_like_defs) THEN
  subst_tac ctxt [fld_unf_coiter_like] 1 THEN asm_simp_tac coiter_like_ss 1 THEN
  Local_Defs.unfold_tac ctxt (pre_map_def :: coiter_like_thms @ map_ids) THEN
  Local_Defs.unfold_tac ctxt @{thms id_def} THEN rtac refl 1;

end;
