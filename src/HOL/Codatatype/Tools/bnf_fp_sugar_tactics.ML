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
  val mk_fld_iff_unf_tac: Proof.context -> ctyp option list -> cterm -> cterm -> thm -> thm ->
    tactic
  val mk_half_distinct_tac: Proof.context -> thm -> thm list -> tactic
  val mk_induct_tac: Proof.context -> int list -> int list list ->
    ((int * int) * (int * int)) list list list -> thm list -> thm -> thm list -> thm list list ->
    tactic
  val mk_inject_tac: Proof.context -> thm -> thm -> tactic
  val mk_iter_like_tac: thm list -> thm list -> thm list -> thm -> thm -> Proof.context -> tactic
end;

structure BNF_FP_Sugar_Tactics : BNF_FP_SUGAR_TACTICS =
struct

open BNF_Tactics
open BNF_Util
open BNF_FP_Util

val meta_mp = @{thm meta_mp};
val meta_spec = @{thm meta_spec};

fun smash_spurious_fs lthy thm =
  let
    val fs =
      Term.add_vars (prop_of thm) []
      |> filter (fn (_, Type (@{type_name fun}, [_, T'])) => T' <> HOLogic.boolT | _ => false);
    val cfs =
      map (fn f as (_, T) => (certify lthy (Var f), certify lthy (id_abs (domain_type T)))) fs;
  in
    Drule.cterm_instantiate cfs thm
  end;

val smash_spurious_fs_tac = PRIMITIVE o smash_spurious_fs;

fun mk_case_tac ctxt n k m case_def ctr_def unf_fld =
  Local_Defs.unfold_tac ctxt [case_def, ctr_def, unf_fld] THEN
  (rtac (mk_sum_casesN_balanced n k RS ssubst) THEN'
   REPEAT_DETERM_N (Int.max (0, m - 1)) o rtac (@{thm split} RS ssubst) THEN'
   rtac refl) 1;

fun mk_exhaust_tac ctxt n ctr_defs fld_iff_unf sumEN' =
  Local_Defs.unfold_tac ctxt (fld_iff_unf :: ctr_defs) THEN rtac sumEN' 1 THEN
  Local_Defs.unfold_tac ctxt @{thms all_prod_eq} THEN
  EVERY' (maps (fn k => [select_prem_tac n (rotate_tac 1) k, REPEAT_DETERM o dtac meta_spec,
    etac meta_mp, atac]) (1 upto n)) 1;

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
  Local_Defs.unfold_tac ctxt @{thms id_def} THEN
  TRY ((rtac refl ORELSE' subst_tac ctxt @{thms unit_eq} THEN' rtac refl) 1);

fun mk_induct_prelude_tac ctxt ctr_defs fld_induct' =
  Local_Defs.unfold_tac ctxt ctr_defs THEN rtac fld_induct' 1 THEN smash_spurious_fs_tac ctxt;

fun mk_induct_prepare_prem_tac n m k =
  EVERY' [select_prem_tac n (rotate_tac 1) k, rotate_tac ~1, hyp_subst_tac,
    REPEAT_DETERM_N m o (dtac meta_spec THEN' rotate_tac ~1)] 1;

(* FIXME: why not in "Pure"? *)
fun prefer_tac i = defer_tac i THEN PRIMITIVE (Thm.permute_prems 0 ~1);

fun mk_induct_prepare_prem_prems_tac r =
  REPEAT_DETERM_N r (rotate_tac ~1 1 THEN dtac meta_mp 1 THEN rotate_tac 1 1 THEN prefer_tac 2) THEN
  PRIMITIVE Raw_Simplifier.norm_hhf;

val induct_prem_prem_thms =
  @{thms SUP_empty Sup_empty Sup_insert UN_compreh_bex UN_insert Un_assoc[symmetric] Un_empty_left
      Un_empty_right Union_Un_distrib collect_def[abs_def] fst_conv image_def o_apply snd_conv
      snd_prod_fun sum.cases sup_bot_right fst_map_pair map_pair_simp sum_map.simps};

(* These rules interfere with the "set_natural'" properties of "sum" and "prod", so we explicitly
   delay them. *)
val induct_prem_prem_thms_delayed =
  @{thms fsts_def[abs_def] snds_def[abs_def] sum_setl_def[abs_def] sum_setr_def[abs_def]};

(* TODO: Get rid of "auto_tac" (or at least use a naked context) *)
fun mk_induct_prem_prem_endgame_tac _ 0 = atac ORELSE' rtac @{thm singletonI}
  | mk_induct_prem_prem_endgame_tac ctxt qq =
    REPEAT_DETERM_N qq o
      (SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms Union_iff bex_simps(6)}) THEN'
       etac @{thm induct_set_step}) THEN'
    atac ORELSE' SELECT_GOAL (auto_tac ctxt);

fun mk_induct_discharge_prem_prems_tac ctxt nn ixs set_natural's pre_set_defs =
  EVERY' (maps (fn ((pp, jj), (qq, kk)) =>
      [select_prem_tac nn (dtac meta_spec) kk, etac meta_mp,
       SELECT_GOAL (Local_Defs.unfold_tac ctxt
         (pre_set_defs @ set_natural's @ induct_prem_prem_thms)),
       SELECT_GOAL (Local_Defs.unfold_tac ctxt
         (induct_prem_prem_thms_delayed @ induct_prem_prem_thms)),
       rtac (mk_UnIN pp jj) THEN' mk_induct_prem_prem_endgame_tac ctxt qq ORELSE'
         SELECT_GOAL (auto_tac ctxt)])
    (rev ixs)) 1;

fun mk_induct_discharge_prem_tac ctxt nn n set_natural's pre_set_defs m k ixs =
  EVERY [mk_induct_prepare_prem_tac n m k,
    mk_induct_prepare_prem_prems_tac (length ixs), atac 1,
    mk_induct_discharge_prem_prems_tac ctxt nn ixs set_natural's pre_set_defs];

fun mk_induct_tac ctxt ns mss ixsss ctr_defs fld_induct' set_natural's pre_set_defss =
  let
    val nn = length ns;
    val n = Integer.sum ns;
  in
    mk_induct_prelude_tac ctxt ctr_defs fld_induct' THEN
    EVERY (map4 (EVERY oooo map3 o mk_induct_discharge_prem_tac ctxt nn n set_natural's)
      pre_set_defss mss (unflat mss (1 upto n)) ixsss)
  end;

end;
