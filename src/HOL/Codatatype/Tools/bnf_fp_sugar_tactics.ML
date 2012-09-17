(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for datatype and codatatype sugar.
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

fun inst_spurious_fs lthy thm =
  let
    val fs =
      Term.add_vars (prop_of thm) []
      |> filter (fn (_, Type (@{type_name fun}, [_, T'])) => T' <> HOLogic.boolT | _ => false);
    val cfs =
      map (fn f as (_, T) => (certify lthy (Var f), certify lthy (id_abs (domain_type T)))) fs;
  in
    Drule.cterm_instantiate cfs thm
  end;

val inst_spurious_fs_tac = PRIMITIVE o inst_spurious_fs;

fun mk_set_rhs set_lhs T =
  let
    val Type (_, Ts0) = domain_type (fastype_of set_lhs);
    val Type (_, Ts) = domain_type T;
  in
    Term.subst_atomic_types (Ts0 ~~ Ts) set_lhs
  end;

val mk_fsts_rhs = mk_set_rhs (snd (Logic.dest_equals (prop_of @{thm fsts_def[abs_def]})));
val mk_snds_rhs = mk_set_rhs (snd (Logic.dest_equals (prop_of @{thm snds_def[abs_def]})));
val mk_setl_rhs = mk_set_rhs (snd (Logic.dest_equals (prop_of @{thm sum_setl_def[abs_def]})));
val mk_setr_rhs = mk_set_rhs (snd (Logic.dest_equals (prop_of @{thm sum_setr_def[abs_def]})));

(* TODO: Put this in "Balanced_Tree" *)
fun balanced_tree_middle n = n div 2;

val sum_prod_sel_defs =
  @{thms fsts_def[abs_def] snds_def[abs_def] sum_setl_def[abs_def] sum_setr_def[abs_def]};

fun unfold_sum_prod_sets ctxt ms thm =
  let
    fun unf_prod 0 f = f
      | unf_prod 1 f = f
      | unf_prod m (t1 $ (t2 $ (t3 $ (t4 $ Const (_, T1) $ (t5 $ Const (_, T2) $ t6))))
          $ (t7 $ f $ g)) =
        t1 $ (t2 $ (t3 $ (t4 $ mk_fsts_rhs T1 $ (t5 $ mk_snds_rhs T2 $ t6))))
          $ (t7 $ f $ unf_prod (m - 1) g)
      | unf_prod _ f = f;
    fun unf_sum [m] f = unf_prod m f
      | unf_sum ms (t1 $ (t2 $ (t3 $ (t4 $ Const (_, T1) $ (t5 $ Const (_, T2) $ t6))))
          $ (t7 $ f $ g)) =
        let val (ms1, ms2) = chop (balanced_tree_middle (length ms)) ms in
          t1 $ (t2 $ (t3 $ (t4 $ mk_setl_rhs T1 $ (t5 $ mk_setr_rhs T2 $ t6))))
            $ (t7 $ unf_sum ms1 f $ unf_sum ms2 g)
        end
      | unf_sum _ f = f;

    val P = prop_of thm;
    val P' = Logic.dest_equals P ||> unf_sum ms;
    val goal = Logic.mk_implies (P, Logic.mk_equals P');
  in
    Skip_Proof.prove ctxt [] [] goal (fn {context = ctxt, ...} =>
      Local_Defs.unfold_tac ctxt sum_prod_sel_defs THEN atac 1)
    OF [thm]
  end;

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

val maybe_singletonI_tac = atac ORELSE' rtac @{thm singletonI};

fun mk_induct_prem_prem_endgame_tac _ 0 = maybe_singletonI_tac
  | mk_induct_prem_prem_endgame_tac ctxt qq =
    REPEAT_DETERM_N qq o
      (SELECT_GOAL (Local_Defs.unfold_tac ctxt
         @{thms trans[OF Union_iff bex_simps(6)] mem_compreh_eq_iff ex_mem_singleton}) THEN'
       eresolve_tac @{thms induct_set_step}) THEN' maybe_singletonI_tac;

fun gen_UN_comprehI_tac UnI = REPEAT_DETERM o resolve_tac @{thms mem_UN_comprehI} THEN' rtac UnI;

fun gen_UnIN_tac 1 1 = REPEAT_DETERM o resolve_tac @{thms mem_UN_comprehI'}
  | gen_UnIN_tac _ 1 = gen_UN_comprehI_tac @{thm UnI1} THEN' gen_UnIN_tac 1 1
  | gen_UnIN_tac n k = gen_UN_comprehI_tac @{thm UnI2} THEN' gen_UnIN_tac (n - 1) (k - 1);

val induct_prem_prem_thms =
  @{thms SUP_empty Sup_empty Sup_insert UN_compreh_bex_eq_empty UN_compreh_bex_eq_singleton
      UN_insert Un_assoc Un_empty_left Un_empty_right Union_Un_distrib collect_def[abs_def] fst_conv
      image_def o_apply snd_conv snd_prod_fun sum.cases sup_bot_right fst_map_pair map_pair_simp
      sum_map.simps};

fun mk_induct_leverage_prem_prems_tac ctxt nn ppjjqqkks set_natural's pre_set_defs =
  EVERY' (maps (fn ((pp, jj), (qq, kk)) =>
    [select_prem_tac nn (dtac meta_spec) kk, etac meta_mp,
     SELECT_GOAL (Local_Defs.unfold_tac ctxt
       (pre_set_defs @ set_natural's @ induct_prem_prem_thms)),
     gen_UnIN_tac pp jj, mk_induct_prem_prem_endgame_tac ctxt qq]) (rev ppjjqqkks)) 1;

fun mk_induct_discharge_prem_tac ctxt nn n set_natural's pre_set_defs m k ppjjqqkks =
  let val r = length ppjjqqkks in
    EVERY' [select_prem_tac n (rotate_tac 1) k, rotate_tac ~1, hyp_subst_tac,
      REPEAT_DETERM_N m o (dtac meta_spec THEN' rotate_tac ~1)] 1 THEN
    EVERY [REPEAT_DETERM_N r
        (rotate_tac ~1 1 THEN dtac meta_mp 1 THEN rotate_tac 1 1 THEN prefer_tac 2),
      if r > 0 then PRIMITIVE Raw_Simplifier.norm_hhf else all_tac, atac 1,
      mk_induct_leverage_prem_prems_tac ctxt nn ppjjqqkks set_natural's pre_set_defs]
  end;

fun mk_induct_tac ctxt ns mss ppjjqqkksss ctr_defs fld_induct' set_natural's pre_set_defss =
  let
    val nn = length ns;
    val n = Integer.sum ns;
    val pre_set_defss' = map2 (map o unfold_sum_prod_sets ctxt) mss pre_set_defss;
  in
    Local_Defs.unfold_tac ctxt ctr_defs THEN rtac fld_induct' 1 THEN inst_spurious_fs_tac ctxt THEN
    EVERY (map4 (EVERY oooo map3 o mk_induct_discharge_prem_tac ctxt nn n set_natural's)
      pre_set_defss' mss (unflat mss (1 upto n)) ppjjqqkksss)
  end;

end;
