(*  Title:      HOL/Tools/BNF/bnf_fp_def_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for datatype and codatatype sugar.
*)

signature BNF_FP_DEF_SUGAR_TACTICS =
sig
  val sumprod_thms_map: thm list
  val sumprod_thms_set: thm list
  val sumprod_thms_rel: thm list

  val mk_coinduct_tac: Proof.context -> thm list -> int -> int list -> thm -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm list list -> thm list list list ->
    thm list list list -> tactic
  val mk_corec_tac: thm list -> thm list -> thm -> thm -> thm -> thm -> Proof.context -> tactic
  val mk_ctor_iff_dtor_tac: Proof.context -> ctyp option list -> cterm -> cterm -> thm -> thm ->
    tactic
  val mk_disc_corec_iff_tac: thm list -> thm list -> thm list -> Proof.context -> tactic
  val mk_disc_map_iff_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> tactic
  val mk_exhaust_tac: Proof.context -> int -> thm list -> thm -> thm -> tactic
  val mk_half_distinct_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_induct_tac: Proof.context -> int -> int list -> int list list -> int list list list ->
    thm list -> thm -> thm list -> thm list -> thm list -> thm list list -> tactic
  val mk_inject_tac: Proof.context -> thm -> thm -> thm -> tactic
  val mk_rec_tac: thm list -> thm list -> thm list -> thm -> thm -> thm -> thm -> Proof.context ->
    tactic
  val mk_rel_cases_tac:  Proof.context -> cterm -> cterm -> thm -> thm list -> thm list ->
    thm list -> thm list -> tactic
  val mk_rel_coinduct0_tac: Proof.context -> thm -> cterm list -> thm list -> thm list ->
    thm list list -> thm list list -> thm list list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> tactic
  val mk_rel_induct0_tac: Proof.context -> thm -> thm list -> cterm list -> thm list ->
    thm list list -> thm list -> thm list -> thm list -> thm list -> tactic
  val mk_sel_map_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> thm list -> tactic
  val mk_sel_set_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> thm list -> tactic
  val mk_set_empty_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> tactic
end;

structure BNF_FP_Def_Sugar_Tactics : BNF_FP_DEF_SUGAR_TACTICS =
struct

open Ctr_Sugar_Util
open BNF_Tactics
open BNF_Util
open BNF_FP_Util

val basic_simp_thms = @{thms simp_thms(7,8,12,14,22,24)};
val more_simp_thms = basic_simp_thms @ @{thms simp_thms(11,15,16,21)};
val simp_thms' = @{thms simp_thms(6,7,8,11,12,15,16,22,24)};

val sumprod_thms_map = @{thms id_apply map_prod_simp prod.case sum.case map_sum.simps};
val sumprod_thms_set =
  @{thms UN_empty UN_insert Un_empty_left Un_empty_right Un_iff UN_simps(10) UN_iff
      Union_Un_distrib image_iff o_apply map_prod_simp
      mem_Collect_eq prod_set_simps map_sum.simps sum_set_simps};
val sumprod_thms_rel = @{thms rel_sum_simps rel_prod_apply prod.inject id_apply conj_assoc};

fun hhf_concl_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name Pure.all}, _) $ Abs _ =>
    Conv.arg_conv (Conv.abs_conv (hhf_concl_conv cv o snd) ctxt) ct
  | _ => Conv.concl_conv ~1 cv ct);

fun co_induct_inst_as_projs ctxt k thm =
  let
    val fs = Term.add_vars (prop_of thm) []
      |> filter (fn (_, Type (@{type_name fun}, [_, T'])) => T' <> HOLogic.boolT | _ => false);
    fun mk_cfp (f as (_, T)) =
      (certify ctxt (Var f), certify ctxt (mk_proj T (num_binder_types T) k));
    val cfps = map mk_cfp fs;
  in
    Drule.cterm_instantiate cfps thm
  end;

val co_induct_inst_as_projs_tac = PRIMITIVE oo co_induct_inst_as_projs;

fun mk_exhaust_tac ctxt n ctr_defs ctor_iff_dtor sumEN' =
  unfold_thms_tac ctxt (ctor_iff_dtor :: ctr_defs) THEN HEADGOAL (rtac sumEN') THEN
  HEADGOAL (EVERY' (maps (fn k => [select_prem_tac n (rotate_tac 1) k,
    REPEAT_DETERM o dtac meta_spec, etac meta_mp, atac]) (1 upto n)));

fun mk_ctor_iff_dtor_tac ctxt cTs cctor cdtor ctor_dtor dtor_ctor =
  HEADGOAL (rtac iffI THEN'
    EVERY' (map3 (fn cTs => fn cx => fn th =>
      dtac (Drule.instantiate' cTs [NONE, NONE, SOME cx] arg_cong) THEN'
      SELECT_GOAL (unfold_thms_tac ctxt [th]) THEN'
      atac) [rev cTs, cTs] [cdtor, cctor] [dtor_ctor, ctor_dtor]));

fun mk_half_distinct_tac ctxt ctor_inject abs_inject ctr_defs =
  unfold_thms_tac ctxt (ctor_inject :: abs_inject :: @{thms sum.inject} @ ctr_defs) THEN
  HEADGOAL (rtac @{thm sum.distinct(1)});

fun mk_inject_tac ctxt ctr_def ctor_inject abs_inject =
  unfold_thms_tac ctxt [ctr_def] THEN
  HEADGOAL (rtac (ctor_inject RS ssubst)) THEN
  unfold_thms_tac ctxt (abs_inject :: @{thms sum.inject prod.inject conj_assoc}) THEN
  HEADGOAL (rtac refl);

val rec_unfold_thms =
  @{thms comp_def convol_def fst_conv id_def case_prod_Pair_iden snd_conv split_conv
      case_unit_Unity} @ sumprod_thms_map;

fun mk_rec_tac pre_map_defs map_ident0s rec_defs ctor_rec fp_abs_inverse abs_inverse ctr_def ctxt =
  unfold_thms_tac ctxt (ctr_def :: ctor_rec :: fp_abs_inverse :: abs_inverse :: rec_defs @
    pre_map_defs @ map_ident0s @ rec_unfold_thms) THEN HEADGOAL (rtac refl);

val corec_unfold_thms = @{thms id_def} @ sumprod_thms_map;

fun mk_corec_tac corec_defs map_ident0s ctor_dtor_corec pre_map_def abs_inverse ctr_def ctxt =
  let
    val ss = ss_only (pre_map_def :: abs_inverse :: map_ident0s @ corec_unfold_thms @
      @{thms o_apply vimage2p_def if_True if_False}) ctxt;
  in
    unfold_thms_tac ctxt (ctr_def :: corec_defs) THEN
    HEADGOAL (rtac (ctor_dtor_corec RS trans) THEN' asm_simp_tac ss) THEN_MAYBE
    HEADGOAL (rtac refl ORELSE' rtac (@{thm unit_eq} RS arg_cong))
  end;

fun mk_disc_corec_iff_tac case_splits' corecs discs ctxt =
  EVERY (map3 (fn case_split_tac => fn corec_thm => fn disc =>
      HEADGOAL case_split_tac THEN unfold_thms_tac ctxt [corec_thm] THEN
      HEADGOAL (asm_simp_tac (ss_only basic_simp_thms ctxt)) THEN
      (if is_refl disc then all_tac else HEADGOAL (rtac disc)))
    (map rtac case_splits' @ [K all_tac]) corecs discs);

fun mk_disc_map_iff_tac ctxt ct exhaust discs maps =
  TRYALL Goal.conjunction_tac THEN
    ALLGOALS (rtac (cterm_instantiate_pos [SOME ct] exhaust) THEN_ALL_NEW
      REPEAT_DETERM o hyp_subst_tac ctxt) THEN
    unfold_thms_tac ctxt maps THEN
    unfold_thms_tac ctxt (map (fn thm => thm RS @{thm iffD2[OF eq_False]}
      handle THM _ => thm RS @{thm iffD2[OF eq_True]}) discs) THEN
    ALLGOALS (rtac refl ORELSE' rtac TrueI);

fun solve_prem_prem_tac ctxt =
  REPEAT o (eresolve_tac @{thms bexE rev_bexI} ORELSE' rtac @{thm rev_bexI[OF UNIV_I]} ORELSE'
    hyp_subst_tac ctxt ORELSE' resolve_tac @{thms disjI1 disjI2}) THEN'
  (rtac refl ORELSE' atac ORELSE' rtac @{thm singletonI});

fun mk_induct_leverage_prem_prems_tac ctxt nn kks fp_abs_inverses abs_inverses set_maps
    pre_set_defs =
  HEADGOAL (EVERY' (maps (fn kk => [select_prem_tac nn (dtac meta_spec) kk, etac meta_mp,
    SELECT_GOAL (unfold_thms_tac ctxt (pre_set_defs @ fp_abs_inverses @ abs_inverses @ set_maps @
      sumprod_thms_set)),
    solve_prem_prem_tac ctxt]) (rev kks)));

fun mk_induct_discharge_prem_tac ctxt nn n fp_abs_inverses abs_inverses set_maps pre_set_defs m k
    kks =
  let val r = length kks in
    HEADGOAL (EVERY' [select_prem_tac n (rotate_tac 1) k, rotate_tac ~1, hyp_subst_tac ctxt,
      REPEAT_DETERM_N m o (dtac meta_spec THEN' rotate_tac ~1)]) THEN
    EVERY [REPEAT_DETERM_N r
        (HEADGOAL (rotate_tac ~1 THEN' dtac meta_mp THEN' rotate_tac 1) THEN prefer_tac 2),
      if r > 0 then ALLGOALS (Goal.norm_hhf_tac ctxt) else all_tac, HEADGOAL atac,
      mk_induct_leverage_prem_prems_tac ctxt nn kks fp_abs_inverses abs_inverses set_maps
        pre_set_defs]
  end;

fun mk_induct_tac ctxt nn ns mss kkss ctr_defs ctor_induct' fp_abs_inverses abs_inverses set_maps
    pre_set_defss =
  let val n = Integer.sum ns in
    unfold_thms_tac ctxt ctr_defs THEN HEADGOAL (rtac ctor_induct') THEN
    co_induct_inst_as_projs_tac ctxt 0 THEN
    EVERY (map4 (EVERY oooo map3 o
        mk_induct_discharge_prem_tac ctxt nn n fp_abs_inverses abs_inverses set_maps)
      pre_set_defss mss (unflat mss (1 upto n)) kkss)
  end;

fun mk_coinduct_same_ctr_tac ctxt rel_eqs pre_rel_def fp_abs_inverse abs_inverse dtor_ctor ctr_def
    discs sels =
  hyp_subst_tac ctxt THEN'
  CONVERSION (hhf_concl_conv
    (Conv.top_conv (K (Conv.try_conv (Conv.rewr_conv ctr_def))) ctxt) ctxt) THEN'
  SELECT_GOAL (unfold_thms_tac ctxt (pre_rel_def :: dtor_ctor :: sels)) THEN'
  SELECT_GOAL (unfold_thms_tac ctxt (pre_rel_def :: fp_abs_inverse :: abs_inverse :: dtor_ctor ::
    sels @ sumprod_thms_rel @ @{thms o_apply vimage2p_def})) THEN'
  (atac ORELSE' REPEAT o etac conjE THEN'
     full_simp_tac (ss_only (no_refl discs @ rel_eqs @ more_simp_thms) ctxt) THEN'
     REPEAT o etac conjE THEN_MAYBE' REPEAT o hyp_subst_tac ctxt THEN'
     REPEAT o (resolve_tac [refl, conjI] ORELSE' atac));

fun mk_coinduct_distinct_ctrs_tac ctxt discs discs' =
  let
    val discs'' = map (perhaps (try (fn th => th RS @{thm notnotD}))) (discs @ discs')
      |> distinct Thm.eq_thm_prop;
  in
    hyp_subst_tac ctxt THEN' REPEAT o etac conjE THEN'
    full_simp_tac (ss_only (refl :: no_refl discs'' @ basic_simp_thms) ctxt)
  end;

fun mk_coinduct_discharge_prem_tac ctxt rel_eqs' nn kk n pre_rel_def fp_abs_inverse abs_inverse
    dtor_ctor exhaust ctr_defs discss selss =
  let val ks = 1 upto n in
    EVERY' ([rtac allI, rtac allI, rtac impI, select_prem_tac nn (dtac meta_spec) kk,
        dtac meta_spec, dtac meta_mp, atac, rtac exhaust, K (co_induct_inst_as_projs_tac ctxt 0),
        hyp_subst_tac ctxt] @
      map4 (fn k => fn ctr_def => fn discs => fn sels =>
        EVERY' ([rtac exhaust, K (co_induct_inst_as_projs_tac ctxt 1)] @
          map2 (fn k' => fn discs' =>
            if k' = k then
              mk_coinduct_same_ctr_tac ctxt rel_eqs' pre_rel_def fp_abs_inverse abs_inverse
                dtor_ctor ctr_def discs sels
            else
              mk_coinduct_distinct_ctrs_tac ctxt discs discs') ks discss)) ks ctr_defs discss selss)
  end;

fun mk_coinduct_tac ctxt rel_eqs' nn ns dtor_coinduct' pre_rel_defs fp_abs_inverses abs_inverses
    dtor_ctors exhausts ctr_defss discsss selsss =
  HEADGOAL (rtac dtor_coinduct' THEN'
    EVERY' (map10 (mk_coinduct_discharge_prem_tac ctxt rel_eqs' nn)
      (1 upto nn) ns pre_rel_defs fp_abs_inverses abs_inverses dtor_ctors exhausts ctr_defss discsss
      selsss));

fun mk_rel_cases_tac ctxt ct1 ct2 exhaust injects rel_injects distincts rel_distincts =
  HEADGOAL (rtac (cterm_instantiate_pos [SOME ct1] exhaust) THEN_ALL_NEW
    rtac (cterm_instantiate_pos [SOME ct2] exhaust) THEN_ALL_NEW
      hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt (injects @ rel_injects @ @{thms conj_imp_eq_imp_imp simp_thms(6)
    True_implies_equals conj_imp_eq_imp_imp} @
    map (fn thm => iffD2 OF [@{thm eq_False}, thm]) (distincts @ rel_distincts) @
    map (fn thm => thm RS @{thm eqTrueI}) rel_injects) THEN
  TRYALL (atac ORELSE' etac FalseE ORELSE' (REPEAT_DETERM o dtac @{thm meta_spec} THEN'
    REPEAT_DETERM o (dtac @{thm meta_mp} THEN' rtac refl) THEN' Goal.assume_rule_tac ctxt));

fun mk_rel_coinduct0_tac ctxt dtor_rel_coinduct cts assms exhausts discss selss ctor_defss
  dtor_ctors ctor_injects abs_injects rel_pre_defs abs_inverses nesting_rel_eqs =
  rtac dtor_rel_coinduct 1 THEN
  EVERY (map11 (fn ct => fn assm => fn exhaust => fn discs => fn sels => fn ctor_defs =>
    fn dtor_ctor => fn ctor_inject => fn abs_inject => fn rel_pre_def => fn abs_inverse =>
      (rtac exhaust THEN_ALL_NEW (rtac exhaust THEN_ALL_NEW
        (dtac (rotate_prems (~1) ((cterm_instantiate_pos [NONE, NONE, NONE, NONE, SOME ct] @{thm
        arg_cong2}) RS iffD1)) THEN'
        atac THEN' atac THEN' hyp_subst_tac ctxt THEN' dtac assm THEN'
        REPEAT_DETERM o etac conjE))) 1 THEN
      unfold_thms_tac ctxt ((discs RL @{thms iffD2[OF eq_True] iffD2[OF eq_False]}) @ sels
        @ simp_thms') THEN
      unfold_thms_tac ctxt (dtor_ctor :: rel_pre_def :: abs_inverse :: ctor_inject ::
        abs_inject :: ctor_defs @ nesting_rel_eqs @ simp_thms' @ @{thms BNF_Comp.id_bnf_comp_def
        rel_sum_simps rel_prod_apply vimage2p_def Inl_Inr_False iffD2[OF eq_False Inr_not_Inl]
        sum.inject prod.inject}) THEN
      REPEAT_DETERM (HEADGOAL ((REPEAT_DETERM o etac conjE) THEN' (REPEAT_DETERM o rtac conjI) THEN'
        (rtac refl ORELSE' atac))))
    cts assms exhausts discss selss ctor_defss dtor_ctors ctor_injects abs_injects rel_pre_defs
      abs_inverses);

fun mk_rel_induct0_tac ctxt ctor_rel_induct assms cterms exhausts ctor_defss ctor_injects
    rel_pre_list_defs Abs_inverses nesting_rel_eqs =
  rtac ctor_rel_induct 1 THEN EVERY (map6 (fn cterm => fn exhaust => fn ctor_defs =>
      fn ctor_inject => fn rel_pre_list_def => fn Abs_inverse =>
        HEADGOAL (rtac exhaust THEN_ALL_NEW (rtac exhaust THEN_ALL_NEW
          (rtac (cterm_instantiate_pos (replicate 4 NONE @ [SOME cterm]) @{thm arg_cong2} RS iffD2)
            THEN' atac THEN' atac THEN' TRY o resolve_tac assms))) THEN
        unfold_tac ctxt (ctor_inject :: rel_pre_list_def :: ctor_defs @ nesting_rel_eqs @
          @{thms BNF_Comp.id_bnf_comp_def vimage2p_def}) THEN
        TRYALL (hyp_subst_tac ctxt) THEN
        unfold_tac ctxt (Abs_inverse :: @{thms rel_sum_simps rel_prod_apply Inl_Inr_False
          Inr_Inl_False  sum.inject prod.inject}) THEN
        TRYALL (etac FalseE ORELSE' (REPEAT_DETERM o etac conjE) THEN' atac))
    cterms exhausts ctor_defss ctor_injects rel_pre_list_defs Abs_inverses);

fun mk_sel_map_tac ctxt ct exhaust discs maps sels =
  TRYALL Goal.conjunction_tac THEN
    ALLGOALS (rtac (cterm_instantiate_pos [SOME ct] exhaust) THEN_ALL_NEW
      REPEAT_DETERM o hyp_subst_tac ctxt) THEN
    unfold_thms_tac ctxt ((discs RL @{thms iffD2[OF eq_True] iffD2[OF eq_False]}) @
      @{thms not_True_eq_False not_False_eq_True}) THEN
    TRYALL (etac FalseE ORELSE' etac @{thm TrueE}) THEN
    unfold_thms_tac ctxt (maps @ sels) THEN
    ALLGOALS (rtac refl);

fun mk_sel_set_tac ctxt ct exhaust discs sels sets =
  TRYALL Goal.conjunction_tac THEN
    ALLGOALS (rtac (cterm_instantiate_pos [SOME ct] exhaust) THEN_ALL_NEW
      REPEAT_DETERM o hyp_subst_tac ctxt) THEN
    unfold_thms_tac ctxt ((discs RL @{thms iffD2[OF eq_True] iffD2[OF eq_False]}) @
      @{thms not_True_eq_False not_False_eq_True}) THEN
    TRYALL (etac FalseE ORELSE' etac @{thm TrueE}) THEN
    unfold_thms_tac ctxt (sels @ sets) THEN
    ALLGOALS (
      REPEAT o (resolve_tac @{thms UnI1 UnI2 imageI} ORELSE'
        eresolve_tac @{thms UN_I UN_I[rotated] imageE} ORELSE'
        hyp_subst_tac ctxt) THEN'
      (rtac @{thm singletonI} ORELSE' atac));

fun mk_set_empty_tac ctxt ct exhaust sets discs =
  TRYALL Goal.conjunction_tac THEN
  ALLGOALS (rtac (cterm_instantiate_pos [SOME ct] exhaust) THEN_ALL_NEW
    REPEAT_DETERM o hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt (sets @ map_filter (fn thm =>
    SOME (thm RS @{thm iffD2[OF eq_False]}) handle THM _ => NONE) discs) THEN
  ALLGOALS (rtac refl ORELSE' etac FalseE);

end;
