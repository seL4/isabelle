(*  Title:      HOL/Tools/BNF/bnf_fp_def_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2012, 2013, 2014

Tactics for datatype and codatatype sugar.
*)

signature BNF_FP_DEF_SUGAR_TACTICS =
sig
  val sumprod_thms_rel: thm list

  val co_induct_inst_as_projs_tac: Proof.context -> int -> tactic
  val mk_case_transfer_tac: Proof.context -> thm -> thm list -> tactic
  val mk_coinduct_discharge_prem_tac: Proof.context -> thm list -> thm list -> int -> int -> int ->
    thm -> thm -> thm -> thm -> thm -> thm list -> thm list list -> thm list list -> int -> tactic
  val mk_coinduct_tac: Proof.context -> thm list -> int -> int list -> thm -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm list list -> thm list list list ->
    thm list list list -> tactic
  val mk_corec_tac: thm list -> thm list -> thm -> thm -> thm -> thm -> Proof.context -> tactic
  val mk_corec_disc_iff_tac: thm list -> thm list -> thm list -> Proof.context -> tactic
  val mk_co_rec_o_map_tac: Proof.context -> thm -> thm list -> thm list -> thm list -> thm -> thm ->
    thm Seq.seq
  val mk_corec_transfer_tac: Proof.context -> cterm list -> cterm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> ''a list -> ''a list list -> ''a list list list list ->
    ''a list list list list -> tactic
  val mk_ctor_iff_dtor_tac: Proof.context -> ctyp option list -> cterm -> cterm -> thm -> thm ->
    tactic
  val mk_ctr_transfer_tac: Proof.context -> thm list -> thm list -> tactic
  val mk_disc_transfer_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_exhaust_tac: Proof.context -> int -> thm list -> thm -> thm -> tactic
  val mk_half_distinct_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_induct_discharge_prem_tac: Proof.context -> int -> int -> thm list -> thm list ->
    thm list -> thm list -> int -> int -> int list -> tactic
  val mk_induct_tac: Proof.context -> int -> int list -> int list list -> int list list list ->
    thm list -> thm -> thm list -> thm list -> thm list -> thm list list -> tactic
  val mk_inject_tac: Proof.context -> thm -> thm -> thm -> tactic
  val mk_map_tac: Proof.context -> thm list -> thm -> thm -> thm list -> thm list -> thm list ->
    tactic
  val mk_map_disc_iff_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> tactic
  val mk_map_sel_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> thm list ->
    thm list -> tactic
  val mk_rec_tac: thm list -> thm list -> thm list -> thm -> thm -> thm -> thm -> Proof.context ->
    tactic
  val mk_rec_transfer_tac: Proof.context -> int -> int list -> cterm list -> cterm list ->
    term list list list list -> thm list -> thm list -> thm list -> thm list -> tactic
  val mk_rel_tac: Proof.context -> thm list -> thm -> thm -> thm list -> thm list -> thm list ->
    tactic
  val mk_rel_case_tac: Proof.context -> cterm -> cterm -> thm -> thm list -> thm list -> thm list ->
    thm list -> thm list -> tactic
  val mk_rel_coinduct0_tac: Proof.context -> thm -> cterm list -> thm list -> thm list ->
    thm list list -> thm list list -> thm list list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> tactic
  val mk_rel_induct0_tac: Proof.context -> thm -> thm list -> cterm list -> thm list ->
    thm list list -> thm list -> thm list -> thm list -> thm list -> tactic
  val mk_rel_sel_tac: Proof.context -> cterm -> cterm -> thm -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> tactic
  val mk_sel_transfer_tac: Proof.context -> int -> thm list -> thm -> tactic
  val mk_set0_tac: Proof.context -> thm list -> thm list -> thm -> thm list -> thm list ->
    thm list -> thm list -> thm list -> tactic
  val mk_set_cases_tac: Proof.context -> cterm -> thm list -> thm -> thm list -> tactic
  val mk_set_induct0_tac: Proof.context -> cterm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> tactic
  val mk_set_intros_tac: Proof.context -> thm list -> tactic
  val mk_set_sel_tac: Proof.context -> cterm -> thm -> thm list -> thm list -> thm list -> tactic
end;

structure BNF_FP_Def_Sugar_Tactics : BNF_FP_DEF_SUGAR_TACTICS =
struct

open Ctr_Sugar_Util
open BNF_Tactics
open BNF_Util
open BNF_FP_Util

val case_sum_transfer = @{thm case_sum_transfer};
val case_sum_transfer_eq = @{thm case_sum_transfer[of "(=)" _ "(=)", simplified sum.rel_eq]};
val case_prod_transfer = @{thm case_prod_transfer};
val case_prod_transfer_eq = @{thm case_prod_transfer[of "(=)" "(=)", simplified prod.rel_eq]};

val basic_simp_thms = @{thms simp_thms(7,8,12,14,22,24)};
val more_simp_thms = basic_simp_thms @ @{thms simp_thms(11,15,16,21)};
val simp_thms' = @{thms simp_thms(6,7,8,11,12,15,16,22,24)};

val sumprod_thms_map = @{thms id_apply map_prod_simp prod.case sum.case map_sum.simps};
val sumprod_thms_rel = @{thms rel_sum_simps rel_prod_inject prod.inject id_apply conj_assoc};
val basic_sumprod_thms_set =
  @{thms UN_empty UN_insert UN_iff Un_empty_left Un_empty_right Un_iff Union_Un_distrib o_apply
      map_prod_simp mem_Collect_eq prod_set_simps map_sum.simps sum_set_simps};
val sumprod_thms_set = @{thms UN_simps(10) image_iff} @ basic_sumprod_thms_set;

fun is_def_looping def =
  (case Thm.prop_of def of
    Const (\<^const_name>\<open>Pure.eq\<close>, _) $ lhs $ rhs => Term.exists_subterm (curry (op aconv) lhs) rhs
  | _ => false);

fun hhf_concl_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
    Conv.arg_conv (Conv.abs_conv (hhf_concl_conv cv o snd) ctxt) ct
  | _ => Conv.concl_conv ~1 cv ct);

fun co_induct_inst_as_projs ctxt k thm =
  let
    val fs = Term.add_vars (Thm.prop_of thm) []
      |> filter (fn (_, Type (\<^type_name>\<open>fun\<close>, [_, T'])) => T' <> HOLogic.boolT | _ => false);
    fun mk_inst (xi, T) = (xi, Thm.cterm_of ctxt (mk_proj T (num_binder_types T) k));
  in
    infer_instantiate ctxt (map mk_inst fs) thm
  end;

val co_induct_inst_as_projs_tac = PRIMITIVE oo co_induct_inst_as_projs;

fun mk_case_transfer_tac ctxt rel_case cases =
  let val n = length (tl (Thm.prems_of rel_case)) in
    REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
    HEADGOAL (etac ctxt rel_case) THEN
    ALLGOALS (hyp_subst_tac ctxt) THEN
    unfold_thms_tac ctxt cases THEN
    ALLGOALS (fn k => (select_prem_tac ctxt n (dtac ctxt asm_rl) k) k) THEN
    ALLGOALS (REPEAT_DETERM o (rotate_tac ~1 THEN' dtac ctxt rel_funD THEN'
      (assume_tac ctxt THEN' etac ctxt thin_rl ORELSE' rtac ctxt refl)) THEN' assume_tac ctxt)
  end;

fun mk_ctr_transfer_tac ctxt rel_intros rel_eqs =
  HEADGOAL Goal.conjunction_tac THEN
  ALLGOALS (REPEAT o (resolve_tac ctxt (rel_funI :: rel_intros) THEN'
    TRY o (REPEAT_DETERM1 o (SELECT_GOAL (unfold_thms_tac ctxt rel_eqs) THEN'
      (assume_tac ctxt ORELSE' hyp_subst_tac ctxt THEN' rtac ctxt refl)))));

fun mk_disc_transfer_tac ctxt rel_sel exhaust_disc distinct_disc =
  let
    fun last_disc_tac iffD =
      HEADGOAL (rtac ctxt (rotate_prems ~1 exhaust_disc) THEN' assume_tac ctxt THEN'
      REPEAT_DETERM o (rotate_tac ~1 THEN' dtac ctxt (rotate_prems 1 iffD) THEN'
        assume_tac ctxt THEN' rotate_tac ~1 THEN'
        etac ctxt (rotate_prems 1 notE) THEN' eresolve_tac ctxt distinct_disc));
  in
    HEADGOAL Goal.conjunction_tac THEN
    REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI THEN' dtac ctxt (rel_sel RS iffD1) THEN'
      REPEAT_DETERM o (etac ctxt conjE) THEN' (assume_tac ctxt ORELSE' rtac ctxt iffI))) THEN
    TRY (last_disc_tac iffD2) THEN TRY (last_disc_tac iffD1)
  end;

fun mk_exhaust_tac ctxt n ctr_defs ctor_iff_dtor sumEN' =
  unfold_thms_tac ctxt (ctor_iff_dtor :: ctr_defs) THEN HEADGOAL (rtac ctxt sumEN') THEN
  HEADGOAL (EVERY' (maps (fn k => [select_prem_tac ctxt n (rotate_tac 1) k,
    REPEAT_DETERM o dtac ctxt meta_spec, etac ctxt meta_mp, assume_tac ctxt]) (1 upto n)));

fun mk_ctor_iff_dtor_tac ctxt cTs cctor cdtor ctor_dtor dtor_ctor =
  HEADGOAL (rtac ctxt iffI THEN'
    EVERY' (@{map 3} (fn cTs => fn cx => fn th =>
      dtac ctxt (Thm.instantiate' cTs [NONE, NONE, SOME cx] arg_cong) THEN'
      SELECT_GOAL (unfold_thms_tac ctxt [th]) THEN'
      assume_tac ctxt) [rev cTs, cTs] [cdtor, cctor] [dtor_ctor, ctor_dtor]));

fun mk_half_distinct_tac ctxt ctor_inject abs_inject ctr_defs =
  unfold_thms_tac ctxt (ctor_inject :: abs_inject :: @{thms sum.inject} @ ctr_defs) THEN
  HEADGOAL (rtac ctxt @{thm sum.distinct(1)});

fun mk_inject_tac ctxt ctr_def ctor_inject abs_inject =
  unfold_thms_tac ctxt [ctr_def] THEN
  HEADGOAL (rtac ctxt (ctor_inject RS ssubst)) THEN
  unfold_thms_tac ctxt (abs_inject :: @{thms sum.inject prod.inject conj_assoc}) THEN
  HEADGOAL (rtac ctxt refl);

val rec_unfold_thms =
  @{thms comp_def convol_def fst_conv id_def case_prod_Pair_iden snd_conv split_conv
      case_unit_Unity} @ sumprod_thms_map;

fun mk_co_rec_o_map_tac ctxt co_rec_def pre_map_defs map_ident0s abs_inverses xtor_co_rec_o_map =
  let
    val rec_o_map_simps = @{thms o_def[abs_def] id_def case_prod_app case_sum_map_sum map_sum.simps
      case_prod_map_prod id_bnf_def map_prod_simp map_sum_if_distrib_then map_sum_if_distrib_else
      if_distrib[THEN sym]};
  in
    HEADGOAL (subst_tac ctxt (SOME [1, 2]) [co_rec_def] THEN'
      rtac ctxt (xtor_co_rec_o_map RS trans) THEN'
      CONVERSION Thm.eta_long_conversion THEN'
      asm_simp_tac (ss_only (pre_map_defs @ distinct Thm.eq_thm_prop (map_ident0s @ abs_inverses) @
        rec_o_map_simps) ctxt))
  end;

fun mk_rec_tac pre_map_defs map_ident0s rec_defs ctor_rec pre_abs_inverse abs_inverse ctr_def ctxt =
  HEADGOAL ((if is_def_looping ctr_def then subst_tac ctxt NONE
    else SELECT_GOAL o unfold_thms_tac ctxt) [ctr_def]) THEN
  unfold_thms_tac ctxt (ctor_rec :: pre_abs_inverse :: abs_inverse :: rec_defs @
    pre_map_defs @ map_ident0s @ rec_unfold_thms) THEN HEADGOAL (rtac ctxt refl);

fun mk_rec_transfer_tac ctxt nn ns actives passives xssss rec_defs ctor_rec_transfers rel_pre_T_defs
    rel_eqs =
  let
    val ctor_rec_transfers' =
      map (infer_instantiate' ctxt (map SOME (passives @ actives))) ctor_rec_transfers;
    val total_n = Integer.sum ns;
    val True = \<^term>\<open>True\<close>;
  in
    HEADGOAL Goal.conjunction_tac THEN
    EVERY (map (fn ctor_rec_transfer =>
        REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
        unfold_thms_tac ctxt rec_defs THEN
        HEADGOAL (etac ctxt (mk_rel_funDN_rotated (nn + 1) ctor_rec_transfer)) THEN
        unfold_thms_tac ctxt rel_pre_T_defs THEN
        EVERY (fst (@{fold_map 2} (fn k => fn xsss => fn acc =>
            rpair (k + acc)
            (HEADGOAL (rtac ctxt (mk_rel_funDN_rotated 2 @{thm comp_transfer})) THEN
             HEADGOAL (rtac ctxt @{thm vimage2p_rel_fun}) THEN
             unfold_thms_tac ctxt rel_eqs THEN
             EVERY (@{map 2} (fn n => fn xss =>
                 REPEAT_DETERM (HEADGOAL (resolve_tac ctxt
                   [mk_rel_funDN 2 case_sum_transfer_eq, mk_rel_funDN 2 case_sum_transfer])) THEN
                 HEADGOAL (select_prem_tac ctxt total_n (dtac ctxt asm_rl) (acc + n)) THEN
                 HEADGOAL (SELECT_GOAL (HEADGOAL
                   (REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt
                       [mk_rel_funDN 1 case_prod_transfer_eq,
                        mk_rel_funDN 1 case_prod_transfer,
                        rel_funI]) THEN_ALL_NEW
                    (Subgoal.FOCUS (fn {prems, ...} =>
                       let val thm = prems
                         |> permute_like (op =) (True :: flat xss) (True :: flat_rec_arg_args xss)
                         |> Library.foldl1 (fn (acc, elem) => elem RS (acc RS rel_funD))
                       in HEADGOAL (rtac ctxt thm) end) ctxt)))))
               (1 upto k) xsss)))
          ns xssss 0)))
      ctor_rec_transfers')
  end;

val corec_unfold_thms = @{thms id_def} @ sumprod_thms_map;

fun mk_corec_tac corec_defs map_ident0s ctor_dtor_corec pre_map_def abs_inverse ctr_def ctxt =
  let
    val ss = ss_only (pre_map_def :: abs_inverse :: map_ident0s @ corec_unfold_thms @
      @{thms o_apply vimage2p_def if_True if_False}) ctxt;
  in
    unfold_thms_tac ctxt (ctr_def :: corec_defs) THEN
    HEADGOAL (rtac ctxt (ctor_dtor_corec RS trans) THEN' asm_simp_tac ss) THEN_MAYBE
    HEADGOAL (rtac ctxt refl ORELSE' rtac ctxt (@{thm unit_eq} RS arg_cong))
  end;

fun mk_corec_disc_iff_tac case_splits' corecs discs ctxt =
  EVERY (@{map 3} (fn case_split_tac => fn corec_thm => fn disc =>
      HEADGOAL case_split_tac THEN unfold_thms_tac ctxt [corec_thm] THEN
      HEADGOAL (asm_simp_tac (ss_only basic_simp_thms ctxt)) THEN
      (if is_refl disc then all_tac else HEADGOAL (rtac ctxt disc)))
    (map (rtac ctxt) case_splits' @ [K all_tac]) corecs discs);

fun mk_corec_transfer_tac ctxt actives passives type_definitions corec_defs dtor_corec_transfers
    rel_pre_T_defs rel_eqs pgs pss qssss gssss =
  let
    val num_pgs = length pgs;
    fun prem_no_of x = 1 + find_index (curry (op =) x) pgs;

    val Inl_Inr_Pair_tac = REPEAT_DETERM o (resolve_tac ctxt
      [mk_rel_funDN 1 @{thm Inl_transfer},
       mk_rel_funDN 1 @{thm Inl_transfer[of "(=)" "(=)", simplified sum.rel_eq]},
       mk_rel_funDN 1 @{thm Inr_transfer},
       mk_rel_funDN 1 @{thm Inr_transfer[of "(=)" "(=)", simplified sum.rel_eq]},
       mk_rel_funDN 2 @{thm Pair_transfer},
       mk_rel_funDN 2 @{thm Pair_transfer[of "(=)" "(=)", simplified prod.rel_eq]}]);

    fun mk_unfold_If_tac total pos =
      HEADGOAL (Inl_Inr_Pair_tac THEN'
        rtac ctxt (mk_rel_funDN 3 @{thm If_transfer}) THEN'
        select_prem_tac ctxt total (dtac ctxt asm_rl) pos THEN'
        dtac ctxt rel_funD THEN' assume_tac ctxt THEN' assume_tac ctxt);

    fun mk_unfold_Inl_Inr_Pair_tac total pos =
      HEADGOAL (Inl_Inr_Pair_tac THEN'
        select_prem_tac ctxt total (dtac ctxt asm_rl) pos THEN'
        dtac ctxt rel_funD THEN' assume_tac ctxt THEN' assume_tac ctxt);

    fun mk_unfold_arg_tac qs gs =
      EVERY (map (mk_unfold_If_tac num_pgs o prem_no_of) qs) THEN
      EVERY (map (mk_unfold_Inl_Inr_Pair_tac num_pgs o prem_no_of) gs);

    fun mk_unfold_ctr_tac type_definition qss gss =
      HEADGOAL (rtac ctxt (mk_rel_funDN 1 (@{thm Abs_transfer} OF
        [type_definition, type_definition])) THEN' Inl_Inr_Pair_tac) THEN
      (case (qss, gss) of
        ([], []) => HEADGOAL (rtac ctxt refl)
      | _ => EVERY (map2 mk_unfold_arg_tac qss gss));

    fun mk_unfold_type_tac type_definition ps qsss gsss =
      let
        val p_tacs = map (mk_unfold_If_tac num_pgs o prem_no_of) ps;
        val qg_tacs = map2 (mk_unfold_ctr_tac type_definition) qsss gsss;
        fun mk_unfold_ty [] [qg_tac] = qg_tac
          | mk_unfold_ty (p_tac :: p_tacs) (qg_tac :: qg_tacs) =
            p_tac THEN qg_tac THEN mk_unfold_ty p_tacs qg_tacs
      in
        HEADGOAL (rtac ctxt rel_funI) THEN mk_unfold_ty p_tacs qg_tacs
      end;

    fun mk_unfold_corec_type_tac dtor_corec_transfer corec_def =
      let
        val active :: actives' = actives;
        val dtor_corec_transfer' =
          infer_instantiate' ctxt
            (SOME active :: map SOME passives @ map SOME actives') dtor_corec_transfer;
      in
        HEADGOAL Goal.conjunction_tac THEN REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
        unfold_thms_tac ctxt [corec_def] THEN
        HEADGOAL (etac ctxt (mk_rel_funDN_rotated (1 + length actives) dtor_corec_transfer')) THEN
        unfold_thms_tac ctxt (rel_pre_T_defs @ rel_eqs)
      end;

    fun mk_unfold_prop_tac dtor_corec_transfer corec_def =
      mk_unfold_corec_type_tac dtor_corec_transfer corec_def THEN
      EVERY (@{map 4} mk_unfold_type_tac type_definitions pss qssss gssss);
  in
    HEADGOAL Goal.conjunction_tac THEN
    EVERY (map2 mk_unfold_prop_tac dtor_corec_transfers corec_defs)
  end;

fun solve_prem_prem_tac ctxt =
  REPEAT o (eresolve_tac ctxt @{thms bexE rev_bexI} ORELSE'
    rtac ctxt @{thm rev_bexI[OF UNIV_I]} ORELSE' hyp_subst_tac ctxt ORELSE'
    resolve_tac ctxt @{thms disjI1 disjI2}) THEN'
  (rtac ctxt refl ORELSE' assume_tac ctxt ORELSE' rtac ctxt @{thm singletonI});

fun mk_induct_leverage_prem_prems_tac ctxt nn kks pre_abs_inverses abs_inverses set_maps
    pre_set_defs =
  HEADGOAL (EVERY' (maps (fn kk => [select_prem_tac ctxt nn (dtac ctxt meta_spec) kk,
    etac ctxt meta_mp,
    SELECT_GOAL (unfold_thms_tac ctxt (pre_set_defs @ pre_abs_inverses @ abs_inverses @ set_maps @
      sumprod_thms_set)),
    solve_prem_prem_tac ctxt]) (rev kks)));

fun mk_induct_discharge_prem_tac ctxt nn n pre_abs_inverses abs_inverses set_maps pre_set_defs m k
    kks =
  let val r = length kks in
    HEADGOAL (EVERY' [select_prem_tac ctxt n (rotate_tac 1) k, rotate_tac ~1, hyp_subst_tac ctxt,
      REPEAT_DETERM_N m o (dtac ctxt meta_spec THEN' rotate_tac ~1)]) THEN
    EVERY [REPEAT_DETERM_N r
        (HEADGOAL (rotate_tac ~1 THEN' dtac ctxt meta_mp THEN' rotate_tac 1) THEN prefer_tac 2),
      if r > 0 then ALLGOALS (Goal.norm_hhf_tac ctxt) else all_tac, HEADGOAL (assume_tac ctxt),
      mk_induct_leverage_prem_prems_tac ctxt nn kks pre_abs_inverses abs_inverses set_maps
        pre_set_defs]
  end;

fun mk_induct_tac ctxt nn ns mss kksss ctr_defs ctor_induct' pre_abs_inverses abs_inverses set_maps
    pre_set_defss =
  let val n = Integer.sum ns in
    (if exists is_def_looping ctr_defs then
       EVERY (map (fn def => HEADGOAL (subst_asm_tac ctxt NONE [def])) ctr_defs)
     else
       unfold_thms_tac ctxt ctr_defs) THEN
    HEADGOAL (rtac ctxt ctor_induct') THEN co_induct_inst_as_projs_tac ctxt 0 THEN
    EVERY (@{map 4} (EVERY oooo @{map 3} o
        mk_induct_discharge_prem_tac ctxt nn n pre_abs_inverses abs_inverses set_maps)
      pre_set_defss mss (unflat mss (1 upto n)) kksss)
  end;

fun mk_coinduct_same_ctr_tac ctxt rel_eqs pre_rel_def pre_abs_inverse abs_inverse dtor_ctor ctr_def
    discs sels extra_unfolds =
  hyp_subst_tac ctxt THEN'
  CONVERSION (hhf_concl_conv
    (Conv.top_conv (K (Conv.try_conv (Conv.rewr_conv ctr_def))) ctxt) ctxt) THEN'
  SELECT_GOAL (unfold_thms_tac ctxt (pre_rel_def :: dtor_ctor :: sels)) THEN'
  SELECT_GOAL (unfold_thms_tac ctxt (pre_rel_def :: pre_abs_inverse :: abs_inverse :: dtor_ctor ::
    sels @ sumprod_thms_rel @ extra_unfolds @ @{thms o_apply vimage2p_def})) THEN'
  (assume_tac ctxt ORELSE' REPEAT o etac ctxt conjE THEN'
     full_simp_tac (ss_only (no_refl discs @ rel_eqs @ more_simp_thms) ctxt) THEN'
     REPEAT o etac ctxt conjE THEN_MAYBE' REPEAT o hyp_subst_tac ctxt THEN'
     REPEAT o (resolve_tac ctxt [refl, conjI] ORELSE' assume_tac ctxt));

fun mk_coinduct_distinct_ctrs_tac ctxt discs discs' =
  let
    val discs'' = map (perhaps (try (fn th => th RS @{thm notnotD}))) (discs @ discs')
      |> distinct Thm.eq_thm_prop;
  in
    hyp_subst_tac ctxt THEN' REPEAT o etac ctxt conjE THEN'
    full_simp_tac (ss_only (refl :: no_refl discs'' @ basic_simp_thms) ctxt)
  end;

fun mk_coinduct_discharge_prem_tac ctxt extra_unfolds rel_eqs' nn kk n pre_rel_def pre_abs_inverse
    abs_inverse dtor_ctor exhaust ctr_defs discss selss =
  let val ks = 1 upto n in
    EVERY' ([rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
        select_prem_tac ctxt nn (dtac ctxt meta_spec) kk, dtac ctxt meta_spec, dtac ctxt meta_mp,
        assume_tac ctxt, rtac ctxt exhaust, K (co_induct_inst_as_projs_tac ctxt 0),
        hyp_subst_tac ctxt] @
      @{map 4} (fn k => fn ctr_def => fn discs => fn sels =>
        EVERY' ([rtac ctxt exhaust, K (co_induct_inst_as_projs_tac ctxt 1)] @
          map2 (fn k' => fn discs' =>
            if k' = k then
              mk_coinduct_same_ctr_tac ctxt rel_eqs' pre_rel_def pre_abs_inverse abs_inverse
                dtor_ctor ctr_def discs sels extra_unfolds
            else
              mk_coinduct_distinct_ctrs_tac ctxt discs discs') ks discss)) ks ctr_defs discss selss)
  end;

fun mk_coinduct_tac ctxt rel_eqs' nn ns dtor_coinduct' pre_rel_defs pre_abs_inverses abs_inverses
    dtor_ctors exhausts ctr_defss discsss selsss =
  HEADGOAL (rtac ctxt dtor_coinduct' THEN'
    EVERY' (@{map 10} (mk_coinduct_discharge_prem_tac ctxt [] rel_eqs' nn)
      (1 upto nn) ns pre_rel_defs pre_abs_inverses abs_inverses dtor_ctors exhausts ctr_defss
      discsss selsss));

fun mk_map_tac ctxt abs_inverses pre_map_def map_ctor live_nesting_map_id0s ctr_defs'
    extra_unfolds =
  TRYALL Goal.conjunction_tac THEN
  unfold_thms_tac ctxt (pre_map_def :: map_ctor :: abs_inverses @ live_nesting_map_id0s @
    ctr_defs' @ extra_unfolds @ sumprod_thms_map @
    @{thms o_apply id_apply id_o o_id}) THEN
  ALLGOALS (rtac ctxt refl);

fun mk_map_disc_iff_tac ctxt ct exhaust discs maps =
  TRYALL Goal.conjunction_tac THEN
  ALLGOALS (rtac ctxt (infer_instantiate' ctxt [SOME ct] exhaust) THEN_ALL_NEW
    REPEAT_DETERM o hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt maps THEN
  unfold_thms_tac ctxt (map (fn thm => thm RS eqFalseI
    handle THM _ => thm RS eqTrueI) discs) THEN
  ALLGOALS (rtac ctxt refl ORELSE' rtac ctxt TrueI);

fun mk_map_sel_tac ctxt ct exhaust discs maps sels map_id0s =
  TRYALL Goal.conjunction_tac THEN
  ALLGOALS (rtac ctxt (infer_instantiate' ctxt [SOME ct] exhaust) THEN_ALL_NEW
    REPEAT_DETERM o hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt ((discs RL [eqTrueI, eqFalseI]) @
    @{thms not_True_eq_False not_False_eq_True}) THEN
  TRYALL (etac ctxt FalseE ORELSE' etac ctxt @{thm TrueE}) THEN
  unfold_thms_tac ctxt (@{thm id_apply} :: maps @ sels @ map_id0s) THEN
  ALLGOALS (rtac ctxt refl);

fun mk_rel_tac ctxt abs_inverses pre_rel_def rel_ctor live_nesting_rel_eqs ctr_defs' extra_unfolds =
  TRYALL Goal.conjunction_tac THEN
  unfold_thms_tac ctxt (pre_rel_def :: rel_ctor :: abs_inverses @ live_nesting_rel_eqs @ ctr_defs' @
    extra_unfolds @ sumprod_thms_rel @ @{thms vimage2p_def o_apply sum.inject
      sum.distinct(1)[THEN eq_False[THEN iffD2]] not_False_eq_True}) THEN
  ALLGOALS (resolve_tac ctxt [TrueI, refl]);

fun mk_rel_case_tac ctxt ct1 ct2 exhaust injects rel_injects distincts rel_distincts rel_eqs =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt [SOME ct1] exhaust) THEN_ALL_NEW
    rtac ctxt (infer_instantiate' ctxt [SOME ct2] exhaust) THEN_ALL_NEW
      hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt (rel_eqs @ injects @ rel_injects @
    @{thms conj_imp_eq_imp_imp simp_thms(6) True_implies_equals} @
    map (fn thm => thm RS eqFalseI) (distincts @ rel_distincts) @
    map (fn thm => thm RS eqTrueI) rel_injects) THEN
  TRYALL (assume_tac ctxt ORELSE' etac ctxt FalseE ORELSE'
    (REPEAT_DETERM o dtac ctxt meta_spec THEN'
     TRY o filter_prems_tac ctxt
       (forall (curry (op <>) (HOLogic.mk_Trueprop \<^term>\<open>False\<close>)) o Logic.strip_imp_prems) THEN'
     REPEAT_DETERM o (dtac ctxt meta_mp THEN' rtac ctxt refl) THEN'
     (assume_tac ctxt ORELSE' Goal.assume_rule_tac ctxt)));

fun mk_rel_coinduct0_tac ctxt dtor_rel_coinduct cts assms exhausts discss selss ctor_defss
    dtor_ctors ctor_injects abs_injects rel_pre_defs abs_inverses nesting_rel_eqs =
  rtac ctxt dtor_rel_coinduct 1 THEN
   EVERY (@{map 11} (fn ct => fn assm => fn exhaust => fn discs => fn sels => fn ctor_defs =>
     fn dtor_ctor => fn ctor_inject => fn abs_inject => fn rel_pre_def => fn abs_inverse =>
      (rtac ctxt exhaust THEN_ALL_NEW (rtac ctxt exhaust THEN_ALL_NEW
         (dtac ctxt (rotate_prems ~1 (infer_instantiate' ctxt [NONE, NONE, NONE, NONE, SOME ct]
            @{thm arg_cong2} RS iffD1)) THEN'
          assume_tac ctxt THEN' assume_tac ctxt THEN' hyp_subst_tac ctxt THEN' dtac ctxt assm THEN'
          REPEAT_DETERM o etac ctxt conjE))) 1 THEN
      unfold_thms_tac ctxt ((discs RL [eqTrueI, eqFalseI]) @ sels @ simp_thms') THEN
      unfold_thms_tac ctxt (dtor_ctor :: rel_pre_def :: abs_inverse :: ctor_inject ::
        abs_inject :: ctor_defs @ nesting_rel_eqs @ simp_thms' @
        @{thms id_bnf_def rel_sum_simps rel_prod_inject vimage2p_def Inl_Inr_False
          iffD2[OF eq_False Inr_not_Inl] sum.inject prod.inject}) THEN
      REPEAT_DETERM (HEADGOAL ((REPEAT_DETERM o etac ctxt conjE) THEN'
        (REPEAT_DETERM o rtac ctxt conjI) THEN' (rtac ctxt refl ORELSE' assume_tac ctxt))))
    cts assms exhausts discss selss ctor_defss dtor_ctors ctor_injects abs_injects rel_pre_defs
      abs_inverses);

fun mk_rel_induct0_tac ctxt ctor_rel_induct assms cterms exhausts ctor_defss ctor_injects
    rel_pre_list_defs Abs_inverses nesting_rel_eqs =
  rtac ctxt ctor_rel_induct 1 THEN EVERY (@{map 6} (fn cterm => fn exhaust => fn ctor_defs =>
      fn ctor_inject => fn rel_pre_list_def => fn Abs_inverse =>
        HEADGOAL (rtac ctxt exhaust THEN_ALL_NEW (rtac ctxt exhaust THEN_ALL_NEW
          (rtac ctxt (infer_instantiate' ctxt (replicate 4 NONE @ [SOME cterm]) @{thm arg_cong2}
              RS iffD2)
            THEN' assume_tac ctxt THEN' assume_tac ctxt THEN' TRY o resolve_tac ctxt assms))) THEN
        unfold_thms_tac ctxt (ctor_inject :: rel_pre_list_def :: ctor_defs @ nesting_rel_eqs @
          @{thms id_bnf_def vimage2p_def}) THEN
        TRYALL (hyp_subst_tac ctxt) THEN
        unfold_thms_tac ctxt (Abs_inverse :: @{thms rel_sum_simps rel_prod_inject Inl_Inr_False
          Inr_Inl_False  sum.inject prod.inject}) THEN
        TRYALL (rtac ctxt refl ORELSE' etac ctxt FalseE ORELSE'
          (REPEAT_DETERM o etac ctxt conjE) THEN' assume_tac ctxt))
    cterms exhausts ctor_defss ctor_injects rel_pre_list_defs Abs_inverses);

fun mk_rel_sel_tac ctxt ct1 ct2 exhaust discs sels rel_injects distincts rel_distincts rel_eqs =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt [SOME ct1] exhaust) THEN_ALL_NEW
    rtac ctxt (infer_instantiate' ctxt [SOME ct2] exhaust) THEN_ALL_NEW hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt (sels @ rel_injects @ rel_eqs @
    @{thms simp_thms(6,7,8,11,12,15,16,21,22,24)} @ ((discs @ distincts) RL [eqTrueI, eqFalseI]) @
    (rel_injects RL [eqTrueI]) @ (rel_distincts RL [eqFalseI])) THEN
  TRYALL (resolve_tac ctxt [TrueI, refl]);

fun mk_sel_transfer_tac ctxt n sel_defs case_transfer =
  TRYALL Goal.conjunction_tac THEN
  unfold_thms_tac ctxt (map (Local_Defs.abs_def_rule ctxt) sel_defs) THEN
  ALLGOALS (rtac ctxt (mk_rel_funDN n case_transfer) THEN_ALL_NEW
    REPEAT_DETERM o (assume_tac ctxt ORELSE' rtac ctxt rel_funI));

fun mk_set0_tac ctxt abs_inverses pre_set_defs dtor_ctor fp_sets fp_nesting_set_maps
    live_nesting_set_maps ctr_defs' extra_unfolds =
  TRYALL Goal.conjunction_tac THEN
  unfold_thms_tac ctxt ctr_defs' THEN
  ALLGOALS (subst_tac ctxt NONE fp_sets) THEN
  unfold_thms_tac ctxt (dtor_ctor :: abs_inverses @ pre_set_defs @ fp_nesting_set_maps @
    live_nesting_set_maps @ extra_unfolds @ basic_sumprod_thms_set @
    @{thms UN_UN_flatten UN_Un_distrib UN_Un sup_assoc[THEN sym]}) THEN
  ALLGOALS (rtac ctxt @{thm set_eqI[OF iffI]}) THEN
  ALLGOALS (REPEAT_DETERM o etac ctxt @{thm UnE}) THEN
  ALLGOALS (REPEAT o resolve_tac ctxt @{thms UnI1 UnI2} THEN' assume_tac ctxt);

fun mk_set_sel_tac ctxt ct exhaust discs sels sets =
  TRYALL Goal.conjunction_tac THEN
  ALLGOALS (rtac ctxt (infer_instantiate' ctxt [SOME ct] exhaust) THEN_ALL_NEW
    REPEAT_DETERM o hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt ((discs RL [eqTrueI, eqFalseI]) @
    @{thms not_True_eq_False not_False_eq_True}) THEN
  TRYALL (etac ctxt FalseE ORELSE' etac ctxt @{thm TrueE}) THEN
  unfold_thms_tac ctxt (sels @ sets) THEN
  ALLGOALS (REPEAT o (resolve_tac ctxt @{thms UnI1 UnI2 imageI} ORELSE'
      eresolve_tac ctxt @{thms UN_I UN_I[rotated] imageE} ORELSE'
      hyp_subst_tac ctxt) THEN'
    (rtac ctxt @{thm singletonI} ORELSE' assume_tac ctxt));

fun mk_set_cases_tac ctxt ct assms exhaust sets =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt [SOME ct] exhaust)
    THEN_ALL_NEW hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt sets THEN
  REPEAT_DETERM (HEADGOAL
    (eresolve_tac ctxt @{thms FalseE emptyE singletonE UnE UN_E insertE} ORELSE'
     hyp_subst_tac ctxt ORELSE'
     SELECT_GOAL (SOLVE (HEADGOAL (eresolve_tac ctxt assms THEN' REPEAT_DETERM o
       assume_tac ctxt)))));

fun mk_set_intros_tac ctxt sets =
  TRYALL Goal.conjunction_tac THEN unfold_thms_tac ctxt sets THEN
  TRYALL (REPEAT o
    (resolve_tac ctxt @{thms UnI1 UnI2} ORELSE'
     eresolve_tac ctxt @{thms UN_I UN_I[rotated]}) THEN'
     (rtac ctxt @{thm singletonI} ORELSE' assume_tac ctxt));

fun mk_set_induct0_tac ctxt cts assms dtor_set_inducts exhausts set_pre_defs ctor_defs dtor_ctors
    Abs_pre_inverses =
  let
    val assms_tac =
      let val assms' = map (unfold_thms ctxt (@{thm id_bnf_def} :: ctor_defs)) assms in
        fold (curry (op ORELSE')) (map (fn thm =>
            funpow (Thm.nprems_of thm) (fn tac => tac THEN' assume_tac ctxt)
              (rtac ctxt thm)) assms')
          (etac ctxt FalseE)
      end;
    val exhausts' = map (fn thm => thm RS @{thm asm_rl[of "P x y" for P x y]}) exhausts
      |> map2 (fn ct => infer_instantiate' ctxt [NONE, SOME ct]) cts;
  in
    ALLGOALS (resolve_tac ctxt dtor_set_inducts) THEN
    TRYALL (resolve_tac ctxt exhausts' THEN_ALL_NEW
      (resolve_tac ctxt (map (fn ct => refl RS
         infer_instantiate' ctxt (replicate 4 NONE @ [SOME ct]) @{thm arg_cong2} RS iffD2) cts)
        THEN' assume_tac ctxt THEN' hyp_subst_tac ctxt)) THEN
    unfold_thms_tac ctxt (Abs_pre_inverses @ dtor_ctors @ set_pre_defs @ ctor_defs @
      @{thms id_bnf_def o_apply sum_set_simps prod_set_simps UN_empty UN_insert Un_empty_left
        Un_empty_right empty_iff singleton_iff}) THEN
    REPEAT (HEADGOAL (hyp_subst_tac ctxt ORELSE'
      eresolve_tac ctxt @{thms UN_E UnE singletonE} ORELSE' assms_tac))
  end;

end;
