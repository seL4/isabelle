(*  Title:      HOL/Tools/BNF/bnf_gfp_grec_sugar_tactics.ML
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2016

Tactics for generalized corecursor sugar.
*)

signature BNF_GFP_GREC_SUGAR_TACTICS =
sig
  val rho_transfer_simps: thm list

  val mk_case_dtor_tac: Proof.context -> term -> thm -> thm -> thm list -> thm -> thm list -> tactic
  val mk_cong_intro_ctr_or_friend_tac: Proof.context -> thm -> thm list -> thm -> tactic
  val mk_code_tac: Proof.context -> int -> term list -> term -> term -> thm -> thm -> thm list ->
    thm list -> thm list -> thm list -> thm -> thm -> thm list -> thm list -> thm -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm list -> thm -> tactic
  val mk_eq_algrho_tac: Proof.context -> term list -> term -> term -> term -> term -> term -> thm ->
    thm -> thm list -> thm list -> thm list -> thm list -> thm -> thm -> thm -> thm list ->
    thm list -> thm list -> thm -> thm list -> thm list -> thm list -> thm -> thm -> thm -> thm ->
    thm list -> thm list -> thm list -> thm list -> thm list -> tactic
  val mk_eq_corecUU_tac: Proof.context -> int -> term list -> term -> term -> thm -> thm ->
    thm list -> thm list -> thm list -> thm list -> thm -> thm -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm list -> thm -> thm -> tactic
  val mk_last_disc_tac: Proof.context -> term -> thm -> thm list -> tactic
  val mk_rho_transfer_tac: Proof.context -> bool -> thm -> thm list -> tactic
  val mk_unique_tac: Proof.context -> int -> term list -> term -> term -> thm -> thm -> thm list ->
    thm list -> thm list -> thm list -> thm -> thm -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> thm -> thm -> tactic
end;

structure BNF_GFP_Grec_Sugar_Tactics : BNF_GFP_GREC_SUGAR_TACTICS =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Tactics
open BNF_FP_Def_Sugar_Tactics
open BNF_GFP_Grec_Tactics
open BNF_GFP_Grec_Sugar_Util

fun apply_func f =
  let
    val arg_Ts = binder_fun_types (fastype_of f);
    val args = map_index (fn (j, T) => Var (("a" ^ string_of_int j, 0), T)) arg_Ts;
  in
    list_comb (f, args)
  end;

fun instantiate_distrib thm ctxt t =
  infer_instantiate' ctxt [SOME (Thm.incr_indexes_cterm 1 (Thm.cterm_of ctxt t))] thm;

val mk_if_distrib_of = instantiate_distrib @{thm if_distrib};
val mk_case_sum_distrib_of = instantiate_distrib @{thm sum.case_distrib};

fun mk_case_dtor_tac ctxt u abs_inverse dtor_ctor ctr_defs exhaust cases =
  let val exhaust' = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt u)] exhaust in
    HEADGOAL (rtac ctxt exhaust') THEN
    REPEAT_DETERM (HEADGOAL (etac ctxt ssubst THEN'
      SELECT_GOAL (unfold_thms_tac ctxt cases THEN
        unfold_thms_tac ctxt (abs_inverse :: dtor_ctor :: ctr_defs @
        @{thms prod.case sum.case})) THEN'
      rtac ctxt refl))
  end;

fun mk_cong_intro_ctr_or_friend_tac ctxt ctr_or_friend_def extra_simps cong_alg_intro =
  HEADGOAL (REPEAT_DETERM_N 2 o subst_tac ctxt NONE [ctr_or_friend_def] THEN'
    rtac ctxt cong_alg_intro) THEN
  unfold_thms_tac ctxt (extra_simps @ sumprod_thms_rel @
    @{thms vimage2p_def prod.rel_eq sum.rel_eq}) THEN
  REPEAT_DETERM (HEADGOAL (rtac ctxt conjI ORELSE' assume_tac ctxt ORELSE' rtac ctxt refl ORELSE'
    etac ctxt subst));

val shared_simps =
  @{thms map_prod_simp map_sum.simps sum.case prod.case_eq_if split_beta' prod.sel
      sum.disc(1)[THEN eq_True[THEN iffD2]] sum.disc(2)[THEN eq_False[THEN iffD2]] sum.sel
      isl_map_sum map_sum_sel if_True if_False if_True_False Let_def[abs_def] o_def[abs_def] id_def
      BNF_Composition.id_bnf_def};

fun mk_code_tac ctxt num_args fpsig_nesting_maps ssig_map eval pre_map_def abs_inverse
    fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
    live_nesting_map_ident0s fp_map_ident case_trivial ctr_defs case_eq_ifs corecUU all_sig_maps
    ssig_map_thms all_algLam_alg_pointfuls all_algrho_eqs eval_simps inner_fp_simps fun_def =
  let
    val fun_def' =
      if null inner_fp_simps andalso num_args > 0 then
        HOLogic.mk_obj_eq fun_def RS (mk_curry_uncurryN_balanced ctxt num_args RS iffD2) RS sym
      else
        fun_def;
    val case_trivial' = unfold_thms ctxt (case_eq_ifs @ ctr_defs @ shared_simps) case_trivial;
    val case_eq_ifs' = map (Drule.abs_def o (fn thm => thm RS eq_reflection)) case_eq_ifs;
    val if_distribs = @{thm if_distrib_fun} :: map (mk_if_distrib_of ctxt)
      (eval :: map apply_func (ssig_map :: fpsig_nesting_maps));

    val unfold_tac = unfold_thms_tac ctxt (case_trivial' :: pre_map_def :: abs_inverse ::
      fp_map_ident :: (if null inner_fp_simps then [] else [corecUU]) @ fpsig_nesting_map_ident0s @
      fpsig_nesting_map_comps @ fpsig_nesting_map_thms @ live_nesting_map_ident0s @ ctr_defs @
      case_eq_ifs' @ all_sig_maps @ ssig_map_thms @ all_algLam_alg_pointfuls @ all_algrho_eqs @
      eval_simps @ if_distribs @ shared_simps);
  in
    HEADGOAL (subst_tac ctxt NONE [fun_def] THEN' subst_tac ctxt NONE [corecUU] THEN'
      (if null inner_fp_simps then K all_tac else subst_tac ctxt NONE inner_fp_simps)) THEN
    unfold_thms_tac ctxt [fun_def'] THEN
    unfold_tac THEN HEADGOAL (CONVERSION Thm.eta_long_conversion) THEN unfold_tac THEN
    HEADGOAL (rtac ctxt refl)
  end;

fun mk_eq_algrho_tac ctxt fpsig_nesting_maps abs rep ctor ssig_map eval pre_map_def abs_inverse
    fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
    live_nesting_map_ident0s fp_map_ident dtor_ctor ctor_iff_dtor ctr_defs nullary_disc_defs
    disc_sel_eq_cases case_dtor case_eq_ifs const_pointful_naturals fp_nesting_k_map_disc_sels'
    rho_def dtor_algrho corecUU_unique eq_corecUU all_sig_maps ssig_map_thms
    all_algLam_alg_pointfuls all_algrho_eqs eval_simps =
  let
    val nullary_disc_defs' = nullary_disc_defs
      |> map (fn thm => thm RS sym)
      |> maps (fn thm => [thm, thm RS @{thm subst[OF eq_commute, of "%e. e = z" for z]}]);

    val case_dtor' = unfold_thms ctxt shared_simps case_dtor;
    val disc_sel_eq_cases' = map (mk_abs_def
      o unfold_thms ctxt (case_dtor' :: ctr_defs @ shared_simps)) disc_sel_eq_cases;
    val extra_naturals = Facts.retrieve (Context.Proof ctxt) (Proof_Context.facts_of ctxt)
      ("friend_of_corec_simps", Position.none) |> #thms;
    val const_pointful_naturals' = map (unfold_thms ctxt shared_simps)
      (extra_naturals @ const_pointful_naturals);
    val const_pointful_naturals_sym' = map (fn thm => thm RS sym) const_pointful_naturals';
    val case_eq_ifs' = map mk_abs_def (@{thm sum.case_eq_if} :: case_eq_ifs);

    val distrib_consts =
      abs :: rep :: ctor :: eval :: map apply_func (ssig_map :: fpsig_nesting_maps);
    val if_distribs = @{thm if_distrib_fun} :: map (mk_if_distrib_of ctxt) distrib_consts;
    val case_sum_distribs = map (mk_case_sum_distrib_of ctxt) distrib_consts;

    val simp_ctxt = ctxt
      |> Context_Position.set_visible false
      |> put_simpset (simpset_of (Proof_Context.init_global \<^theory>\<open>Main\<close>))
      |> Simplifier.add_cong @{thm if_cong}
      |> Simplifier.add_simps (pre_map_def :: abs_inverse :: fp_map_ident :: dtor_ctor :: rho_def ::
        @{thm convol_def} :: fpsig_nesting_map_ident0s @ fpsig_nesting_map_comps @
        fpsig_nesting_map_thms @ live_nesting_map_ident0s @ ctr_defs @ disc_sel_eq_cases' @
        fp_nesting_k_map_disc_sels' @ case_eq_ifs' @ all_sig_maps @ ssig_map_thms @
        all_algLam_alg_pointfuls @ all_algrho_eqs @ eval_simps @ if_distribs @ case_sum_distribs @
        shared_simps);

    fun mk_main_simp const_pointful_naturals_maybe_sym' =
      simp_tac (simp_ctxt |> Simplifier.add_simps const_pointful_naturals_maybe_sym');
  in
    unfold_thms_tac ctxt [eq_corecUU] THEN
    HEADGOAL (REPEAT_DETERM o rtac ctxt ext THEN'
      rtac ctxt (corecUU_unique RS sym RS fun_cong) THEN'
      subst_tac ctxt NONE [dtor_algrho RS (ctor_iff_dtor RS iffD2)] THEN' rtac ctxt ext) THEN
    unfold_thms_tac ctxt (nullary_disc_defs' @ shared_simps) THEN
    HEADGOAL (rtac ctxt meta_eq_to_obj_eq) THEN
    REPEAT_DETERM_N (length const_pointful_naturals' + 1)
      (ALLGOALS (mk_main_simp const_pointful_naturals_sym') THEN
       ALLGOALS (mk_main_simp const_pointful_naturals'))
  end;

fun mk_eq_corecUU_tac ctxt num_args fpsig_nesting_maps ssig_map eval pre_map_def abs_inverse
    fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
    live_nesting_map_ident0s fp_map_ident case_trivial ctr_defs case_eq_ifs all_sig_maps
    ssig_map_thms all_algLam_alg_pointfuls all_algrho_eqs eval_simps corecUU_unique fun_code =
  let
    val case_trivial' = unfold_thms ctxt (case_eq_ifs @ ctr_defs @ shared_simps) case_trivial;
    val case_eq_ifs' = map (Drule.abs_def o (fn thm => thm RS eq_reflection)) case_eq_ifs;
    val if_distribs = @{thm if_distrib_fun} :: map (mk_if_distrib_of ctxt)
      (eval :: map apply_func (ssig_map :: fpsig_nesting_maps));

    val unfold_tac = unfold_thms_tac ctxt (case_trivial' :: pre_map_def :: abs_inverse ::
      fp_map_ident :: fpsig_nesting_map_ident0s @ fpsig_nesting_map_comps @ fpsig_nesting_map_thms @
      live_nesting_map_ident0s @ ctr_defs @ case_eq_ifs' @ all_sig_maps @ ssig_map_thms @
      all_algLam_alg_pointfuls @ all_algrho_eqs @ eval_simps @ if_distribs @ shared_simps);
  in
    HEADGOAL (rtac ctxt (mk_curry_uncurryN_balanced ctxt num_args RS iffD1) THEN'
      rtac ctxt corecUU_unique THEN' rtac ctxt ext) THEN
    unfold_thms_tac ctxt @{thms prod.case_eq_if} THEN
    HEADGOAL (rtac ctxt (fun_code RS trans)) THEN
    unfold_tac THEN HEADGOAL (CONVERSION Thm.eta_long_conversion) THEN unfold_tac THEN
    HEADGOAL (rtac ctxt refl)
  end;

fun mk_last_disc_tac ctxt u exhaust discs' =
  let val exhaust' = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt u)] exhaust in
    HEADGOAL (rtac ctxt exhaust') THEN
    REPEAT_DETERM (HEADGOAL (etac ctxt ssubst THEN'
      simp_tac (ss_only (distinct Thm.eq_thm discs' @ @{thms simp_thms}) ctxt)))
  end;

val rho_transfer_simps = @{thms BNF_Def.vimage2p_def[abs_def] BNF_Composition.id_bnf_def};

fun mk_rho_transfer_tac ctxt unfold rel_def const_transfers =
  (if unfold then unfold_thms_tac ctxt (rel_def :: rho_transfer_simps) else all_tac) THEN
  HEADGOAL (transfer_prover_add_tac ctxt [] const_transfers);

fun mk_unique_tac ctxt num_args fpsig_nesting_maps ssig_map eval pre_map_def abs_inverse
    fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
    live_nesting_map_ident0s fp_map_ident case_trivial ctr_defs case_eq_ifs all_sig_maps
    ssig_map_thms all_algLam_alg_pointfuls all_algrho_eqs eval_simps corecUU_unique eq_corecUU =
  let
    val case_trivial' = unfold_thms ctxt (case_eq_ifs @ ctr_defs @ shared_simps) case_trivial;
    val case_eq_ifs' = map (Drule.abs_def o (fn thm => thm RS eq_reflection)) case_eq_ifs;
    val if_distribs = @{thm if_distrib_fun} :: map (mk_if_distrib_of ctxt)
      (eval :: map apply_func (ssig_map :: fpsig_nesting_maps));

    val unfold_tac = unfold_thms_tac ctxt (case_trivial' :: pre_map_def :: abs_inverse ::
      fp_map_ident :: fpsig_nesting_map_ident0s @ fpsig_nesting_map_comps @ fpsig_nesting_map_thms @
      live_nesting_map_ident0s @ ctr_defs @ case_eq_ifs' @ all_sig_maps @ ssig_map_thms @
      all_algLam_alg_pointfuls @ all_algrho_eqs @ eval_simps @ if_distribs @ shared_simps);
  in
    HEADGOAL (subst_tac ctxt NONE [eq_corecUU] THEN'
      rtac ctxt (mk_curry_uncurryN_balanced ctxt num_args RS iffD1) THEN'
      rtac ctxt corecUU_unique THEN' rtac ctxt ext THEN'
      etac ctxt @{thm ssubst[of _ _ "\<lambda>x. f x = u" for f u]}) THEN
    unfold_tac THEN HEADGOAL (CONVERSION Thm.eta_long_conversion) THEN unfold_tac THEN
    HEADGOAL (rtac ctxt refl)
  end;

end;
