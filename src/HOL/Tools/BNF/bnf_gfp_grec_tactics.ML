(*  Title:      HOL/Tools/BNF/bnf_gfp_grec_tactics.ML
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Dmitriy Traytel, ETH Zurich
    Copyright   2015, 2016

Tactics for generalized corecursor construction.
*)

signature BNF_GFP_GREC_TACTICS =
sig
  val transfer_prover_eq_tac: Proof.context -> int -> tactic
  val transfer_prover_add_tac: Proof.context -> thm list -> thm list -> int -> tactic

  val mk_algLam_algLam_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    tactic
  val mk_algLam_algrho_tac: Proof.context -> thm -> thm -> tactic
  val mk_algLam_base_tac: Proof.context -> term -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm list -> thm -> thm list -> thm list -> thm -> thm -> tactic
  val mk_algLam_step_tac: Proof.context -> thm -> thm -> thm -> tactic
  val mk_cong_locale_tac: Proof.context -> thm -> thm list -> thm -> thm -> thm list -> thm ->
    thm -> tactic
  val mk_corecU_pointfree_tac: Proof.context -> thm -> thm -> thm list -> thm -> thm list -> thm ->
    thm list -> thm -> thm -> thm -> tactic
  val mk_corecUU_pointfree_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_corecUU_unique_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_corecUU_Inl_tac: Proof.context -> term -> thm -> thm -> thm -> thm -> thm list -> thm ->
    thm list -> thm -> thm -> thm -> thm -> tactic
  val mk_dtor_algLam_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm list ->
    thm -> thm -> thm list -> thm -> thm -> thm -> thm -> tactic
  val mk_dtor_algrho_tac: Proof.context -> thm -> thm -> thm -> thm -> tactic
  val mk_dtor_transfer_tac: Proof.context -> thm -> tactic
  val mk_equivp_Retr_tac: Proof.context -> thm -> thm -> thm -> thm -> tactic
  val mk_eval_core_embL_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm -> thm -> thm -> thm list -> thm list -> thm list -> thm -> tactic
  val mk_eval_core_flat_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm list -> thm -> thm list -> thm -> thm -> thm -> thm list -> tactic
  val mk_eval_core_k_as_ssig_tac: Proof.context -> thm -> thm -> thm -> thm list -> thm -> thm ->
    thm -> thm list -> tactic
  val mk_eval_embL_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_eval_flat_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    tactic
  val mk_eval_sctr_tac: Proof.context -> thm -> thm -> thm -> thm -> tactic
  val mk_eval_Oper_tac: Proof.context -> int -> thm -> thm -> thm -> thm -> thm -> thm list ->
    thm -> thm -> tactic
  val mk_eval_V_or_CLeaf_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm list -> thm ->
    tactic
  val mk_extdd_mor_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm -> thm -> thm -> tactic
  val mk_extdd_o_VLeaf_tac: Proof.context -> thm -> thm -> thm -> thm list -> thm list -> thm ->
    thm -> thm -> tactic
  val mk_flat_embL_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm list -> thm list ->
    thm list -> thm list -> tactic
  val mk_flat_VLeaf_or_flat_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_Lam_Inl_Inr_tac: Proof.context -> thm -> thm -> tactic
  val mk_mor_cutSsig_flat_tac: Proof.context -> term -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm list -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_natural_from_transfer_tac: Proof.context -> int -> bool list -> thm -> thm list ->
    thm list -> thm list -> tactic
  val mk_natural_by_unfolding_tac: Proof.context -> thm list -> tactic
  val mk_Retr_coinduct_tac: Proof.context -> thm -> thm -> tactic
  val mk_sig_transfer_tac: Proof.context -> thm -> thm list -> thm -> tactic
  val mk_transfer_by_transfer_prover_tac: Proof.context -> thm list -> thm list -> thm list ->
    tactic
end;

structure BNF_GFP_Grec_Tactics : BNF_GFP_GREC_TACTICS =
struct

open BNF_Util
open BNF_Tactics
open BNF_FP_Util

val o_assoc = @{thm o_assoc};
val o_def = @{thm o_def};

fun ss_only_silent thms ctxt =
  ss_only thms (ctxt |> Context_Position.set_visible false);

fun context_relator_eq_add rel_eqs ctxt =
  fold (snd oo Thm.proof_attributes (map (Attrib.attribute ctxt) @{attributes [relator_eq]}))
    rel_eqs ctxt;
val context_transfer_rule_add = fold (snd oo Thm.proof_attributes [Transfer.transfer_add]);

fun transfer_prover_eq_tac ctxt =
  SELECT_GOAL (Local_Defs.fold_tac ctxt (Transfer.get_relator_eq ctxt)) THEN'
  Transfer.transfer_prover_tac ctxt;

fun transfer_prover_add_tac ctxt rel_eqs transfers =
  transfer_prover_eq_tac (ctxt
    |> context_relator_eq_add rel_eqs
    |> context_transfer_rule_add transfers);

fun instantiate_natural_rule_with_id ctxt live =
  Rule_Insts.of_rule ctxt ([], NONE :: replicate live (SOME \<^const_name>\<open>id\<close>)) [];

fun instantiate_transfer_rule_with_Grp_UNIV ctxt alives thm =
  let
    val n = length alives;
    val fs = map (prefix "f" o string_of_int) (1 upto n);
    val ss = map2 (fn live => fn f => SOME (\<^const_name>\<open>BNF_Def.Grp\<close> ^ " " ^ \<^const_name>\<open>top\<close> ^
        " " ^ (if live then f else \<^const_name>\<open>id\<close>))) alives fs;
    val bs = map_filter (fn (live, f) => if live then SOME (Binding.name f, NONE, NoSyn) else NONE)
      (alives ~~ fs);
  in
    Rule_Insts.of_rule ctxt ([], ss) bs thm
  end;

fun mk_algLam_algLam_tac ctxt dead_pre_map_comp dtor_inject unsig sig_map Lam_def eval_embL
    old_dtor_algLam dtor_algLam =
  HEADGOAL (rtac ctxt ext THEN' rtac ctxt (dtor_inject RS iffD1)) THEN
  unfold_thms_tac ctxt (dead_pre_map_comp :: unsig :: sig_map :: Lam_def :: eval_embL ::
    old_dtor_algLam :: dtor_algLam :: @{thms o_apply id_o map_sum.simps sum.case}) THEN
  HEADGOAL (rtac ctxt refl);

fun mk_algLam_algrho_tac ctxt algLam_def algrho_def =
  HEADGOAL (rtac ctxt ext) THEN unfold_thms_tac ctxt [algLam_def, algrho_def, o_apply] THEN
  HEADGOAL (rtac ctxt refl);

fun mk_algLam_base_tac ctxt dead_pre_map_dtor dead_pre_map_id dead_pre_map_comp ctor_dtor dtor_ctor
    dtor_unfold_unique unsig Sig_pointful_natural ssig_maps Lam_def flat_simps eval_core_simps eval
    algLam_def =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt dead_pre_map_dtor)]
    (trans OF [dtor_unfold_unique, dtor_unfold_unique RS sym]) OF [ext, ext])) THEN
  ALLGOALS (asm_simp_tac (ss_only_silent (dead_pre_map_id :: ctor_dtor :: dtor_ctor :: unsig ::
    Sig_pointful_natural :: Lam_def :: eval :: algLam_def ::
    unfold_thms ctxt [o_def] dead_pre_map_comp :: ssig_maps @ flat_simps @ eval_core_simps @
    @{thms o_apply id_apply id_def[symmetric] snd_conv convol_apply}) ctxt));

fun mk_algLam_step_tac ctxt proto_sctr_def old_algLam_pointful algLam_algLam_pointful =
  HEADGOAL (rtac ctxt ext) THEN
  unfold_thms_tac ctxt [proto_sctr_def, old_algLam_pointful, algLam_algLam_pointful, o_apply] THEN
  HEADGOAL (rtac ctxt refl);

fun mk_cong_locale_tac ctxt dead_pre_rel_mono dead_pre_rel_maps equivp_Retr
    ssig_rel_mono ssig_rel_maps eval eval_core_transfer =
  HEADGOAL (resolve_tac ctxt (Locale.get_unfolds \<^context>) THEN'
    etac ctxt ssig_rel_mono THEN' etac ctxt equivp_Retr) THEN
  unfold_thms_tac ctxt (eval :: dead_pre_rel_maps @ @{thms id_apply}) THEN
  HEADGOAL (rtac ctxt (@{thm predicate2I} RS (dead_pre_rel_mono RS @{thm predicate2D})) THEN'
    etac ctxt @{thm rel_funD} THEN' assume_tac ctxt THEN'
    rtac ctxt (eval_core_transfer RS @{thm rel_funD})) THEN
  unfold_thms_tac ctxt (ssig_rel_maps @ @{thms vimage2p_rel_prod vimage2p_id}) THEN
  unfold_thms_tac ctxt @{thms vimage2p_def} THEN HEADGOAL (assume_tac ctxt);

fun mk_corecU_pointfree_tac ctxt dead_pre_map_comp dtor_unfold ssig_maps dead_ssig_map_comp0
    flat_simps flat_VLeaf eval_core_simps cutSsig_def mor_cutSsig_flat corecU_def =
  unfold_thms_tac ctxt [corecU_def, dead_ssig_map_comp0, o_assoc] THEN
  HEADGOAL (subst_tac ctxt NONE [ext RS mor_cutSsig_flat] THEN'
    asm_simp_tac (ss_only_silent [dtor_unfold, o_apply] ctxt) THEN'
    asm_simp_tac (ss_only_silent (dtor_unfold :: flat_VLeaf :: cutSsig_def :: ssig_maps @
      flat_simps @ eval_core_simps @ unfold_thms ctxt [o_def] dead_pre_map_comp ::
      @{thms o_def id_apply id_def[symmetric] snd_conv convol_apply}) ctxt));

fun mk_corecUU_tail_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_ctor ssig_map_comp
    flat_pointful_natural eval_core_pointful_natural eval eval_flat sctr_pointful_natural
    eval_sctr_pointful =
  asm_simp_tac (ss_only_silent (dtor_ctor :: flat_pointful_natural :: eval :: eval_flat ::
    map (unfold_thms ctxt [o_def]) [dead_pre_map_comp, ssig_map_comp] @
    @{thms o_apply id_apply id_def[symmetric] convol_apply}) ctxt) THEN'
  asm_simp_tac (ss_only_silent (eval_core_pointful_natural :: sctr_pointful_natural ::
    eval_sctr_pointful :: map (unfold_thms ctxt [o_def]) [dead_pre_map_comp0, ssig_map_comp] @
    @{thms id_apply id_def[symmetric] convol_apply map_prod_simp}) ctxt);

fun mk_corecUU_pointfree_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_ctor dtor_inject
    ssig_map_comp flat_pointful_natural eval_core_pointful_natural eval eval_flat corecU_ctor
    sctr_pointful_natural eval_sctr_pointful corecUU_def =
  unfold_thms_tac ctxt [corecUU_def] THEN
  HEADGOAL (rtac ctxt ext THEN' subst_tac ctxt NONE [corecU_ctor RS sym]) THEN
  unfold_thms_tac ctxt [corecUU_def RS symmetric_thm] THEN
  HEADGOAL (rtac ctxt (dtor_inject RS iffD1) THEN'
    mk_corecUU_tail_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_ctor ssig_map_comp
      flat_pointful_natural eval_core_pointful_natural eval eval_flat sctr_pointful_natural
      eval_sctr_pointful);

fun mk_corecUU_unique_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_ctor ssig_map_comp
    flat_pointful_natural eval_core_pointful_natural eval eval_flat corecU_unique
    sctr_pointful_natural eval_sctr_pointful corecUU_def prem =
  unfold_thms_tac ctxt [corecUU_def] THEN
  HEADGOAL (rtac ctxt corecU_unique THEN' rtac ctxt sym THEN' subst_tac ctxt NONE [prem] THEN'
    rtac ctxt ext THEN'
    mk_corecUU_tail_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_ctor ssig_map_comp
      flat_pointful_natural eval_core_pointful_natural eval eval_flat sctr_pointful_natural
      eval_sctr_pointful);

fun mk_corecUU_Inl_tac ctxt inl_case' pre_map_comp dead_pre_map_ident dead_pre_map_comp0 ctor_dtor
    ssig_maps ssig_map_id0 eval_core_simps eval_core_pointful_natural eval_VLeaf corecUU_pointfree
    corecUU_unique =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt inl_case')]
      (trans OF [corecUU_unique, corecUU_unique RS sym]) OF [ext, ext]) THEN'
    subst_tac ctxt NONE [corecUU_pointfree] THEN'
    asm_simp_tac (ss_only_silent (dead_pre_map_comp0 :: eval_core_pointful_natural :: ssig_maps @
      @{thms o_apply sum.case convol_apply id_apply map_prod_simp}) ctxt) THEN'
    asm_simp_tac (ss_only_silent (dead_pre_map_ident :: ctor_dtor :: ssig_map_id0 ::
        eval_core_pointful_natural :: eval_VLeaf :: unfold_thms ctxt [o_def] pre_map_comp ::
        ssig_maps @ eval_core_simps @ @{thms o_apply prod.map_id convol_apply snd_conv id_apply})
      ctxt));

fun mk_dtor_algLam_tac ctxt pre_map_comp dead_pre_map_id dead_pre_map_comp0 dead_pre_map_comp
    sig_map_comp Oper_pointful_natural ssig_maps dead_ssig_map_comp0 Lam_pointful_natural
    eval_core_simps eval eval_flat eval_VLeaf algLam_def =
  unfold_thms_tac ctxt [dead_ssig_map_comp0, o_assoc] THEN
  HEADGOAL (asm_simp_tac (ss_only_silent (sig_map_comp :: Oper_pointful_natural :: eval ::
      eval_flat :: algLam_def :: unfold_thms ctxt [o_def] dead_pre_map_comp :: eval_core_simps @
      @{thms o_apply id_apply id_def[symmetric]}) ctxt) THEN'
    asm_simp_tac (ss_only_silent (Lam_pointful_natural :: eval_VLeaf ::
      map (unfold_thms ctxt [o_def]) [dead_pre_map_comp0, sig_map_comp] @ ssig_maps @
      eval_core_simps @
      @{thms o_apply convol_apply snd_conv fst_conv id_apply map_prod_simp}) ctxt) THEN'
    asm_simp_tac (ss_only_silent (dead_pre_map_id :: eval_VLeaf ::
      unfold_thms ctxt [o_def] pre_map_comp ::
      @{thms id_apply id_def[symmetric] convol_def}) ctxt));

fun mk_dtor_algrho_tac ctxt eval k_as_ssig_natural_pointful eval_core_k_as_ssig algrho_def =
  HEADGOAL (asm_simp_tac (ss_only_silent [eval, k_as_ssig_natural_pointful, algrho_def,
    eval_core_k_as_ssig RS sym, o_apply] ctxt));

fun mk_dtor_transfer_tac ctxt dtor_rel =
  HEADGOAL (rtac ctxt refl ORELSE'
    rtac ctxt @{thm rel_funI} THEN' rtac ctxt (dtor_rel RS iffD1) THEN' assume_tac ctxt);

fun mk_equivp_Retr_tac ctxt dead_pre_rel_refl dead_pre_rel_flip dead_pre_rel_mono
    dead_pre_rel_compp =
  HEADGOAL (EVERY' [etac ctxt @{thm equivpE}, rtac ctxt @{thm equivpI},
    rtac ctxt @{thm reflpI}, rtac ctxt dead_pre_rel_refl, etac ctxt @{thm reflpD},
    SELECT_GOAL (unfold_thms_tac ctxt @{thms symp_iff}),
      REPEAT_DETERM o rtac ctxt ext, rtac ctxt (dead_pre_rel_flip RS sym RS trans),
      rtac ctxt ((@{thm conversep_iff} RS sym) RSN (2, trans)),
      asm_simp_tac (ss_only_silent @{thms conversep_eq} ctxt),
    SELECT_GOAL (unfold_thms_tac ctxt @{thms transp_relcompp}),
      rtac ctxt @{thm predicate2I}, etac ctxt @{thm relcomppE},
      etac ctxt (dead_pre_rel_mono RS @{thm rev_predicate2D[rotated -1]}),
      SELECT_GOAL (unfold_thms_tac ctxt
        (unfold_thms ctxt [@{thm eq_OO}] dead_pre_rel_compp :: @{thms relcompp_apply})),
      REPEAT_DETERM o resolve_tac ctxt [exI, conjI], assume_tac ctxt, assume_tac ctxt]);

fun mk_eval_core_k_as_ssig_tac ctxt pre_map_comp dead_pre_map_id sig_map_comp ssig_maps
    Lam_natural_pointful Lam_Inr flat_VLeaf eval_core_simps =
  HEADGOAL (asm_simp_tac (ss_only_silent (dead_pre_map_id :: flat_VLeaf :: (Lam_Inr RS sym) ::
    o_apply :: id_apply :: @{thm id_def[symmetric]} ::
    unfold_thms ctxt @{thms map_prod_def split_def} Lam_natural_pointful :: ssig_maps @
    eval_core_simps @ map (unfold_thms ctxt [o_def]) [pre_map_comp, sig_map_comp]) ctxt));

fun mk_eval_embL_tac ctxt dead_pre_map_comp0 dtor_unfold_unique embL_pointful_natural eval_core_embL
    old_eval eval =
  HEADGOAL (rtac ctxt (unfold_thms ctxt [o_apply]
      (trans OF [dtor_unfold_unique, dtor_unfold_unique RS sym] OF [ext, ext])
    OF [asm_rl, old_eval RS sym])) THEN
  unfold_thms_tac ctxt [dead_pre_map_comp0, embL_pointful_natural, eval_core_embL, eval,
    o_apply] THEN
  HEADGOAL (rtac ctxt refl);

fun mk_eval_flat_tac ctxt dead_pre_map_comp0 ssig_map_id ssig_map_comp flat_pointful_natural
    eval_core_pointful_natural eval_core_flat eval cond_eval_o_flat =
  HEADGOAL (rtac ctxt (unfold_thms ctxt [o_apply] cond_eval_o_flat)) THEN
  unfold_thms_tac ctxt [dead_pre_map_comp0, flat_pointful_natural, eval_core_flat, eval,
    o_apply] THEN
  HEADGOAL (rtac ctxt refl THEN'
    asm_simp_tac (ss_only_silent (ssig_map_id :: eval_core_pointful_natural :: eval ::
        map (unfold_thms ctxt [o_def]) [dead_pre_map_comp0, ssig_map_comp] @
        @{thms id_apply id_def[symmetric] fst_conv map_prod_simp convol_apply})
      ctxt));

fun instantiate_map_comp_with_f_g ctxt =
  Rule_Insts.of_rule ctxt ([], [NONE, SOME ("%x. f (g x)")])
    [(Binding.name "f", NONE, NoSyn), (Binding.name "g", NONE, NoSyn)];

fun mk_eval_core_embL_tac ctxt old_ssig_induct dead_pre_map_comp0 dead_pre_map_comp
    Sig_pointful_natural unsig_thm old_sig_map_comp old_sig_map_cong old_Lam_pointful_natural
    Lam_def flat_embL old_eval_core_simps eval_core_simps embL_simps embL_pointful_natural =
  HEADGOAL (rtac ctxt old_ssig_induct) THEN
  ALLGOALS (asm_simp_tac (ss_only_silent (Sig_pointful_natural :: unsig_thm :: Lam_def ::
    (flat_embL RS sym) :: unfold_thms ctxt [o_def] dead_pre_map_comp :: embL_simps @
    old_eval_core_simps @ eval_core_simps @
    @{thms id_apply id_def[symmetric] o_apply map_sum.simps sum.case}) ctxt)) THEN
  HEADGOAL (asm_simp_tac (Simplifier.add_cong old_sig_map_cong (ss_only_silent
    (old_Lam_pointful_natural :: embL_pointful_natural ::
     map (unfold_thms ctxt [o_def]) [dead_pre_map_comp0, instantiate_map_comp_with_f_g ctxt
       dead_pre_map_comp0, old_sig_map_comp] @ @{thms map_prod_simp}) ctxt)));

fun mk_eval_core_flat_tac ctxt ssig_induct dead_pre_map_id dead_pre_map_comp0 dead_pre_map_comp
    fp_map_id sig_map_comp sig_map_cong ssig_maps ssig_map_comp flat_simps flat_natural flat_flat
    Lam_natural_sym eval_core_simps =
  HEADGOAL (rtac ctxt ssig_induct) THEN
  ALLGOALS (full_simp_tac (ss_only_silent ((flat_flat RS sym) :: dead_pre_map_id ::
    dead_pre_map_comp :: fp_map_id :: sig_map_comp :: ssig_map_comp :: ssig_maps @ flat_simps @
    eval_core_simps @ @{thms o_def id_def[symmetric] convol_apply id_apply snd_conv}) ctxt)) THEN
  HEADGOAL (asm_simp_tac (Simplifier.add_cong sig_map_cong (ss_only_silent
      (map (unfold_thms ctxt [o_def]) [dead_pre_map_comp0, sig_map_comp] @
       flat_natural :: Lam_natural_sym :: @{thms id_apply fst_conv map_prod_simp})
    ctxt)));

fun mk_eval_sctr_tac ctxt proto_sctr_pointful_natural eval_Oper algLam sctr_def =
  HEADGOAL (rtac ctxt ext) THEN
  unfold_thms_tac ctxt [proto_sctr_pointful_natural, eval_Oper, algLam RS sym, sctr_def,
    o_apply] THEN
  HEADGOAL (rtac ctxt refl);

fun mk_eval_V_or_CLeaf_tac ctxt dead_pre_map_id dead_pre_map_comp fp_map_id dtor_unfold_unique
    V_or_CLeaf_map eval_core_simps eval =
  HEADGOAL (rtac ctxt (trans OF [dtor_unfold_unique, dtor_unfold_unique RS sym] RS fun_cong
    OF [ext, ext])) THEN
  ALLGOALS (asm_simp_tac (ss_only_silent (dead_pre_map_id :: fp_map_id ::
    unfold_thms ctxt @{thms o_def} dead_pre_map_comp :: V_or_CLeaf_map :: eval :: eval_core_simps @
    @{thms o_apply id_def[symmetric] id_apply snd_conv convol_apply}) ctxt));

fun mk_eval_Oper_tac ctxt live sig_map_ident sig_map_comp0 sig_map_comp Oper_natural_pointful
    VLeaf_natural flat_simps eval_flat algLam_def =
  let val VLeaf_natural' = instantiate_natural_rule_with_id ctxt live VLeaf_natural in
    unfold_thms_tac ctxt [sig_map_comp, VLeaf_natural', algLam_def, o_apply] THEN
    unfold_thms_tac ctxt (sig_map_comp0 :: Oper_natural_pointful :: (eval_flat RS sym) :: o_apply ::
      flat_simps) THEN
    unfold_thms_tac ctxt (@{thm id_apply} :: sig_map_ident :: unfold_thms ctxt [o_def] sig_map_comp ::
      flat_simps) THEN
    HEADGOAL (rtac ctxt refl)
  end;

fun mk_extdd_mor_tac ctxt dead_pre_map_comp0 dead_pre_map_comp VLeaf_map ssig_map_comp
    flat_pointful_natural eval_core_pointful_natural eval eval_flat eval_VLeaf cutSsig_def prem =
  HEADGOAL (rtac ctxt ext) THEN
  unfold_thms_tac ctxt (ssig_map_comp :: unfold_thms ctxt [o_def] dead_pre_map_comp ::
    flat_pointful_natural :: eval :: eval_flat :: cutSsig_def ::
    @{thms o_apply convol_o id_o id_apply id_def[symmetric]}) THEN
  unfold_thms_tac ctxt (unfold_thms ctxt [dead_pre_map_comp0] prem :: dead_pre_map_comp0 ::
    ssig_map_comp :: eval_core_pointful_natural ::
    @{thms o_def[symmetric] o_apply map_prod_o_convol}) THEN
  unfold_thms_tac ctxt (VLeaf_map :: eval_VLeaf :: @{thms o_def id_apply id_def[symmetric]}) THEN
  HEADGOAL (rtac ctxt refl);

fun mk_extdd_o_VLeaf_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_inject ssig_maps
    eval_core_simps eval eval_VLeaf prem =
  HEADGOAL (rtac ctxt ext THEN' rtac ctxt (dtor_inject RS iffD1) THEN'
    asm_simp_tac (ss_only_silent (dead_pre_map_comp0 :: ssig_maps @ eval_core_simps @ eval ::
      eval_VLeaf :: (mk_pointful ctxt prem RS sym) :: unfold_thms ctxt [o_def] dead_pre_map_comp ::
      @{thms o_apply convol_apply snd_conv id_apply}) ctxt));

fun mk_flat_embL_tac ctxt old_ssig_induct fp_map_id Sig_pointful_natural old_sig_map_comp
    old_sig_map_cong old_ssig_maps old_flat_simps flat_simps embL_simps =
  HEADGOAL (rtac ctxt old_ssig_induct) THEN
  ALLGOALS (asm_simp_tac (Simplifier.add_cong old_sig_map_cong (ss_only_silent
    (fp_map_id :: Sig_pointful_natural :: unfold_thms ctxt [o_def] old_sig_map_comp ::
     old_ssig_maps @ old_flat_simps @ flat_simps @ embL_simps @
     @{thms id_apply id_def[symmetric] map_sum.simps}) ctxt)));

fun mk_flat_VLeaf_or_flat_tac ctxt ssig_induct cong simps =
  HEADGOAL (rtac ctxt ssig_induct) THEN
  ALLGOALS (asm_simp_tac (Simplifier.add_cong cong (ss_only_silent simps ctxt)));

fun mk_Lam_Inl_Inr_tac ctxt unsig Lam_def =
  TRYALL Goal.conjunction_tac THEN ALLGOALS (rtac ctxt ext) THEN
  unfold_thms_tac ctxt (o_apply :: Lam_def :: unsig :: @{thms sum.case}) THEN
  ALLGOALS (rtac ctxt refl);

fun mk_mor_cutSsig_flat_tac ctxt eval_core_o_map dead_pre_map_comp0 dead_pre_map_comp
    dead_pre_map_cong dtor_unfold_unique dead_ssig_map_comp0 ssig_map_comp flat_simps
    flat_pointful_natural eval_core_pointful_natural flat_flat flat_VLeaf eval_core_flat cutSsig_def
    cutSsig_def_pointful_natural eval_thm prem =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt eval_core_o_map)]
    (trans OF [dtor_unfold_unique, dtor_unfold_unique RS sym]) OF [ext, ext]) THEN'
  asm_simp_tac (ss_only_silent ((prem RS sym) :: dead_pre_map_comp0 :: ssig_map_comp ::
    eval_core_pointful_natural :: eval_thm ::
    @{thms o_apply map_prod_o_convol o_id convol_o id_o}) ctxt) THEN'
  asm_simp_tac (ss_only_silent ((mk_pointful ctxt prem RS sym) :: dead_pre_map_comp0 ::
    cutSsig_def_pointful_natural :: flat_simps @
    @{thms o_apply convol_apply map_prod_simp id_apply}) ctxt) THEN'
  rtac ctxt (dead_pre_map_cong OF [asm_rl, refl]) THEN'
  asm_simp_tac (ss_only_silent (ssig_map_comp :: cutSsig_def :: flat_pointful_natural ::
    eval_core_flat :: unfold_thms ctxt [o_def] dead_pre_map_comp :: (dead_ssig_map_comp0 RS sym) ::
    (flat_flat RS sym) ::
    @{thms o_apply convol_o fst_convol id_apply id_def[symmetric]}) ctxt) THEN'
  asm_simp_tac (ss_only_silent (eval_core_pointful_natural :: flat_VLeaf ::
    map (unfold_thms ctxt [o_def]) [dead_pre_map_comp0, ssig_map_comp] @
    @{thms o_apply id_apply id_def[symmetric] map_prod_simp convol_def}) ctxt));

fun mk_natural_from_transfer_tac ctxt m alives transfer map_ids rel_Grps subst_rel_Grps =
  let
    val unfold_eq = unfold_thms ctxt @{thms Grp_UNIV_id[symmetric]};
    val (rel_Grps', subst_rel_Grps') =
      apply2 (map (fn thm => unfold_eq (thm RS eq_reflection))) (rel_Grps, subst_rel_Grps);
    val transfer' = instantiate_transfer_rule_with_Grp_UNIV ctxt alives (unfold_eq transfer)
      |> unfold_thms ctxt rel_Grps';
  in
    HEADGOAL (Method.insert_tac ctxt [transfer'] THEN'
      EVERY' (map (subst_asm_tac ctxt NONE o single) subst_rel_Grps')) THEN
    unfold_thms_tac ctxt (map_ids @ @{thms Grp_def rel_fun_def}) THEN
    HEADGOAL (REPEAT_DETERM_N m o rtac ctxt ext THEN'
      asm_full_simp_tac (ss_only_silent @{thms simp_thms id_apply o_apply mem_Collect_eq
        top_greatest UNIV_I subset_UNIV[simplified UNIV_def]} ctxt)) THEN
    ALLGOALS (REPEAT_DETERM o etac ctxt @{thm meta_allE} THEN' REPEAT_DETERM o etac ctxt allE THEN'
      forward_tac ctxt [sym] THEN' assume_tac ctxt)
  end;

fun mk_natural_by_unfolding_tac ctxt maps =
  HEADGOAL (rtac ctxt ext) THEN
  unfold_thms_tac ctxt (@{thms o_def[abs_def] id_apply id_def[symmetric]} @ maps) THEN
  HEADGOAL (rtac ctxt refl);

fun mk_Retr_coinduct_tac ctxt dtor_rel_coinduct rel_eq =
  HEADGOAL (EVERY' [rtac ctxt allI, rtac ctxt impI,
    rtac ctxt (@{thm ord_le_eq_trans} OF [dtor_rel_coinduct, rel_eq]),
    etac ctxt @{thm predicate2D}, assume_tac ctxt]);

fun mk_sig_transfer_tac ctxt pre_rel_def rel_eqs0 transfer =
  let
    val rel_eqs = no_refl rel_eqs0;
    val rel_eq_syms = map (fn thm => thm RS sym) rel_eqs;
    val transfer' = unfold_thms ctxt rel_eq_syms transfer
  in
    HEADGOAL (rtac ctxt transfer') ORELSE
    unfold_thms_tac ctxt (pre_rel_def :: rel_eq_syms @
      @{thms BNF_Def.vimage2p_def BNF_Composition.id_bnf_def}) THEN
    HEADGOAL (rtac ctxt transfer')
  end;

fun mk_transfer_by_transfer_prover_tac ctxt defs rel_eqs0 transfers =
  let
    val rel_eqs = no_refl rel_eqs0;
    val rel_eq_syms = map (fn thm => thm RS sym) rel_eqs;
  in
    unfold_thms_tac ctxt (defs @ rel_eq_syms) THEN
    HEADGOAL (transfer_prover_add_tac ctxt rel_eqs transfers)
  end;

end;
