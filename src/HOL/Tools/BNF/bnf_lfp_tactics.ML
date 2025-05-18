(*  Title:      HOL/Tools/BNF/bnf_lfp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jan van Brügge, TU Muenchen
    Copyright   2012, 2022

Tactics for the datatype construction.
*)

signature BNF_LFP_TACTICS =
sig
  val mk_alg_min_alg_tac: Proof.context -> int -> thm -> thm list -> thm -> thm -> thm list list ->
    thm list -> thm list -> tactic
  val mk_alg_not_empty_tac: Proof.context -> thm -> thm list -> thm list -> tactic
  val mk_alg_select_tac: Proof.context -> thm -> tactic
  val mk_alg_set_tac: Proof.context -> thm -> tactic
  val mk_bd_card_order_tac: Proof.context -> thm list -> tactic
  val mk_bd_limit_tac: Proof.context -> int -> thm -> tactic
  val mk_card_of_min_alg_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_copy_tac: Proof.context -> int -> thm -> thm -> thm list -> thm list list -> tactic
  val mk_ctor_induct_tac: Proof.context -> int -> thm list list -> thm -> thm list -> thm ->
    thm list -> thm list -> thm list -> tactic
  val mk_ctor_induct2_tac: Proof.context -> ctyp option list -> cterm option list -> thm ->
    thm list -> tactic
  val mk_ctor_set_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_ctor_rec_transfer_tac: Proof.context -> int -> int -> thm list -> thm list -> thm list ->
    thm list -> tactic
  val mk_ctor_rel_tac: Proof.context -> thm list -> int -> thm -> thm -> thm -> thm -> thm list ->
    thm -> thm -> thm list -> thm list -> thm list list -> tactic
  val mk_dtor_o_ctor_tac: Proof.context -> thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_init_ex_mor_tac: Proof.context -> thm -> thm -> thm list -> thm -> thm -> thm -> thm ->
    tactic
  val mk_init_induct_tac: Proof.context -> int -> thm -> thm -> thm list -> thm list -> tactic
  val mk_init_unique_mor_tac: Proof.context -> cterm list -> int -> thm -> thm -> thm list ->
    thm list -> thm list -> thm list -> thm list -> tactic
  val mk_fold_unique_mor_tac: Proof.context -> thm list -> thm list -> thm list -> thm -> thm ->
    thm -> tactic
  val mk_fold_transfer_tac: Proof.context -> int -> thm -> thm list -> thm list -> tactic
  val mk_least_min_alg_tac: Proof.context -> thm -> thm -> tactic
  val mk_le_rel_OO_tac: Proof.context -> int -> thm -> thm list -> thm list -> thm list ->
    thm list -> tactic
  val mk_map_comp0_tac: Proof.context -> thm list -> thm list -> thm -> int -> tactic
  val mk_map_id0_tac: Proof.context -> thm list -> thm -> tactic
  val mk_map_tac: Proof.context -> int -> int -> thm -> thm -> thm -> tactic
  val mk_ctor_map_unique_tac: Proof.context -> thm -> thm list -> tactic
  val mk_mcong_tac: Proof.context -> (int -> tactic) -> thm list list list -> thm list ->
    thm list -> tactic
  val mk_min_algs_card_of_tac: Proof.context -> ctyp -> cterm -> int -> thm -> thm list ->
    thm list -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_min_algs_least_tac: Proof.context -> ctyp -> cterm -> thm -> thm list -> thm list -> tactic
  val mk_min_algs_mono_tac: Proof.context -> thm -> tactic
  val mk_min_algs_tac: Proof.context -> thm -> thm list -> tactic
  val mk_mor_Abs_tac: Proof.context -> cterm list -> thm list -> thm list -> thm list -> thm list ->
    tactic
  val mk_mor_Rep_tac: Proof.context -> int -> thm list -> thm list -> thm list -> thm -> thm list ->
    thm list list -> tactic
  val mk_mor_UNIV_tac: Proof.context -> int -> thm list -> thm -> tactic
  val mk_mor_comp_tac: Proof.context -> thm -> thm list list -> thm list -> tactic
  val mk_mor_elim_tac: Proof.context -> thm -> tactic
  val mk_mor_incl_tac: Proof.context -> thm -> thm list -> tactic
  val mk_mor_fold_tac: Proof.context -> ctyp -> cterm -> thm list -> thm -> thm -> tactic
  val mk_mor_select_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm list ->
    thm list list -> thm list -> tactic
  val mk_mor_str_tac: Proof.context -> 'a list -> thm -> tactic
  val mk_rel_induct_tac: Proof.context -> thm list -> int -> thm -> int list -> thm list ->
    thm list -> tactic
  val mk_rec_tac: Proof.context -> thm list -> thm -> thm list -> tactic
  val mk_rec_unique_mor_tac: Proof.context -> thm list -> thm list -> thm -> tactic
  val mk_set_bd_tac: Proof.context -> int -> (int -> tactic) -> thm -> thm -> thm list list ->
    thm list -> int -> tactic
  val mk_set_nat_tac: Proof.context -> int -> (int -> tactic) -> thm list list -> thm list ->
    cterm list -> thm list -> int -> tactic
  val mk_set_map0_tac: Proof.context -> thm -> tactic
  val mk_set_tac: Proof.context -> thm -> tactic
  val mk_wit_tac: Proof.context -> int -> thm list -> thm list -> tactic
end;

structure BNF_LFP_Tactics : BNF_LFP_TACTICS =
struct

open BNF_Tactics
open BNF_LFP_Util
open BNF_Util

val fst_snd_convs = @{thms fst_conv snd_conv};
val ord_eq_le_trans = @{thm ord_eq_le_trans};
val subset_trans = @{thm subset_trans};
val trans_fun_cong_image_id_id_apply = @{thm trans[OF fun_cong[OF image_id] id_apply]};
val rev_bspec = Drule.rotate_prems 1 @{thm bspec};
val Un_cong = @{thm arg_cong2[of _ _ _ _ "(\<union>)"]};
val relChainD = @{thm iffD2[OF meta_eq_to_obj_eq[OF relChain_def]]};

fun mk_alg_set_tac ctxt alg_def =
  EVERY' [dtac ctxt (alg_def RS iffD1), REPEAT_DETERM o etac ctxt conjE, etac ctxt @{thm bspec}, rtac ctxt @{thm CollectI},
   REPEAT_DETERM o (rtac ctxt (subset_UNIV RS conjI) ORELSE' etac ctxt conjI), assume_tac ctxt] 1;

fun mk_alg_not_empty_tac ctxt alg_set alg_sets wits =
  (EVERY' [rtac ctxt notI, hyp_subst_tac ctxt, forward_tac ctxt [alg_set]] THEN'
  REPEAT_DETERM o FIRST'
    [EVERY' [rtac ctxt @{thm subset_emptyI}, eresolve_tac ctxt wits],
    EVERY' [rtac ctxt @{thm subsetI}, rtac ctxt FalseE, eresolve_tac ctxt wits],
    EVERY' [rtac ctxt @{thm subsetI}, dresolve_tac ctxt wits, hyp_subst_tac ctxt,
      FIRST' (map (fn thm => rtac ctxt thm THEN' assume_tac ctxt) alg_sets)]] THEN'
  etac ctxt @{thm emptyE}) 1;

fun mk_mor_elim_tac ctxt mor_def =
  (dtac ctxt (mor_def RS iffD1) THEN'
  REPEAT o etac ctxt conjE THEN'
  TRY o rtac ctxt @{thm image_subsetI} THEN'
  etac ctxt @{thm bspec} THEN'
  assume_tac ctxt) 1;

fun mk_mor_incl_tac ctxt mor_def map_ids =
  (rtac ctxt (mor_def RS iffD2) THEN'
  rtac ctxt conjI THEN'
  CONJ_WRAP' (K (EVERY' [rtac ctxt @{thm ballI}, etac ctxt set_mp, etac ctxt (id_apply RS @{thm ssubst_mem})]))
    map_ids THEN'
  CONJ_WRAP' (fn thm =>
    (EVERY' [rtac ctxt @{thm ballI}, rtac ctxt trans, rtac ctxt id_apply, stac ctxt thm, rtac ctxt refl])) map_ids) 1;

fun mk_mor_comp_tac ctxt mor_def set_maps map_comp_ids =
  let
    val fbetw_tac =
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt (o_apply RS @{thm ssubst_mem}),
        etac ctxt @{thm bspec}, etac ctxt @{thm bspec}, assume_tac ctxt];
    fun mor_tac (set_map, map_comp_id) =
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt (o_apply RS trans), rtac ctxt trans,
        rtac ctxt trans, dtac ctxt rev_bspec, assume_tac ctxt, etac ctxt arg_cong,
         REPEAT o eresolve_tac ctxt @{thms CollectE conjE}, etac ctxt @{thm bspec}, rtac ctxt @{thm CollectI}] THEN'
      CONJ_WRAP' (fn thm =>
        FIRST' [rtac ctxt subset_UNIV,
          (EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt thm, rtac ctxt @{thm image_subsetI},
            etac ctxt @{thm bspec}, etac ctxt set_mp, assume_tac ctxt])]) set_map THEN'
      rtac ctxt (map_comp_id RS arg_cong);
  in
    (dtac ctxt (mor_def RS iffD1) THEN' dtac ctxt (mor_def RS iffD1) THEN' rtac ctxt (mor_def RS iffD2) THEN'
    REPEAT o etac ctxt conjE THEN'
    rtac ctxt conjI THEN'
    CONJ_WRAP' (K fbetw_tac) set_maps THEN'
    CONJ_WRAP' mor_tac (set_maps ~~ map_comp_ids)) 1
  end;

fun mk_mor_str_tac ctxt ks mor_def =
  (rtac ctxt (mor_def RS iffD2) THEN' rtac ctxt conjI THEN'
  CONJ_WRAP' (K (EVERY' [rtac ctxt @{thm ballI}, rtac ctxt @{thm UNIV_I}])) ks THEN'
  CONJ_WRAP' (K (EVERY' [rtac ctxt @{thm ballI}, rtac ctxt refl])) ks) 1;

fun mk_mor_UNIV_tac ctxt m morEs mor_def =
  let
    val n = length morEs;
    fun mor_tac morE = EVERY' [rtac ctxt @{thm ext}, rtac ctxt trans, rtac ctxt o_apply, rtac ctxt trans, etac ctxt morE,
      rtac ctxt @{thm CollectI}, CONJ_WRAP' (K (rtac ctxt subset_UNIV)) (1 upto m + n),
      rtac ctxt sym, rtac ctxt o_apply];
  in
    EVERY' [rtac ctxt iffI, CONJ_WRAP' mor_tac morEs,
    rtac ctxt (mor_def RS iffD2), rtac ctxt conjI, CONJ_WRAP' (K (rtac ctxt @{thm ballI} THEN' rtac ctxt @{thm UNIV_I})) morEs,
    REPEAT_DETERM o etac ctxt conjE, REPEAT_DETERM_N n o dtac ctxt (@{thm fun_eq_iff} RS iffD1),
    CONJ_WRAP' (K (EVERY' [rtac ctxt @{thm ballI}, REPEAT_DETERM o etac ctxt allE, rtac ctxt trans,
      etac ctxt (o_apply RS sym RS trans), rtac ctxt o_apply])) morEs] 1
  end;

fun mk_copy_tac ctxt m alg_def mor_def alg_sets set_mapss =
  let
    val n = length alg_sets;
    fun set_tac thm =
      EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt thm, rtac ctxt subset_trans, etac ctxt @{thm image_mono},
        rtac ctxt @{thm equalityD1}, etac ctxt @{thm bij_betw_imp_surj_on}];
    val alg_tac =
      CONJ_WRAP' (fn (set_maps, alg_set) =>
        EVERY' [rtac ctxt @{thm ballI}, REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, rtac ctxt set_mp,
          rtac ctxt @{thm equalityD1}, etac ctxt @{thm bij_betw_imp_surj_on[OF bij_betw_the_inv_into]},
          rtac ctxt @{thm imageI}, etac ctxt alg_set, EVERY' (map set_tac (drop m set_maps))])
      (set_mapss ~~ alg_sets);

    val mor_tac = rtac ctxt conjI THEN' CONJ_WRAP' (K (etac ctxt @{thm bij_betwE})) alg_sets THEN'
      CONJ_WRAP' (fn (set_maps, alg_set) =>
        EVERY' [rtac ctxt @{thm ballI}, REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE},
          etac ctxt @{thm f_the_inv_into_f_bij_betw}, etac ctxt alg_set,
          EVERY' (map set_tac (drop m set_maps))])
      (set_mapss ~~ alg_sets);
  in
    (REPEAT_DETERM_N n o rtac ctxt exI THEN' rtac ctxt conjI THEN'
    rtac ctxt (alg_def RS iffD2) THEN' alg_tac THEN' rtac ctxt (mor_def RS iffD2) THEN' mor_tac) 1
  end;

fun mk_bd_limit_tac ctxt n bd_Cinfinite =
  EVERY' [REPEAT_DETERM o etac ctxt conjE, rtac ctxt rev_mp, rtac ctxt @{thm Cinfinite_limit_finite},
    REPEAT_DETERM_N n o rtac ctxt @{thm finite.insertI}, rtac ctxt @{thm finite.emptyI},
    REPEAT_DETERM_N n o etac ctxt @{thm insert_subsetI}, rtac ctxt @{thm empty_subsetI},
    rtac ctxt bd_Cinfinite, rtac ctxt impI, etac ctxt @{thm bexE}, rtac ctxt @{thm bexI},
    CONJ_WRAP' (fn i =>
      EVERY' [etac ctxt @{thm bspec}, REPEAT_DETERM_N i o rtac ctxt @{thm insertI2}, rtac ctxt @{thm insertI1}])
      (0 upto n - 1),
    assume_tac ctxt] 1;

fun mk_min_algs_tac ctxt worel in_congs =
  let
    val minG_tac = EVERY' [rtac ctxt @{thm SUP_cong}, rtac ctxt refl, dtac ctxt @{thm bspec},
      assume_tac ctxt, etac ctxt arg_cong];
    fun minH_tac thm =
      EVERY' [rtac ctxt Un_cong, minG_tac, rtac ctxt @{thm image_cong}, rtac ctxt thm,
        REPEAT_DETERM_N (length in_congs) o minG_tac, rtac ctxt refl];
  in
    (rtac ctxt (worel RS (@{thm wo_rel.worec_fixpoint} RS fun_cong)) THEN' rtac ctxt iffD2 THEN'
    rtac ctxt meta_eq_to_obj_eq THEN' rtac ctxt (worel RS @{thm wo_rel.adm_wo_def}) THEN'
    REPEAT_DETERM_N 3 o rtac ctxt allI THEN' rtac ctxt impI THEN'
    CONJ_WRAP_GEN' (EVERY' [rtac ctxt prod_injectI, rtac ctxt conjI]) minH_tac in_congs) 1
  end;

fun mk_min_algs_mono_tac ctxt min_algs = EVERY' [rtac ctxt relChainD, rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
  rtac ctxt @{thm case_split}, rtac ctxt @{thm xt1(3)}, rtac ctxt min_algs, etac ctxt @{thm FieldI2}, rtac ctxt @{thm subsetI},
  rtac ctxt @{thm UnI1}, rtac ctxt @{thm UN_I}, etac ctxt @{thm underS_I}, assume_tac ctxt,
  assume_tac ctxt, rtac ctxt @{thm equalityD1}, dtac ctxt @{thm notnotD},
  hyp_subst_tac ctxt, rtac ctxt refl] 1;

fun mk_min_algs_card_of_tac ctxt cT ct m worel min_algs in_bds bd_Card_order bd_Cnotzero
  suc_Card_order suc_Cinfinite suc_Cnotzero suc_Asuc Asuc_Cinfinite =
  let
    val induct = worel RS
      Thm.instantiate' [SOME cT] [NONE, SOME ct] @{thm well_order_induct_imp};
    val src = 1 upto m + 1;
    val dest = (m + 1) :: (1 upto m);
    val absorbAs_tac = if m = 0 then K (all_tac)
      else EVERY' [rtac ctxt @{thm ordIso_transitive}, rtac ctxt @{thm csum_cong1},
        rtac ctxt @{thm ordIso_transitive},
        BNF_Tactics.mk_rotate_eq_tac ctxt (rtac ctxt @{thm ordIso_refl} THEN'
          FIRST' [rtac ctxt @{thm card_of_Card_order}, rtac ctxt @{thm Card_order_csum},
            rtac ctxt @{thm Card_order_cexp}])
        @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_com} @{thm csum_cong}
        src dest,
        rtac ctxt @{thm csum_absorb1}, rtac ctxt Asuc_Cinfinite, rtac ctxt ctrans, rtac ctxt @{thm ordLeq_csum1},
        FIRST' [rtac ctxt @{thm Card_order_csum}, rtac ctxt @{thm card_of_Card_order}],
        rtac ctxt @{thm ordLeq_cexp1}, rtac ctxt suc_Cnotzero, rtac ctxt @{thm Card_order_csum}];

    val minG_tac = EVERY' [rtac ctxt @{thm UNION_Cinfinite_bound}, rtac ctxt @{thm ordLess_imp_ordLeq},
      rtac ctxt @{thm ordLess_transitive}, rtac ctxt @{thm card_of_underS}, rtac ctxt suc_Card_order,
      assume_tac ctxt, rtac ctxt suc_Asuc, rtac ctxt @{thm ballI}, etac ctxt allE,
      dtac ctxt mp, etac ctxt @{thm underS_E},
      dtac ctxt mp, etac ctxt @{thm underS_Field},
      REPEAT o etac ctxt conjE, assume_tac ctxt, rtac ctxt Asuc_Cinfinite]

    fun mk_minH_tac (min_alg, in_bd) = EVERY' [rtac ctxt @{thm ordIso_ordLeq_trans},
      rtac ctxt @{thm card_of_ordIso_subst}, etac ctxt min_alg, rtac ctxt @{thm Un_Cinfinite_bound},
      minG_tac, rtac ctxt ctrans, rtac ctxt @{thm card_of_image}, rtac ctxt ctrans, rtac ctxt in_bd, rtac ctxt ctrans,
      rtac ctxt @{thm cexp_mono1}, rtac ctxt @{thm csum_mono1},
      REPEAT_DETERM_N m o rtac ctxt @{thm csum_mono2},
      CONJ_WRAP_GEN' (rtac ctxt @{thm csum_cinfinite_bound}) (K minG_tac) min_algs,
      REPEAT_DETERM o FIRST'
        [rtac ctxt @{thm card_of_Card_order}, rtac ctxt @{thm Card_order_csum},
        rtac ctxt Asuc_Cinfinite, rtac ctxt bd_Card_order],
      rtac ctxt @{thm ordIso_ordLeq_trans}, rtac ctxt @{thm cexp_cong1}, absorbAs_tac,
      rtac ctxt @{thm csum_absorb1}, rtac ctxt Asuc_Cinfinite, rtac ctxt @{thm ctwo_ordLeq_Cinfinite},
      rtac ctxt Asuc_Cinfinite, rtac ctxt bd_Card_order,
      rtac ctxt @{thm ordIso_imp_ordLeq}, rtac ctxt @{thm cexp_cprod_ordLeq},
      resolve_tac ctxt @{thms Card_order_csum Card_order_ctwo}, rtac ctxt suc_Cinfinite,
      rtac ctxt bd_Cnotzero, rtac ctxt @{thm cardSuc_ordLeq}, rtac ctxt bd_Card_order, rtac ctxt Asuc_Cinfinite];
  in
    (rtac ctxt induct THEN'
    rtac ctxt impI THEN'
    CONJ_WRAP' mk_minH_tac (min_algs ~~ in_bds)) 1
  end;

fun mk_min_algs_least_tac ctxt cT ct worel min_algs alg_sets =
  let
    val induct = worel RS
      Thm.instantiate' [SOME cT] [NONE, SOME ct] @{thm well_order_induct_imp};

    val minG_tac =
      EVERY' [rtac ctxt @{thm UN_least}, etac ctxt allE, dtac ctxt mp, etac ctxt @{thm underS_E},
        dtac ctxt mp, etac ctxt @{thm underS_Field}, REPEAT_DETERM o etac ctxt conjE, assume_tac ctxt];

    fun mk_minH_tac (min_alg, alg_set) = EVERY' [rtac ctxt ord_eq_le_trans, etac ctxt min_alg,
      rtac ctxt @{thm Un_least}, minG_tac, rtac ctxt @{thm image_subsetI},
      REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, etac ctxt alg_set,
      REPEAT_DETERM o (etac ctxt subset_trans THEN' minG_tac)];
  in
    (rtac ctxt induct THEN'
    rtac ctxt impI THEN'
    CONJ_WRAP' mk_minH_tac (min_algs ~~ alg_sets)) 1
  end;

fun mk_alg_min_alg_tac ctxt m alg_def min_alg_defs bd_limit bd_Cinfinite
    set_bdss min_algs min_alg_monos =
  let
    val n = length min_algs;
    fun mk_cardSuc_UNION_tac set_bds (mono, def) = EVERY'
      [rtac ctxt @{thm bexE}, rtac ctxt @{thm cardSuc_UNION_Cinfinite}, rtac ctxt bd_Cinfinite, rtac ctxt mono,
       etac ctxt (def RSN (2, @{thm subset_trans[OF _ equalityD1]})), resolve_tac ctxt set_bds];
    fun mk_conjunct_tac (set_bds, (min_alg, min_alg_def)) =
      EVERY' [rtac ctxt @{thm ballI}, REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE},
        EVERY' (map (mk_cardSuc_UNION_tac set_bds) (min_alg_monos ~~ min_alg_defs)), rtac ctxt @{thm bexE},
        rtac ctxt bd_limit, REPEAT_DETERM_N (n - 1) o etac ctxt conjI, assume_tac ctxt,
        rtac ctxt (min_alg_def RS @{thm set_mp[OF equalityD2]}),
        rtac ctxt @{thm UN_I}, REPEAT_DETERM_N (m + 3 * n) o etac ctxt thin_rl,
        assume_tac ctxt, rtac ctxt set_mp,
        rtac ctxt @{thm equalityD2}, rtac ctxt min_alg, assume_tac ctxt, rtac ctxt @{thm UnI2},
        rtac ctxt @{thm image_eqI}, rtac ctxt refl,
        rtac ctxt @{thm CollectI}, REPEAT_DETERM_N m o dtac ctxt asm_rl, REPEAT_DETERM_N n o etac ctxt thin_rl,
        REPEAT_DETERM o etac ctxt conjE,
        CONJ_WRAP' (K (FIRST' [assume_tac ctxt,
          EVERY' [etac ctxt subset_trans, rtac ctxt @{thm subsetI}, rtac ctxt @{thm UN_I},
            etac ctxt @{thm underS_I}, assume_tac ctxt, assume_tac ctxt]]))
          set_bds];
  in
    (rtac ctxt (alg_def RS iffD2) THEN'
    CONJ_WRAP' mk_conjunct_tac (set_bdss ~~ (min_algs ~~ min_alg_defs))) 1
  end;

fun mk_card_of_min_alg_tac ctxt min_alg_def card_of suc_Card_order suc_Asuc Asuc_Cinfinite =
  EVERY' [rtac ctxt @{thm ordIso_ordLeq_trans}, rtac ctxt (min_alg_def RS @{thm card_of_ordIso_subst}),
    rtac ctxt @{thm UNION_Cinfinite_bound}, rtac ctxt @{thm ordIso_ordLeq_trans},
    rtac ctxt @{thm card_of_Field_ordIso}, rtac ctxt suc_Card_order, rtac ctxt @{thm ordLess_imp_ordLeq},
    rtac ctxt suc_Asuc, rtac ctxt @{thm ballI}, dtac ctxt rev_mp, rtac ctxt card_of,
    REPEAT_DETERM o etac ctxt conjE, assume_tac ctxt, rtac ctxt Asuc_Cinfinite] 1;

fun mk_least_min_alg_tac ctxt min_alg_def least =
  EVERY' [rtac ctxt (min_alg_def RS ord_eq_le_trans), rtac ctxt @{thm UN_least},
    dtac ctxt least, dtac ctxt mp, assume_tac ctxt,
    REPEAT_DETERM o etac ctxt conjE, assume_tac ctxt] 1;

fun mk_alg_select_tac ctxt Abs_inverse =
  EVERY' [rtac ctxt @{thm ballI},
    REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE}, hyp_subst_tac ctxt] 1 THEN
  unfold_thms_tac ctxt (Abs_inverse :: fst_snd_convs) THEN assume_tac ctxt 1;

fun mk_mor_select_tac ctxt mor_def mor_cong mor_comp mor_incl_min_alg alg_def alg_select alg_sets
    set_maps str_init_defs =
  let
    val n = length alg_sets;
    val fbetw_tac =
      CONJ_WRAP'
        (K (EVERY' [rtac ctxt @{thm ballI}, etac ctxt rev_bspec,
          etac ctxt @{thm CollectE}, assume_tac ctxt])) alg_sets;
    val mor_tac =
      CONJ_WRAP' (fn thm => EVERY' [rtac ctxt @{thm ballI}, rtac ctxt thm]) str_init_defs;
    fun alg_epi_tac ((alg_set, str_init_def), set_map) =
      EVERY' [rtac ctxt @{thm ballI}, REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, rtac ctxt @{thm CollectI},
        rtac ctxt @{thm ballI}, forward_tac ctxt [alg_select RS @{thm bspec}],
        rtac ctxt (str_init_def RS @{thm ssubst_mem}),
        etac ctxt alg_set, REPEAT_DETERM o EVERY' [rtac ctxt ord_eq_le_trans, resolve_tac ctxt set_map,
          rtac ctxt subset_trans, etac ctxt @{thm image_mono}, rtac ctxt @{thm image_Collect_subsetI}, etac ctxt @{thm bspec},
          assume_tac ctxt]];
  in
    EVERY' [rtac ctxt mor_cong, REPEAT_DETERM_N n o (rtac ctxt sym THEN' rtac ctxt @{thm comp_id}),
      rtac ctxt (Thm.permute_prems 0 1 mor_comp), etac ctxt (Thm.permute_prems 0 1 mor_comp),
      rtac ctxt (mor_def RS iffD2), rtac ctxt conjI, fbetw_tac, mor_tac, rtac ctxt mor_incl_min_alg,
      rtac ctxt (alg_def RS iffD2), CONJ_WRAP' alg_epi_tac ((alg_sets ~~ str_init_defs) ~~ set_maps)] 1
  end;

fun mk_init_ex_mor_tac ctxt Abs_inverse copy card_of_min_algs mor_Rep mor_comp mor_select mor_incl =
  let
    val n = length card_of_min_algs;
  in
    EVERY' [Method.insert_tac ctxt (map (fn thm => thm RS @{thm ex_bij_betw}) card_of_min_algs),
      REPEAT_DETERM o dtac ctxt meta_spec, REPEAT_DETERM o etac ctxt exE, rtac ctxt rev_mp,
      rtac ctxt copy, REPEAT_DETERM_N n o assume_tac ctxt,
      rtac ctxt impI, REPEAT_DETERM o eresolve_tac ctxt [exE, conjE], REPEAT_DETERM_N n o rtac ctxt exI,
      rtac ctxt mor_comp, rtac ctxt mor_Rep, rtac ctxt mor_select, rtac ctxt @{thm CollectI}, REPEAT_DETERM o rtac ctxt exI,
      rtac ctxt conjI, rtac ctxt refl, assume_tac ctxt,
      SELECT_GOAL (unfold_thms_tac ctxt (Abs_inverse :: fst_snd_convs)),
      etac ctxt mor_comp, rtac ctxt mor_incl, REPEAT_DETERM_N n o rtac ctxt subset_UNIV] 1
  end;

fun mk_init_unique_mor_tac ctxt cts m
    alg_def alg_min_alg least_min_algs in_monos alg_sets morEs map_cong0s =
  let
    val n = length least_min_algs;
    val ks = (1 upto n);

    fun mor_tac morE in_mono = EVERY' [etac ctxt morE, rtac ctxt set_mp, rtac ctxt in_mono,
      REPEAT_DETERM_N n o rtac ctxt @{thm Collect_restrict}, rtac ctxt @{thm CollectI},
      REPEAT_DETERM_N (m + n) o (TRY o rtac ctxt conjI THEN' assume_tac ctxt)];
    fun cong_tac ct map_cong0 = EVERY'
      [rtac ctxt (map_cong0 RS infer_instantiate' ctxt [NONE, NONE, SOME ct] arg_cong),
      REPEAT_DETERM_N m o rtac ctxt refl,
      REPEAT_DETERM_N n o (etac ctxt @{thm prop_restrict} THEN' assume_tac ctxt)];

    fun mk_alg_tac (ct, (alg_set, (in_mono, (morE, map_cong0)))) =
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt @{thm CollectI},
        REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, rtac ctxt conjI, rtac ctxt (alg_min_alg RS alg_set),
        REPEAT_DETERM_N n o (etac ctxt subset_trans THEN' rtac ctxt @{thm Collect_restrict}),
        rtac ctxt trans, mor_tac morE in_mono,
        rtac ctxt trans, cong_tac ct map_cong0,
        rtac ctxt sym, mor_tac morE in_mono];

    fun mk_unique_tac (k, least_min_alg) =
      select_prem_tac ctxt n (etac ctxt @{thm prop_restrict}) k THEN' rtac ctxt least_min_alg THEN'
      rtac ctxt (alg_def RS iffD2) THEN'
      CONJ_WRAP' mk_alg_tac (cts ~~ (alg_sets ~~ (in_monos ~~ (morEs ~~ map_cong0s))));
  in
    CONJ_WRAP' mk_unique_tac (ks ~~ least_min_algs) 1
  end;

fun mk_init_induct_tac ctxt m alg_def alg_min_alg least_min_algs alg_sets =
  let
    val n = length least_min_algs;

    fun mk_alg_tac alg_set = EVERY' [rtac ctxt @{thm ballI}, rtac ctxt @{thm CollectI},
      REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, rtac ctxt conjI, rtac ctxt (alg_min_alg RS alg_set),
      REPEAT_DETERM_N n o (etac ctxt subset_trans THEN' rtac ctxt @{thm Collect_restrict}),
      rtac ctxt mp, etac ctxt @{thm bspec}, rtac ctxt @{thm CollectI},
      REPEAT_DETERM_N m o (rtac ctxt conjI THEN' assume_tac ctxt),
      CONJ_WRAP' (K (etac ctxt subset_trans THEN' rtac ctxt @{thm Collect_restrict})) alg_sets,
      CONJ_WRAP' (K (rtac ctxt @{thm ballI} THEN' etac ctxt @{thm prop_restrict} THEN' assume_tac ctxt))
        alg_sets];

    fun mk_induct_tac least_min_alg =
      rtac ctxt @{thm ballI} THEN' etac ctxt @{thm prop_restrict} THEN' rtac ctxt least_min_alg THEN'
      rtac ctxt (alg_def RS iffD2) THEN'
      CONJ_WRAP' mk_alg_tac alg_sets;
  in
    CONJ_WRAP' mk_induct_tac least_min_algs 1
  end;

fun mk_mor_Rep_tac ctxt m defs Reps Abs_inverses alg_min_alg alg_sets set_mapss =
  unfold_thms_tac ctxt (@{thm o_apply} :: defs) THEN
  EVERY' [rtac ctxt conjI,
    CONJ_WRAP' (fn thm => rtac ctxt @{thm ballI} THEN' rtac ctxt thm) Reps,
    CONJ_WRAP' (fn (Abs_inverse, (set_maps, alg_set)) =>
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt Abs_inverse, rtac ctxt (alg_min_alg RS alg_set),
        EVERY' (map2 (fn Rep => fn set_map =>
          EVERY' [rtac ctxt (set_map RS ord_eq_le_trans), rtac ctxt @{thm image_subsetI}, rtac ctxt Rep])
        Reps (drop m set_maps))])
    (Abs_inverses ~~ (set_mapss ~~ alg_sets))] 1;

fun mk_mor_Abs_tac ctxt cts defs Abs_inverses map_comp_ids map_congLs =
  unfold_thms_tac ctxt (@{thm o_apply} :: defs) THEN
  EVERY' [rtac ctxt conjI,
    CONJ_WRAP' (K (rtac ctxt @{thm ballI} THEN' rtac ctxt @{thm UNIV_I})) Abs_inverses,
    CONJ_WRAP' (fn (ct, thm) =>
      EVERY' [rtac ctxt @{thm ballI}, REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE},
        rtac ctxt (thm RS (infer_instantiate' ctxt [NONE, NONE, SOME ct] arg_cong) RS sym),
        EVERY' (map (fn Abs_inverse =>
          EVERY' [rtac ctxt (o_apply RS trans RS @{thm ballI}), etac ctxt (set_mp RS Abs_inverse),
            assume_tac ctxt])
        Abs_inverses)])
    (cts ~~ map2 mk_trans map_comp_ids map_congLs)] 1;

fun mk_mor_fold_tac ctxt cT ct fold_defs ex_mor mor =
  (EVERY' (map (stac ctxt) fold_defs) THEN' EVERY' [rtac ctxt rev_mp, rtac ctxt ex_mor, rtac ctxt impI] THEN'
  REPEAT_DETERM_N (length fold_defs) o etac ctxt exE THEN'
  rtac ctxt (Thm.instantiate' [SOME cT] [SOME ct] @{thm someI}) THEN' etac ctxt mor) 1;

fun mk_fold_unique_mor_tac ctxt type_defs init_unique_mors Reps mor_comp mor_Abs mor_fold =
  let
    fun mk_unique type_def =
      EVERY' [rtac ctxt @{thm surj_fun_eq}, rtac ctxt (type_def RS @{thm type_definition.Abs_image}),
        rtac ctxt @{thm ballI}, resolve_tac ctxt init_unique_mors,
        EVERY' (map (fn thm => assume_tac ctxt ORELSE' rtac ctxt thm) Reps),
        rtac ctxt mor_comp, rtac ctxt mor_Abs, assume_tac ctxt,
        rtac ctxt mor_comp, rtac ctxt mor_Abs, rtac ctxt mor_fold];
  in
    CONJ_WRAP' mk_unique type_defs 1
  end;

fun mk_dtor_o_ctor_tac ctxt dtor_def foldx map_comp_id map_cong0L ctor_o_folds =
  EVERY' [rtac ctxt @{thm ext}, rtac ctxt trans, rtac ctxt o_apply, rtac ctxt (dtor_def RS fun_cong RS trans),
    rtac ctxt trans, rtac ctxt foldx, rtac ctxt trans, rtac ctxt map_comp_id, rtac ctxt trans, rtac ctxt map_cong0L,
    EVERY' (map (fn thm => rtac ctxt @{thm ballI} THEN' rtac ctxt (trans OF [thm RS fun_cong, id_apply]))
      ctor_o_folds),
    rtac ctxt sym, rtac ctxt id_apply] 1;

fun mk_rec_tac ctxt rec_defs foldx fst_recs =
  unfold_thms_tac ctxt
    (rec_defs @ map (fn thm => thm RS @{thm convol_expand_snd}) fst_recs) THEN
  EVERY' [rtac ctxt trans, rtac ctxt o_apply, rtac ctxt trans, rtac ctxt (foldx RS @{thm arg_cong[of _ _ snd]}),
    rtac ctxt @{thm snd_convol'}] 1;

fun mk_rec_unique_mor_tac ctxt rec_defs fst_recs fold_unique_mor =
  unfold_thms_tac ctxt
    (rec_defs @ map (fn thm => thm RS @{thm convol_expand_snd'}) fst_recs) THEN
  etac ctxt fold_unique_mor 1;

fun mk_ctor_induct_tac ctxt m set_mapss init_induct morEs mor_Abs Rep_invs Abs_invs Reps =
  let
    val n = length set_mapss;
    val ks = 1 upto n;

    fun mk_IH_tac Rep_inv Abs_inv set_map =
      DETERM o EVERY' [dtac ctxt meta_mp, rtac ctxt (Rep_inv RS arg_cong RS iffD1), etac ctxt @{thm bspec},
        dtac ctxt set_rev_mp, rtac ctxt @{thm equalityD1}, rtac ctxt set_map, etac ctxt @{thm imageE},
        hyp_subst_tac ctxt, rtac ctxt (Abs_inv RS @{thm ssubst_mem}), etac ctxt set_mp,
        assume_tac ctxt, assume_tac ctxt];

    fun mk_closed_tac (k, (morE, set_maps)) =
      EVERY' [select_prem_tac ctxt n (dtac ctxt asm_rl) k, rtac ctxt @{thm ballI}, rtac ctxt impI,
        rtac ctxt (mor_Abs RS morE RS arg_cong RS iffD2), assume_tac ctxt,
        REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, dtac ctxt @{thm meta_spec},
        EVERY' (@{map 3} mk_IH_tac Rep_invs Abs_invs (drop m set_maps)), assume_tac ctxt];

    fun mk_induct_tac (Rep, Rep_inv) =
      EVERY' [rtac ctxt (Rep_inv RS arg_cong RS iffD1), etac ctxt (Rep RSN (2, @{thm bspec}))];
  in
    (rtac ctxt mp THEN' rtac ctxt impI THEN'
    DETERM o CONJ_WRAP_GEN' (etac ctxt conjE THEN' rtac ctxt conjI) mk_induct_tac (Reps ~~ Rep_invs) THEN'
    rtac ctxt init_induct THEN'
    DETERM o CONJ_WRAP' mk_closed_tac (ks ~~ (morEs ~~ set_mapss))) 1
  end;

fun mk_ctor_induct2_tac ctxt cTs cts ctor_induct weak_ctor_inducts =
  let
    val n = length weak_ctor_inducts;
    val ks = 1 upto n;
    fun mk_inner_induct_tac induct i =
      EVERY' [rtac ctxt allI, fo_rtac ctxt induct,
        select_prem_tac ctxt n (dtac ctxt @{thm meta_spec2}) i,
        REPEAT_DETERM_N n o
          EVERY' [dtac ctxt meta_mp THEN_ALL_NEW Goal.norm_hhf_tac ctxt,
            REPEAT_DETERM o dtac ctxt @{thm meta_spec}, etac ctxt (spec RS meta_mp),
            assume_tac ctxt],
        assume_tac ctxt];
  in
    EVERY' [rtac ctxt rev_mp, rtac ctxt (Thm.instantiate' cTs cts ctor_induct),
      EVERY' (map2 mk_inner_induct_tac weak_ctor_inducts ks), rtac ctxt impI,
      REPEAT_DETERM o eresolve_tac ctxt [conjE, allE],
      CONJ_WRAP' (K (assume_tac ctxt)) ks] 1
  end;

fun mk_map_tac ctxt m n foldx map_comp_id map_cong0 =
  EVERY' [rtac ctxt @{thm ext}, rtac ctxt trans, rtac ctxt o_apply, rtac ctxt trans, rtac ctxt foldx, rtac ctxt trans,
    rtac ctxt o_apply,
    rtac ctxt trans, rtac ctxt (map_comp_id RS arg_cong), rtac ctxt trans, rtac ctxt (map_cong0 RS arg_cong),
    REPEAT_DETERM_N m o rtac ctxt refl,
    REPEAT_DETERM_N n o (EVERY' (map (rtac ctxt) [trans, o_apply, id_apply])),
    rtac ctxt sym, rtac ctxt o_apply] 1;

fun mk_ctor_map_unique_tac ctxt fold_unique sym_map_comps =
  rtac ctxt fold_unique 1 THEN
  unfold_thms_tac ctxt (sym_map_comps @ @{thms comp_assoc id_comp comp_id}) THEN
  ALLGOALS (assume_tac ctxt);

fun mk_set_tac ctxt foldx = EVERY' [rtac ctxt @{thm ext}, rtac ctxt trans, rtac ctxt o_apply,
  rtac ctxt trans, rtac ctxt foldx, rtac ctxt sym, rtac ctxt o_apply] 1;

fun mk_ctor_set_tac ctxt set set_map set_maps =
  let
    val n = length set_maps;
    fun mk_UN thm = rtac ctxt (thm RS @{thm arg_cong[of _ _ Union]} RS trans)
      THEN' rtac ctxt @{thm refl};
  in
    EVERY' [rtac ctxt (set RS @{thm comp_eq_dest} RS trans), rtac ctxt Un_cong,
      rtac ctxt (trans OF [set_map, trans_fun_cong_image_id_id_apply]),
      REPEAT_DETERM_N (n - 1) o rtac ctxt Un_cong,
      EVERY' (map mk_UN set_maps)] 1
  end;

fun mk_set_nat_tac ctxt m induct_tac set_mapss ctor_maps csets ctor_sets i =
  let
    val n = length ctor_maps;

    fun useIH set_nat = EVERY' [rtac ctxt trans, rtac ctxt @{thm image_UN}, rtac ctxt trans, rtac ctxt @{thm SUP_cong},
      rtac ctxt refl, Goal.assume_rule_tac ctxt, rtac ctxt sym, rtac ctxt trans, rtac ctxt @{thm SUP_cong},
      rtac ctxt set_nat, rtac ctxt refl, rtac ctxt @{thm UN_simps(10)}];

    fun mk_set_nat cset ctor_map ctor_set set_nats =
      EVERY' [rtac ctxt trans, rtac ctxt @{thm image_cong}, rtac ctxt ctor_set, rtac ctxt refl, rtac ctxt sym,
        rtac ctxt (trans OF [ctor_map RS infer_instantiate' ctxt [NONE, NONE, SOME cset] arg_cong,
          ctor_set RS trans]),
        rtac ctxt sym, EVERY' (map (rtac ctxt) [trans, @{thm image_Un}, Un_cong]),
        rtac ctxt sym, rtac ctxt (nth set_nats (i - 1)),
        REPEAT_DETERM_N (n - 1) o EVERY' (map (rtac ctxt) [trans, @{thm image_Un}, Un_cong]),
        EVERY' (map useIH (drop m set_nats))];
  in
    (induct_tac THEN' EVERY' (@{map 4} mk_set_nat csets ctor_maps ctor_sets set_mapss)) 1
  end;

fun mk_set_bd_tac ctxt m induct_tac bd_Cinfinite bd_regularCard set_bdss ctor_sets i =
  let
    val n = length ctor_sets;

    fun useIH set_bd = EVERY' [
      rtac ctxt (@{thm card_of_UNION_ordLess_infinite_Field_regularCard} OF [
        bd_regularCard, bd_Cinfinite, set_bd
      ]),
      rtac ctxt @{thm ballI},
      Goal.assume_rule_tac ctxt
    ];

    fun mk_set_nat ctor_set set_bds =
      EVERY' [rtac ctxt @{thm ordIso_ordLess_trans}, rtac ctxt @{thm card_of_ordIso_subst}, rtac ctxt ctor_set,
        rtac ctxt (bd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound_strict})), rtac ctxt (nth set_bds (i - 1)),
        REPEAT_DETERM_N (n - 1) o rtac ctxt (bd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound_strict})),
        EVERY' (map useIH (drop m set_bds))];
  in
    (induct_tac THEN' EVERY' (map2 mk_set_nat ctor_sets set_bdss)) 1
  end;

fun mk_mcong_tac ctxt induct_tac set_setsss map_cong0s ctor_maps =
  let
    fun use_asm thm = EVERY' [etac ctxt @{thm bspec}, etac ctxt set_rev_mp, rtac ctxt thm];

    fun useIH set_sets = EVERY' [rtac ctxt mp, Goal.assume_rule_tac ctxt,
      CONJ_WRAP' (fn thm =>
        EVERY' [rtac ctxt @{thm ballI}, etac ctxt @{thm bspec}, etac ctxt set_rev_mp, etac ctxt thm]) set_sets];

    fun mk_map_cong0 ctor_map map_cong0 set_setss =
      EVERY' [rtac ctxt impI, REPEAT_DETERM o etac ctxt conjE,
        rtac ctxt trans, rtac ctxt ctor_map, rtac ctxt trans, rtac ctxt (map_cong0 RS arg_cong),
        EVERY' (map use_asm (map hd set_setss)),
        EVERY' (map useIH (transpose (map tl set_setss))),
        rtac ctxt sym, rtac ctxt ctor_map];
  in
    (induct_tac THEN' EVERY' (@{map 3} mk_map_cong0 ctor_maps map_cong0s set_setsss)) 1
  end;

fun mk_le_rel_OO_tac ctxt m induct ctor_nchotomys ctor_Irels rel_mono_strong0s le_rel_OOs =
  EVERY' (rtac ctxt induct ::
  @{map 4} (fn nchotomy => fn Irel => fn rel_mono => fn le_rel_OO =>
    EVERY' [rtac ctxt impI, etac ctxt (nchotomy RS @{thm nchotomy_relcomppE}),
      REPEAT_DETERM_N 2 o dtac ctxt (Irel RS iffD1), rtac ctxt (Irel RS iffD2),
      rtac ctxt rel_mono, rtac ctxt (le_rel_OO RS @{thm predicate2D}),
      rtac ctxt @{thm relcomppI}, assume_tac ctxt, assume_tac ctxt,
      REPEAT_DETERM_N m o EVERY' [rtac ctxt @{thm ballI}, rtac ctxt @{thm ballI}, rtac ctxt impI, assume_tac ctxt],
      REPEAT_DETERM_N (length le_rel_OOs) o
        EVERY' [rtac ctxt @{thm ballI}, rtac ctxt @{thm ballI}, Goal.assume_rule_tac ctxt]])
  ctor_nchotomys ctor_Irels rel_mono_strong0s le_rel_OOs) 1;

(* BNF tactics *)

fun mk_map_id0_tac ctxt map_id0s unique =
  (rtac ctxt sym THEN' rtac ctxt unique THEN'
  EVERY' (map (fn thm =>
    EVERY' [rtac ctxt trans, rtac ctxt @{thm id_comp}, rtac ctxt trans, rtac ctxt sym, rtac ctxt @{thm comp_id},
      rtac ctxt (thm RS sym RS arg_cong)]) map_id0s)) 1;

fun mk_map_comp0_tac ctxt map_comp0s ctor_maps unique iplus1 =
  let
    val i = iplus1 - 1;
    val unique' = Thm.permute_prems 0 i unique;
    val map_comp0s' = drop i map_comp0s @ take i map_comp0s;
    val ctor_maps' = drop i ctor_maps @ take i ctor_maps;
    fun mk_comp comp simp =
      EVERY' [rtac ctxt @{thm ext}, rtac ctxt trans, rtac ctxt o_apply, rtac ctxt trans, rtac ctxt o_apply,
        rtac ctxt trans, rtac ctxt (simp RS arg_cong), rtac ctxt trans, rtac ctxt simp,
        rtac ctxt trans, rtac ctxt (comp RS arg_cong), rtac ctxt sym, rtac ctxt o_apply];
  in
    (rtac ctxt sym THEN' rtac ctxt unique' THEN' EVERY' (map2 mk_comp map_comp0s' ctor_maps')) 1
  end;

fun mk_set_map0_tac ctxt set_nat =
  EVERY' (map (rtac ctxt) [@{thm ext}, trans, o_apply, sym, trans, o_apply, set_nat]) 1;

fun mk_bd_card_order_tac ctxt bd_card_orders =
  CONJ_WRAP_GEN' (rtac ctxt @{thm card_order_csum}) (rtac ctxt) bd_card_orders 1;

fun mk_wit_tac ctxt n ctor_set wit =
  REPEAT_DETERM (assume_tac ctxt 1 ORELSE
    EVERY' [dtac ctxt set_rev_mp, rtac ctxt @{thm equalityD1}, resolve_tac ctxt ctor_set,
    REPEAT_DETERM o
      (TRY o REPEAT_DETERM o etac ctxt @{thm UnE} THEN' TRY o etac ctxt @{thm UN_E} THEN'
        (eresolve_tac ctxt wit ORELSE'
        (dresolve_tac ctxt wit THEN'
          (etac ctxt FalseE ORELSE'
          EVERY' [hyp_subst_tac ctxt, dtac ctxt set_rev_mp, rtac ctxt @{thm equalityD1}, resolve_tac ctxt ctor_set,
            REPEAT_DETERM_N n o etac ctxt @{thm UnE}]))))] 1);

fun mk_ctor_rel_tac ctxt in_Irels i in_rel map_comp0 map_cong0 ctor_map ctor_sets ctor_inject
  ctor_dtor set_map0s ctor_set_incls ctor_set_set_inclss =
  let
    val m = length ctor_set_incls;
    val n = length ctor_set_set_inclss;

    val (passive_set_map0s, active_set_map0s) = chop m set_map0s;
    val in_Irel = nth in_Irels (i - 1);
    val le_arg_cong_ctor_dtor = ctor_dtor RS arg_cong RS ord_eq_le_trans;
    val eq_arg_cong_ctor_dtor = ctor_dtor RS arg_cong RS trans;
    val if_tac =
      EVERY' [dtac ctxt (in_Irel RS iffD1), REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE CollectE},
        rtac ctxt (in_rel RS iffD2), rtac ctxt exI, rtac ctxt conjI, rtac ctxt @{thm CollectI},
        EVERY' (map2 (fn set_map0 => fn ctor_set_incl =>
          EVERY' [rtac ctxt conjI, rtac ctxt ord_eq_le_trans, rtac ctxt set_map0,
            rtac ctxt ord_eq_le_trans, rtac ctxt trans_fun_cong_image_id_id_apply,
            rtac ctxt (ctor_set_incl RS subset_trans), etac ctxt le_arg_cong_ctor_dtor])
        passive_set_map0s ctor_set_incls),
        CONJ_WRAP' (fn (in_Irel, (set_map0, ctor_set_set_incls)) =>
          EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt set_map0, rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm CollectI},
            rtac ctxt @{thm case_prodI}, rtac ctxt (in_Irel RS iffD2), rtac ctxt exI, rtac ctxt conjI, rtac ctxt @{thm CollectI},
            CONJ_WRAP' (fn thm =>
              EVERY' (map (etac ctxt) [thm RS subset_trans, le_arg_cong_ctor_dtor]))
            ctor_set_set_incls,
            rtac ctxt conjI, rtac ctxt refl, rtac ctxt refl])
        (in_Irels ~~ (active_set_map0s ~~ ctor_set_set_inclss)),
        CONJ_WRAP' (fn conv =>
          EVERY' [rtac ctxt trans, rtac ctxt map_comp0, rtac ctxt trans, rtac ctxt map_cong0,
          REPEAT_DETERM_N m o rtac ctxt @{thm fun_cong[OF comp_id]},
          REPEAT_DETERM_N n o EVERY' (map (rtac ctxt) [trans, o_apply, conv]),
          rtac ctxt (ctor_inject RS iffD1), rtac ctxt trans, rtac ctxt sym, rtac ctxt ctor_map,
          etac ctxt eq_arg_cong_ctor_dtor])
        fst_snd_convs];
    val only_if_tac =
      EVERY' [dtac ctxt (in_rel RS iffD1), REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE CollectE},
        rtac ctxt (in_Irel RS iffD2), rtac ctxt exI, rtac ctxt conjI, rtac ctxt @{thm CollectI},
        CONJ_WRAP' (fn (ctor_set, passive_set_map0) =>
          EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt ctor_set, rtac ctxt @{thm Un_least},
            rtac ctxt ord_eq_le_trans, rtac ctxt @{thm box_equals[OF _ refl]},
            rtac ctxt passive_set_map0, rtac ctxt trans_fun_cong_image_id_id_apply, assume_tac ctxt,
            CONJ_WRAP_GEN' (rtac ctxt (Thm.permute_prems 0 1 @{thm Un_least}))
              (fn (active_set_map0, in_Irel) => EVERY' [rtac ctxt ord_eq_le_trans,
                rtac ctxt @{thm SUP_cong[OF _ refl]}, rtac ctxt active_set_map0, rtac ctxt @{thm UN_least},
                dtac ctxt set_rev_mp, etac ctxt @{thm image_mono}, etac ctxt @{thm imageE},
                dtac ctxt @{thm ssubst_mem[OF prod.collapse]},
                REPEAT_DETERM o eresolve_tac ctxt
                  @{thms CollectE conjE case_prodE iffD1[OF prod.inject, elim_format]},
                hyp_subst_tac ctxt,
                dtac ctxt (in_Irel RS iffD1), dtac ctxt @{thm someI_ex}, REPEAT_DETERM o etac ctxt conjE,
                REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, assume_tac ctxt])
            (rev (active_set_map0s ~~ in_Irels))])
        (ctor_sets ~~ passive_set_map0s),
        rtac ctxt conjI,
        REPEAT_DETERM_N 2 o EVERY' [rtac ctxt trans, rtac ctxt ctor_map, rtac ctxt (ctor_inject RS iffD2),
          rtac ctxt trans, rtac ctxt map_comp0, rtac ctxt trans, rtac ctxt map_cong0,
          REPEAT_DETERM_N m o rtac ctxt @{thm fun_cong[OF comp_id]},
          EVERY' (map (fn in_Irel => EVERY' [rtac ctxt trans, rtac ctxt o_apply,
            dtac ctxt set_rev_mp, assume_tac ctxt,
            dtac ctxt @{thm ssubst_mem[OF prod.collapse]},
            REPEAT_DETERM o eresolve_tac ctxt
              @{thms CollectE conjE case_prodE iffD1[OF prod.inject, elim_format]},
            hyp_subst_tac ctxt,
            dtac ctxt (in_Irel RS iffD1), dtac ctxt @{thm someI_ex},
            REPEAT_DETERM o etac ctxt conjE, assume_tac ctxt])
          in_Irels),
          assume_tac ctxt]]
  in
    EVERY' [rtac ctxt iffI, if_tac, only_if_tac] 1
  end;

fun mk_ctor_rec_transfer_tac ctxt n m ctor_rec_defs ctor_fold_transfers pre_T_map_transfers
    ctor_rels =
  CONJ_WRAP (fn (ctor_rec_def, ctor_fold_transfer) =>
      REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
      unfold_thms_tac ctxt [ctor_rec_def, o_apply] THEN
      HEADGOAL (rtac ctxt @{thm rel_funD[OF snd_transfer]} THEN'
        etac ctxt (mk_rel_funDN_rotated (n + 1) ctor_fold_transfer) THEN'
        EVERY' (map2 (fn pre_T_map_transfer => fn ctor_rel =>
          etac ctxt (mk_rel_funDN_rotated 2 @{thm convol_transfer}) THEN'
          rtac ctxt (mk_rel_funDN_rotated 2 @{thm comp_transfer}) THEN'
          rtac ctxt (mk_rel_funDN (m + n) pre_T_map_transfer) THEN'
          REPEAT_DETERM_N m o rtac ctxt @{thm id_transfer} THEN'
          REPEAT_DETERM o rtac ctxt @{thm fst_transfer} THEN'
          rtac ctxt rel_funI THEN'
          etac ctxt (ctor_rel RS iffD2)) pre_T_map_transfers ctor_rels)))
    (ctor_rec_defs ~~ ctor_fold_transfers);

fun mk_rel_induct_tac ctxt IHs m ctor_induct2 ks ctor_rels rel_mono_strong0s =
  let val n = length ks;
  in
    unfold_tac ctxt @{thms le_fun_def le_bool_def all_simps(1,2)[symmetric]} THEN
    EVERY' [REPEAT_DETERM o rtac ctxt allI, rtac ctxt ctor_induct2,
      EVERY' (@{map 3} (fn IH => fn ctor_rel => fn rel_mono_strong0 =>
        EVERY' [rtac ctxt impI, dtac ctxt (ctor_rel RS iffD1), rtac ctxt (IH RS @{thm spec2} RS mp),
          etac ctxt rel_mono_strong0,
          REPEAT_DETERM_N m o rtac ctxt @{thm ballI[OF ballI[OF imp_refl]]},
          EVERY' (map (fn j =>
            EVERY' [select_prem_tac ctxt n (dtac ctxt asm_rl) j, rtac ctxt @{thm ballI[OF ballI]},
              Goal.assume_rule_tac ctxt]) ks)])
      IHs ctor_rels rel_mono_strong0s)] 1
  end;

fun mk_fold_transfer_tac ctxt m ctor_rel_induct map_transfers folds =
  let
    val n = length map_transfers;
  in
    unfold_thms_tac ctxt
      @{thms rel_fun_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]} THEN
    unfold_thms_tac ctxt @{thms rel_fun_iff_leq_vimage2p} THEN
    HEADGOAL (EVERY'
      [REPEAT_DETERM o resolve_tac ctxt [allI, impI], rtac ctxt ctor_rel_induct,
      EVERY' (map (fn map_transfer => EVERY'
        [REPEAT_DETERM o resolve_tac ctxt [allI, impI, @{thm vimage2pI}],
        SELECT_GOAL (unfold_thms_tac ctxt folds),
        etac ctxt @{thm predicate2D_vimage2p},
        rtac ctxt (funpow (m + n + 1) (fn thm => thm RS rel_funD) map_transfer),
        REPEAT_DETERM_N m o rtac ctxt @{thm id_transfer},
        REPEAT_DETERM_N n o rtac ctxt @{thm vimage2p_rel_fun},
        assume_tac ctxt])
      map_transfers)])
  end;

end;
