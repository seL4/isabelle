(*  Title:      HOL/Tools/BNF/bnf_lfp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Tactics for the datatype construction.
*)

signature BNF_LFP_TACTICS =
sig
  val mk_alg_min_alg_tac: int -> thm -> thm list -> thm -> thm -> thm list list -> thm list ->
    thm list -> tactic
  val mk_alg_not_empty_tac: Proof.context -> thm -> thm list -> thm list -> tactic
  val mk_alg_select_tac: thm -> {prems: 'a, context: Proof.context} -> tactic
  val mk_alg_set_tac: thm -> tactic
  val mk_bd_card_order_tac: thm list -> tactic
  val mk_bd_limit_tac: int -> thm -> tactic
  val mk_card_of_min_alg_tac: thm -> thm -> thm -> thm -> thm -> tactic
  val mk_copy_alg_tac: thm list list -> thm list -> thm -> thm -> thm -> tactic
  val mk_copy_str_tac: thm list list -> thm -> thm list -> tactic
  val mk_ctor_induct_tac: Proof.context -> int -> thm list list -> thm -> thm list -> thm ->
    thm list -> thm list -> thm list -> tactic
  val mk_ctor_induct2_tac: ctyp option list -> cterm option list -> thm -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_ctor_set_tac: thm -> thm -> thm list -> tactic
  val mk_ctor_rel_tac: Proof.context -> thm list -> int -> thm -> thm -> thm -> thm -> thm list ->
    thm -> thm -> thm list -> thm list -> thm list list -> tactic
  val mk_dtor_o_ctor_tac: thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_ex_copy_alg_tac: int -> thm -> thm -> tactic
  val mk_init_ex_mor_tac: thm -> thm -> thm -> thm list -> thm -> thm -> thm ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_init_induct_tac: int -> thm -> thm -> thm list -> thm list -> tactic
  val mk_init_unique_mor_tac: int -> thm -> thm -> thm list -> thm list -> thm list -> thm list ->
    thm list -> tactic
  val mk_iso_alt_tac: thm list -> thm -> tactic
  val mk_fold_unique_mor_tac: thm list -> thm list -> thm list -> thm -> thm -> thm -> tactic
  val mk_fold_transfer_tac: int -> thm -> thm list -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_least_min_alg_tac: thm -> thm -> tactic
  val mk_le_rel_OO_tac: int -> thm -> thm list -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_map_comp0_tac: thm list -> thm list -> thm -> int -> tactic
  val mk_map_id0_tac: thm list -> thm -> tactic
  val mk_map_tac: int -> int -> thm -> thm -> thm -> tactic
  val mk_ctor_map_unique_tac: thm -> thm list -> Proof.context -> tactic
  val mk_mcong_tac: (int -> tactic) -> thm list list list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_min_algs_card_of_tac: ctyp -> cterm -> int -> thm -> thm list -> thm list -> thm -> thm ->
    thm -> thm -> thm -> thm -> thm -> tactic
  val mk_min_algs_least_tac: ctyp -> cterm -> thm -> thm list -> thm list -> tactic
  val mk_min_algs_mono_tac: Proof.context -> thm -> tactic
  val mk_min_algs_tac: thm -> thm list -> tactic
  val mk_mor_Abs_tac: thm -> thm list -> thm list -> tactic
  val mk_mor_Rep_tac: thm list -> thm -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_mor_UNIV_tac: int -> thm list -> thm -> tactic
  val mk_mor_comp_tac: thm -> thm list list -> thm list -> tactic
  val mk_mor_convol_tac: 'a list -> thm -> tactic
  val mk_mor_elim_tac: thm -> tactic
  val mk_mor_incl_tac: thm -> thm list -> tactic
  val mk_mor_inv_tac: thm -> thm -> thm list list -> thm list -> thm list -> thm list -> tactic
  val mk_mor_fold_tac: ctyp -> cterm -> thm list -> thm -> thm -> tactic
  val mk_mor_select_tac: thm -> thm -> thm -> thm -> thm -> thm -> thm list -> thm list list ->
    thm list -> tactic
  val mk_mor_str_tac: 'a list -> thm -> tactic
  val mk_rel_induct_tac: int -> thm -> int list -> thm list -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_rec_tac: thm list -> thm -> thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_rec_unique_mor_tac: thm list -> thm list -> thm -> {prems: 'a, context: Proof.context} ->
    tactic
  val mk_set_bd_tac: int -> (int -> tactic) -> thm -> thm list list -> thm list -> int ->
    Proof.context -> tactic
  val mk_set_nat_tac: int -> (int -> tactic) -> thm list list -> thm list -> cterm list ->
    thm list -> int -> {prems: 'a, context: Proof.context} -> tactic
  val mk_set_map0_tac: thm -> tactic
  val mk_set_tac: thm -> tactic
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
val rev_bspec = Drule.rotate_prems 1 bspec;
val Un_cong = @{thm arg_cong2[of _ _ _ _ "op \<union>"]}

fun mk_alg_set_tac alg_def =
  dtac (alg_def RS iffD1) 1 THEN
  REPEAT_DETERM (etac conjE 1) THEN
  EVERY' [etac bspec, rtac CollectI] 1 THEN
  REPEAT_DETERM (etac conjI 1) THEN atac 1;

fun mk_alg_not_empty_tac ctxt alg_set alg_sets wits =
  (EVERY' [rtac notI, hyp_subst_tac ctxt, ftac alg_set] THEN'
  REPEAT_DETERM o FIRST'
    [rtac subset_UNIV,
    EVERY' [rtac @{thm subset_emptyI}, eresolve_tac wits],
    EVERY' [rtac subsetI, rtac FalseE, eresolve_tac wits],
    EVERY' [rtac subsetI, dresolve_tac wits, hyp_subst_tac ctxt,
      FIRST' (map (fn thm => rtac thm THEN' atac) alg_sets)]] THEN'
  etac @{thm emptyE}) 1;

fun mk_mor_elim_tac mor_def =
  (dtac (subst OF [mor_def]) THEN'
  REPEAT o etac conjE THEN'
  TRY o rtac @{thm image_subsetI} THEN'
  etac bspec THEN'
  atac) 1;

fun mk_mor_incl_tac mor_def map_ids =
  (stac mor_def THEN'
  rtac conjI THEN'
  CONJ_WRAP' (K (EVERY' [rtac ballI, etac set_mp, stac id_apply, atac])) map_ids THEN'
  CONJ_WRAP' (fn thm =>
   (EVERY' [rtac ballI, rtac trans, rtac id_apply, stac thm, rtac refl])) map_ids) 1;

fun mk_mor_comp_tac mor_def set_maps map_comp_ids =
  let
    val fbetw_tac = EVERY' [rtac ballI, stac o_apply, etac bspec, etac bspec, atac];
    fun mor_tac (set_map, map_comp_id) =
      EVERY' [rtac ballI, stac o_apply, rtac trans,
        rtac trans, dtac rev_bspec, atac, etac arg_cong,
         REPEAT o eresolve_tac [CollectE, conjE], etac bspec, rtac CollectI] THEN'
      CONJ_WRAP' (fn thm =>
        FIRST' [rtac subset_UNIV,
          (EVERY' [rtac ord_eq_le_trans, rtac thm, rtac @{thm image_subsetI},
            etac bspec, etac set_mp, atac])]) set_map THEN'
      rtac (map_comp_id RS arg_cong);
  in
    (dtac (mor_def RS subst) THEN' dtac (mor_def RS subst) THEN' stac mor_def THEN'
    REPEAT o etac conjE THEN'
    rtac conjI THEN'
    CONJ_WRAP' (K fbetw_tac) set_maps THEN'
    CONJ_WRAP' mor_tac (set_maps ~~ map_comp_ids)) 1
  end;

fun mk_mor_inv_tac alg_def mor_def set_maps morEs map_comp_ids map_cong0Ls =
  let
    val fbetw_tac = EVERY' [rtac ballI, etac set_mp, etac imageI];
    fun Collect_tac set_map =
      CONJ_WRAP' (fn thm =>
        FIRST' [rtac subset_UNIV,
          (EVERY' [rtac ord_eq_le_trans, rtac thm, rtac subset_trans,
            etac @{thm image_mono}, atac])]) set_map;
    fun mor_tac (set_map, ((morE, map_comp_id), map_cong0L)) =
      EVERY' [rtac ballI, ftac rev_bspec, atac,
         REPEAT o eresolve_tac [CollectE, conjE], rtac sym, rtac trans, rtac sym,
         etac @{thm inverE}, etac bspec, rtac CollectI, Collect_tac set_map,
         rtac trans, etac (morE RS arg_cong), rtac CollectI, Collect_tac set_map,
         rtac trans, rtac (map_comp_id RS arg_cong), rtac (map_cong0L RS arg_cong),
         REPEAT_DETERM_N (length morEs) o
           (EVERY' [rtac subst, rtac @{thm inver_pointfree}, etac @{thm inver_mono}, atac])];
  in
    (stac mor_def THEN'
    dtac (alg_def RS iffD1) THEN'
    dtac (alg_def RS iffD1) THEN'
    REPEAT o etac conjE THEN'
    rtac conjI THEN'
    CONJ_WRAP' (K fbetw_tac) set_maps THEN'
    CONJ_WRAP' mor_tac (set_maps ~~ (morEs ~~ map_comp_ids ~~ map_cong0Ls))) 1
  end;

fun mk_mor_str_tac ks mor_def =
  (stac mor_def THEN' rtac conjI THEN'
  CONJ_WRAP' (K (EVERY' [rtac ballI, rtac UNIV_I])) ks THEN'
  CONJ_WRAP' (K (EVERY' [rtac ballI, rtac refl])) ks) 1;

fun mk_mor_convol_tac ks mor_def =
  (stac mor_def THEN' rtac conjI THEN'
  CONJ_WRAP' (K (EVERY' [rtac ballI, rtac UNIV_I])) ks THEN'
  CONJ_WRAP' (K (EVERY' [rtac ballI, rtac trans, rtac @{thm fst_convol'}, rtac o_apply])) ks) 1;

fun mk_mor_UNIV_tac m morEs mor_def =
  let
    val n = length morEs;
    fun mor_tac morE = EVERY' [rtac ext, rtac trans, rtac o_apply, rtac trans, etac morE,
      rtac CollectI, CONJ_WRAP' (K (rtac subset_UNIV)) (1 upto m + n),
      rtac sym, rtac o_apply];
  in
    EVERY' [rtac iffI, CONJ_WRAP' mor_tac morEs,
    stac mor_def, rtac conjI, CONJ_WRAP' (K (rtac ballI THEN' rtac UNIV_I)) morEs,
    REPEAT_DETERM o etac conjE, REPEAT_DETERM_N n o dtac (@{thm fun_eq_iff} RS subst),
    CONJ_WRAP' (K (EVERY' [rtac ballI, REPEAT_DETERM o etac allE, rtac trans,
      etac (o_apply RS subst), rtac o_apply])) morEs] 1
  end;

fun mk_iso_alt_tac mor_images mor_inv =
  let
    val n = length mor_images;
    fun if_wrap_tac thm =
      EVERY' [rtac ssubst, rtac @{thm bij_betw_iff_ex}, rtac exI, rtac conjI,
        rtac @{thm inver_surj}, etac thm, etac thm, atac, etac conjI, atac]
    val if_tac =
      EVERY' [etac thin_rl, etac thin_rl, REPEAT o eresolve_tac [conjE, exE],
        rtac conjI, atac, CONJ_WRAP' if_wrap_tac mor_images];
    val only_if_tac =
      EVERY' [rtac conjI, etac conjunct1, EVERY' (map (fn thm =>
        EVERY' [rtac exE, rtac @{thm bij_betw_ex_weakE}, etac (conjunct2 RS thm)])
        (map (mk_conjunctN n) (1 upto n))), REPEAT o rtac exI, rtac conjI, rtac mor_inv,
        etac conjunct1, atac, atac, REPEAT_DETERM_N n o atac,
        CONJ_WRAP' (K (etac conjunct2)) mor_images];
  in
    (rtac iffI THEN' if_tac THEN' only_if_tac) 1
  end;

fun mk_copy_str_tac set_maps alg_def alg_sets =
  let
    val n = length alg_sets;
    val bij_betw_inv_tac =
      EVERY' [etac thin_rl, REPEAT_DETERM_N n o EVERY' [dtac @{thm bij_betwI}, atac, atac],
        REPEAT_DETERM_N (2 * n) o etac thin_rl, REPEAT_DETERM_N (n - 1) o etac conjI, atac];
    fun set_tac thms =
      EVERY' [rtac ord_eq_le_trans, resolve_tac thms, rtac subset_trans,
          etac @{thm image_mono}, rtac equalityD1, etac @{thm bij_betw_imageE}];
    val copy_str_tac =
      CONJ_WRAP' (fn (thms, thm) =>
        EVERY' [rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac set_mp,
          rtac equalityD1, etac @{thm bij_betw_imageE}, rtac imageI, etac thm,
          REPEAT_DETERM o rtac subset_UNIV, REPEAT_DETERM_N n o (set_tac thms)])
      (set_maps ~~ alg_sets);
  in
    (rtac rev_mp THEN' DETERM o bij_betw_inv_tac THEN' rtac impI THEN'
    stac alg_def THEN' copy_str_tac) 1
  end;

fun mk_copy_alg_tac set_maps alg_sets mor_def iso_alt copy_str =
  let
    val n = length alg_sets;
    val fbetw_tac = CONJ_WRAP' (K (etac @{thm bij_betwE})) alg_sets;
    fun set_tac thms =
      EVERY' [rtac ord_eq_le_trans, resolve_tac thms, rtac subset_trans,
        REPEAT_DETERM o etac conjE, etac @{thm image_mono},
        rtac equalityD1, etac @{thm bij_betw_imageE}];
    val mor_tac =
      CONJ_WRAP' (fn (thms, thm) =>
        EVERY' [rtac ballI, etac CollectE, etac @{thm inverE}, etac thm,
          REPEAT_DETERM o rtac subset_UNIV, REPEAT_DETERM_N n o (set_tac thms)])
      (set_maps ~~ alg_sets);
  in
    (rtac (iso_alt RS iffD2) THEN'
    etac copy_str THEN' REPEAT_DETERM o atac THEN'
    rtac conjI THEN' stac mor_def THEN' rtac conjI THEN' fbetw_tac THEN' mor_tac THEN'
    CONJ_WRAP' (K atac) alg_sets) 1
  end;

fun mk_ex_copy_alg_tac n copy_str copy_alg =
  EVERY' [REPEAT_DETERM_N n o rtac exI, rtac conjI, etac copy_str,
    REPEAT_DETERM_N n o atac,
    REPEAT_DETERM_N n o etac @{thm bij_betw_inver2},
    REPEAT_DETERM_N n o etac @{thm bij_betw_inver1}, etac copy_alg,
    REPEAT_DETERM_N n o atac,
    REPEAT_DETERM_N n o etac @{thm bij_betw_inver2},
    REPEAT_DETERM_N n o etac @{thm bij_betw_inver1}] 1;

fun mk_bd_limit_tac n bd_Cinfinite =
  EVERY' [REPEAT_DETERM o etac conjE, rtac rev_mp, rtac @{thm Cinfinite_limit_finite},
    REPEAT_DETERM_N n o rtac @{thm finite.insertI}, rtac @{thm finite.emptyI},
    REPEAT_DETERM_N n o etac @{thm insert_subsetI}, rtac @{thm empty_subsetI},
    rtac bd_Cinfinite, rtac impI, etac bexE, rtac bexI,
    CONJ_WRAP' (fn i =>
      EVERY' [etac bspec, REPEAT_DETERM_N i o rtac @{thm insertI2}, rtac @{thm insertI1}])
      (0 upto n - 1),
    atac] 1;

fun mk_min_algs_tac worel in_congs =
  let
    val minG_tac = EVERY' [rtac @{thm UN_cong}, rtac refl, dtac bspec, atac, etac arg_cong];
    fun minH_tac thm =
      EVERY' [rtac Un_cong, minG_tac, rtac @{thm image_cong}, rtac thm,
        REPEAT_DETERM_N (length in_congs) o minG_tac, rtac refl];
  in
    (rtac (worel RS (@{thm wo_rel.worec_fixpoint} RS fun_cong)) THEN' rtac ssubst THEN'
    rtac meta_eq_to_obj_eq THEN' rtac (worel RS @{thm wo_rel.adm_wo_def}) THEN'
    REPEAT_DETERM_N 3 o rtac allI THEN' rtac impI THEN'
    CONJ_WRAP_GEN' (EVERY' [rtac Pair_eqI, rtac conjI]) minH_tac in_congs) 1
  end;

fun mk_min_algs_mono_tac ctxt min_algs = EVERY' [stac @{thm relChain_def}, rtac allI, rtac allI,
  rtac impI, rtac @{thm case_split}, rtac @{thm xt1(3)}, rtac min_algs, etac @{thm FieldI2},
  rtac subsetI, rtac UnI1, rtac @{thm UN_I}, etac @{thm underS_I}, atac, atac,
  rtac equalityD1, dtac @{thm notnotD}, hyp_subst_tac ctxt, rtac refl] 1;

fun mk_min_algs_card_of_tac cT ct m worel min_algs in_bds bd_Card_order bd_Cnotzero
  suc_Card_order suc_Cinfinite suc_Cnotzero suc_Asuc Asuc_Cinfinite =
  let
    val induct = worel RS
      Drule.instantiate' [SOME cT] [NONE, SOME ct] @{thm well_order_induct_imp};
    val src = 1 upto m + 1;
    val dest = (m + 1) :: (1 upto m);
    val absorbAs_tac = if m = 0 then K (all_tac)
      else EVERY' [rtac @{thm ordIso_transitive}, rtac @{thm csum_cong1},
        rtac @{thm ordIso_transitive},
        BNF_Tactics.mk_rotate_eq_tac (rtac @{thm ordIso_refl} THEN'
          FIRST' [rtac @{thm card_of_Card_order}, rtac @{thm Card_order_csum},
            rtac @{thm Card_order_cexp}])
        @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_com} @{thm csum_cong}
        src dest,
        rtac @{thm csum_absorb1}, rtac Asuc_Cinfinite, rtac ctrans, rtac @{thm ordLeq_csum1},
        FIRST' [rtac @{thm Card_order_csum}, rtac @{thm card_of_Card_order}],
        rtac @{thm ordLeq_cexp1}, rtac suc_Cnotzero, rtac @{thm Card_order_csum}];

    val minG_tac = EVERY' [rtac @{thm UNION_Cinfinite_bound}, rtac @{thm ordLess_imp_ordLeq},
      rtac @{thm ordLess_transitive}, rtac @{thm card_of_underS}, rtac suc_Card_order,
      atac, rtac suc_Asuc, rtac ballI, etac allE, dtac mp, etac @{thm underS_E},
      dtac mp, etac @{thm underS_Field}, REPEAT o etac conjE, atac, rtac Asuc_Cinfinite]

    fun mk_minH_tac (min_alg, in_bd) = EVERY' [rtac @{thm ordIso_ordLeq_trans},
      rtac @{thm card_of_ordIso_subst}, etac min_alg, rtac @{thm Un_Cinfinite_bound},
      minG_tac, rtac ctrans, rtac @{thm card_of_image}, rtac ctrans, rtac in_bd, rtac ctrans,
      rtac @{thm cexp_mono1}, rtac @{thm csum_mono1},
      REPEAT_DETERM_N m o rtac @{thm csum_mono2},
      CONJ_WRAP_GEN' (rtac @{thm csum_cinfinite_bound}) (K minG_tac) min_algs,
      REPEAT_DETERM o FIRST'
        [rtac @{thm card_of_Card_order}, rtac @{thm Card_order_csum},
        rtac Asuc_Cinfinite, rtac bd_Card_order],
      rtac @{thm ordIso_ordLeq_trans}, rtac @{thm cexp_cong1}, absorbAs_tac,
      rtac @{thm csum_absorb1}, rtac Asuc_Cinfinite, rtac @{thm ctwo_ordLeq_Cinfinite},
      rtac Asuc_Cinfinite, rtac bd_Card_order,
      rtac @{thm ordIso_imp_ordLeq}, rtac @{thm cexp_cprod_ordLeq},
      resolve_tac @{thms Card_order_csum Card_order_ctwo}, rtac suc_Cinfinite,
      rtac bd_Cnotzero, rtac @{thm cardSuc_ordLeq}, rtac bd_Card_order, rtac Asuc_Cinfinite];
  in
    (rtac induct THEN'
    rtac impI THEN'
    CONJ_WRAP' mk_minH_tac (min_algs ~~ in_bds)) 1
  end;

fun mk_min_algs_least_tac cT ct worel min_algs alg_sets =
  let
    val induct = worel RS
      Drule.instantiate' [SOME cT] [NONE, SOME ct] @{thm well_order_induct_imp};

    val minG_tac = EVERY' [rtac @{thm UN_least}, etac allE, dtac mp, etac @{thm underS_E},
      dtac mp, etac @{thm underS_Field}, REPEAT_DETERM o etac conjE, atac];

    fun mk_minH_tac (min_alg, alg_set) = EVERY' [rtac ord_eq_le_trans, etac min_alg,
      rtac @{thm Un_least}, minG_tac, rtac @{thm image_subsetI},
      REPEAT_DETERM o eresolve_tac [CollectE, conjE], etac alg_set,
      REPEAT_DETERM o FIRST' [atac, etac subset_trans THEN' minG_tac]];
  in
    (rtac induct THEN'
    rtac impI THEN'
    CONJ_WRAP' mk_minH_tac (min_algs ~~ alg_sets)) 1
  end;

fun mk_alg_min_alg_tac m alg_def min_alg_defs bd_limit bd_Cinfinite
    set_bdss min_algs min_alg_monos =
  let
    val n = length min_algs;
    fun mk_cardSuc_UNION_tac set_bds (mono, def) = EVERY'
      [rtac bexE, rtac @{thm cardSuc_UNION_Cinfinite}, rtac bd_Cinfinite, rtac mono,
       etac (def RSN (2, @{thm subset_trans[OF _ equalityD1]})), resolve_tac set_bds];
    fun mk_conjunct_tac (set_bds, (min_alg, min_alg_def)) =
      EVERY' [rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, conjE],
        EVERY' (map (mk_cardSuc_UNION_tac set_bds) (min_alg_monos ~~ min_alg_defs)), rtac bexE,
        rtac bd_limit, REPEAT_DETERM_N (n - 1) o etac conjI, atac,
        rtac (min_alg_def RS @{thm set_mp[OF equalityD2]}),
        rtac @{thm UN_I}, REPEAT_DETERM_N (m + 3 * n) o etac thin_rl, atac, rtac set_mp,
        rtac equalityD2, rtac min_alg, atac, rtac UnI2, rtac @{thm image_eqI}, rtac refl,
        rtac CollectI, REPEAT_DETERM_N m o dtac asm_rl, REPEAT_DETERM_N n o etac thin_rl,
        REPEAT_DETERM o etac conjE,
        CONJ_WRAP' (K (FIRST' [atac,
          EVERY' [etac subset_trans, rtac subsetI, rtac @{thm UN_I},
            etac @{thm underS_I}, atac, atac]]))
          set_bds];
  in
    (rtac (alg_def RS iffD2) THEN'
    CONJ_WRAP' mk_conjunct_tac (set_bdss ~~ (min_algs ~~ min_alg_defs))) 1
  end;

fun mk_card_of_min_alg_tac min_alg_def card_of suc_Card_order suc_Asuc Asuc_Cinfinite =
  EVERY' [stac min_alg_def, rtac @{thm UNION_Cinfinite_bound},
    rtac @{thm ordIso_ordLeq_trans}, rtac @{thm card_of_Field_ordIso}, rtac suc_Card_order,
    rtac @{thm ordLess_imp_ordLeq}, rtac suc_Asuc, rtac ballI, dtac rev_mp, rtac card_of,
    REPEAT_DETERM o etac conjE, atac, rtac Asuc_Cinfinite] 1;

fun mk_least_min_alg_tac min_alg_def least =
  EVERY' [stac min_alg_def, rtac @{thm UN_least}, dtac least, dtac mp, atac,
    REPEAT_DETERM o etac conjE, atac] 1;

fun mk_alg_select_tac Abs_inverse {context = ctxt, prems = _} =
  EVERY' [rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac ctxt] 1 THEN
  unfold_thms_tac ctxt (Abs_inverse :: fst_snd_convs) THEN atac 1;

fun mk_mor_select_tac mor_def mor_cong mor_comp mor_incl_min_alg alg_def alg_select alg_sets
    set_maps str_init_defs =
  let
    val n = length alg_sets;
    val fbetw_tac =
      CONJ_WRAP' (K (EVERY' [rtac ballI, etac rev_bspec, etac CollectE, atac])) alg_sets;
    val mor_tac =
      CONJ_WRAP' (fn thm => EVERY' [rtac ballI, rtac thm]) str_init_defs;
    fun alg_epi_tac ((alg_set, str_init_def), set_map) =
      EVERY' [rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac CollectI,
        rtac ballI, ftac (alg_select RS bspec), stac str_init_def, etac alg_set,
        REPEAT_DETERM o FIRST' [rtac subset_UNIV,
          EVERY' [rtac ord_eq_le_trans, resolve_tac set_map, rtac subset_trans,
            etac @{thm image_mono}, rtac @{thm image_Collect_subsetI}, etac bspec, atac]]];
  in
    (rtac mor_cong THEN' REPEAT_DETERM_N n o (rtac sym THEN' rtac @{thm comp_id}) THEN'
    rtac (Thm.permute_prems 0 1 mor_comp) THEN' etac (Thm.permute_prems 0 1 mor_comp) THEN'
    stac mor_def THEN' rtac conjI THEN' fbetw_tac THEN' mor_tac THEN' rtac mor_incl_min_alg THEN'
    stac alg_def THEN' CONJ_WRAP' alg_epi_tac ((alg_sets ~~ str_init_defs) ~~ set_maps)) 1
  end;

fun mk_init_ex_mor_tac Abs_inverse copy_alg_ex alg_min_alg card_of_min_algs
    mor_comp mor_select mor_incl_min_alg {context = ctxt, prems = _} =
  let
    val n = length card_of_min_algs;
    val card_of_ordIso_tac = EVERY' [rtac ssubst, rtac @{thm card_of_ordIso},
      rtac @{thm ordIso_symmetric}, rtac conjunct1, rtac conjunct2, atac];
    fun internalize_tac card_of = EVERY' [rtac subst, rtac @{thm internalize_card_of_ordLeq2},
      rtac @{thm ordLeq_ordIso_trans}, rtac card_of, rtac subst,
      rtac @{thm Card_order_iff_ordIso_card_of}, rtac @{thm Card_order_cexp}];
  in
    (rtac rev_mp THEN'
    REPEAT_DETERM_N (2 * n) o (rtac mp THEN' rtac @{thm ex_mono} THEN' rtac impI) THEN'
    REPEAT_DETERM_N (n + 1) o etac thin_rl THEN' rtac (alg_min_alg RS copy_alg_ex) THEN'
    REPEAT_DETERM_N n o atac THEN'
    REPEAT_DETERM_N n o card_of_ordIso_tac THEN'
    EVERY' (map internalize_tac card_of_min_algs) THEN'
    rtac impI THEN'
    REPEAT_DETERM o eresolve_tac [exE, conjE] THEN'
    REPEAT_DETERM o rtac exI THEN'
    rtac mor_select THEN' atac THEN' rtac CollectI THEN'
    REPEAT_DETERM o rtac exI THEN'
    rtac conjI THEN' rtac refl THEN' atac THEN'
    K (unfold_thms_tac ctxt (Abs_inverse :: fst_snd_convs)) THEN'
    etac mor_comp THEN' etac mor_incl_min_alg) 1
  end;

fun mk_init_unique_mor_tac m
    alg_def alg_min_alg least_min_algs in_monos alg_sets morEs map_cong0s =
  let
    val n = length least_min_algs;
    val ks = (1 upto n);

    fun mor_tac morE in_mono = EVERY' [etac morE, rtac set_mp, rtac in_mono,
      REPEAT_DETERM_N n o rtac @{thm Collect_restrict}, rtac CollectI,
      REPEAT_DETERM_N (m + n) o (TRY o rtac conjI THEN' atac)];
    fun cong_tac map_cong0 = EVERY' [rtac (map_cong0 RS arg_cong),
      REPEAT_DETERM_N m o rtac refl,
      REPEAT_DETERM_N n o (etac @{thm prop_restrict} THEN' atac)];

    fun mk_alg_tac (alg_set, (in_mono, (morE, map_cong0))) = EVERY' [rtac ballI, rtac CollectI,
      REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac conjI, rtac (alg_min_alg RS alg_set),
      REPEAT_DETERM_N m o rtac subset_UNIV,
      REPEAT_DETERM_N n o (etac subset_trans THEN' rtac @{thm Collect_restrict}),
      rtac trans, mor_tac morE in_mono,
      rtac trans, cong_tac map_cong0,
      rtac sym, mor_tac morE in_mono];

    fun mk_unique_tac (k, least_min_alg) =
      select_prem_tac n (etac @{thm prop_restrict}) k THEN' rtac least_min_alg THEN'
      stac alg_def THEN'
      CONJ_WRAP' mk_alg_tac (alg_sets ~~ (in_monos ~~ (morEs ~~ map_cong0s)));
  in
    CONJ_WRAP' mk_unique_tac (ks ~~ least_min_algs) 1
  end;

fun mk_init_induct_tac m alg_def alg_min_alg least_min_algs alg_sets =
  let
    val n = length least_min_algs;

    fun mk_alg_tac alg_set = EVERY' [rtac ballI, rtac CollectI,
      REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac conjI, rtac (alg_min_alg RS alg_set),
      REPEAT_DETERM_N m o rtac subset_UNIV,
      REPEAT_DETERM_N n o (etac subset_trans THEN' rtac @{thm Collect_restrict}),
      rtac mp, etac bspec, rtac CollectI,
      REPEAT_DETERM_N m o (rtac conjI THEN' atac),
      CONJ_WRAP' (K (etac subset_trans THEN' rtac @{thm Collect_restrict})) alg_sets,
      CONJ_WRAP' (K (rtac ballI THEN' etac @{thm prop_restrict} THEN' atac)) alg_sets];

    fun mk_induct_tac least_min_alg =
      rtac ballI THEN' etac @{thm prop_restrict} THEN' rtac least_min_alg THEN'
      stac alg_def THEN'
      CONJ_WRAP' mk_alg_tac alg_sets;
  in
    CONJ_WRAP' mk_induct_tac least_min_algs 1
  end;

fun mk_mor_Rep_tac ctor_defs copy bijs inver_Abss inver_Reps {context = ctxt, prems = _} =
  (K (unfold_thms_tac ctxt ctor_defs) THEN' rtac conjunct1 THEN' rtac copy THEN'
  EVERY' (map (fn bij => EVERY' [rtac bij, atac, etac bexI, rtac UNIV_I]) bijs) THEN'
  EVERY' (map rtac inver_Abss) THEN'
  EVERY' (map rtac inver_Reps)) 1;

fun mk_mor_Abs_tac inv inver_Abss inver_Reps =
  (rtac inv THEN'
  EVERY' (map2 (fn inver_Abs => fn inver_Rep =>
    EVERY' [rtac conjI, rtac subset_UNIV, rtac conjI, rtac inver_Rep, rtac inver_Abs])
    inver_Abss inver_Reps)) 1;

fun mk_mor_fold_tac cT ct fold_defs ex_mor mor =
  (EVERY' (map stac fold_defs) THEN' EVERY' [rtac rev_mp, rtac ex_mor, rtac impI] THEN'
  REPEAT_DETERM_N (length fold_defs) o etac exE THEN'
  rtac (Drule.instantiate' [SOME cT] [SOME ct] @{thm someI}) THEN' etac mor) 1;

fun mk_fold_unique_mor_tac type_defs init_unique_mors Reps mor_comp mor_Abs mor_fold =
  let
    fun mk_unique type_def =
      EVERY' [rtac @{thm surj_fun_eq}, rtac (type_def RS @{thm type_definition.Abs_image}),
        rtac ballI, resolve_tac init_unique_mors,
        EVERY' (map (fn thm => atac ORELSE' rtac thm) Reps),
        rtac mor_comp, rtac mor_Abs, atac,
        rtac mor_comp, rtac mor_Abs, rtac mor_fold];
  in
    CONJ_WRAP' mk_unique type_defs 1
  end;

fun mk_dtor_o_ctor_tac dtor_def foldx map_comp_id map_cong0L ctor_o_folds =
  EVERY' [stac dtor_def, rtac ext, rtac trans, rtac o_apply, rtac trans, rtac foldx,
    rtac trans, rtac map_comp_id, rtac trans, rtac map_cong0L,
    EVERY' (map (fn thm => rtac ballI THEN' rtac (trans OF [thm RS fun_cong, id_apply]))
      ctor_o_folds),
    rtac sym, rtac id_apply] 1;

fun mk_rec_tac rec_defs foldx fst_recs {context = ctxt, prems = _}=
  unfold_thms_tac ctxt
    (rec_defs @ map (fn thm => thm RS @{thm convol_expand_snd}) fst_recs) THEN
  EVERY' [rtac trans, rtac o_apply, rtac trans, rtac (foldx RS @{thm arg_cong[of _ _ snd]}),
    rtac @{thm snd_convol'}] 1;

fun mk_rec_unique_mor_tac rec_defs fst_recs fold_unique_mor {context = ctxt, prems = _} =
  unfold_thms_tac ctxt
    (rec_defs @ map (fn thm => thm RS @{thm convol_expand_snd'}) fst_recs) THEN
  etac fold_unique_mor 1;

fun mk_ctor_induct_tac ctxt m set_mapss init_induct morEs mor_Abs Rep_invs Abs_invs Reps =
  let
    val n = length set_mapss;
    val ks = 1 upto n;

    fun mk_IH_tac Rep_inv Abs_inv set_map =
      DETERM o EVERY' [dtac meta_mp, rtac (Rep_inv RS arg_cong RS subst), etac bspec,
        dtac set_rev_mp, rtac equalityD1, rtac set_map, etac imageE,
        hyp_subst_tac ctxt, rtac (Abs_inv RS ssubst), etac set_mp, atac, atac];

    fun mk_closed_tac (k, (morE, set_maps)) =
      EVERY' [select_prem_tac n (dtac asm_rl) k, rtac ballI, rtac impI,
        rtac (mor_Abs RS morE RS arg_cong RS ssubst), atac,
        REPEAT_DETERM o eresolve_tac [CollectE, conjE], dtac @{thm meta_spec},
        EVERY' (map3 mk_IH_tac Rep_invs Abs_invs (drop m set_maps)), atac];

    fun mk_induct_tac (Rep, Rep_inv) =
      EVERY' [rtac (Rep_inv RS arg_cong RS subst), etac (Rep RSN (2, bspec))];
  in
    (rtac mp THEN' rtac impI THEN'
    DETERM o CONJ_WRAP_GEN' (etac conjE THEN' rtac conjI) mk_induct_tac (Reps ~~ Rep_invs) THEN'
    rtac init_induct THEN'
    DETERM o CONJ_WRAP' mk_closed_tac (ks ~~ (morEs ~~ set_mapss))) 1
  end;

fun mk_ctor_induct2_tac cTs cts ctor_induct weak_ctor_inducts {context = ctxt, prems = _} =
  let
    val n = length weak_ctor_inducts;
    val ks = 1 upto n;
    fun mk_inner_induct_tac induct i =
      EVERY' [rtac allI, fo_rtac induct ctxt,
        select_prem_tac n (dtac @{thm meta_spec2}) i,
        REPEAT_DETERM_N n o
          EVERY' [dtac meta_mp THEN_ALL_NEW Goal.norm_hhf_tac ctxt,
            REPEAT_DETERM o dtac @{thm meta_spec}, etac (spec RS meta_mp), atac],
        atac];
  in
    EVERY' [rtac rev_mp, rtac (Drule.instantiate' cTs cts ctor_induct),
      EVERY' (map2 mk_inner_induct_tac weak_ctor_inducts ks), rtac impI,
      REPEAT_DETERM o eresolve_tac [conjE, allE],
      CONJ_WRAP' (K atac) ks] 1
  end;

fun mk_map_tac m n foldx map_comp_id map_cong0 =
  EVERY' [rtac ext, rtac trans, rtac o_apply, rtac trans, rtac foldx, rtac trans, rtac o_apply,
    rtac trans, rtac (map_comp_id RS arg_cong), rtac trans, rtac (map_cong0 RS arg_cong),
    REPEAT_DETERM_N m o rtac refl,
    REPEAT_DETERM_N n o (EVERY' (map rtac [trans, o_apply, id_apply])),
    rtac sym, rtac o_apply] 1;

fun mk_ctor_map_unique_tac fold_unique sym_map_comps ctxt =
  rtac fold_unique 1 THEN
  unfold_thms_tac ctxt (sym_map_comps @ @{thms comp_assoc id_comp comp_id}) THEN
  ALLGOALS atac;

fun mk_set_tac foldx = EVERY' [rtac ext, rtac trans, rtac o_apply,
  rtac trans, rtac foldx, rtac sym, rtac o_apply] 1;

fun mk_ctor_set_tac set set_map set_maps =
  let
    val n = length set_maps;
    fun mk_UN thm = rtac (thm RS @{thm arg_cong[of _ _ Union]} RS trans) THEN'
      rtac @{thm Union_image_eq};
  in
    EVERY' [rtac (set RS @{thm comp_eq_dest} RS trans), rtac Un_cong,
      rtac (trans OF [set_map, trans_fun_cong_image_id_id_apply]),
      REPEAT_DETERM_N (n - 1) o rtac Un_cong,
      EVERY' (map mk_UN set_maps)] 1
  end;

fun mk_set_nat_tac m induct_tac set_mapss
    ctor_maps csets ctor_sets i {context = ctxt, prems = _} =
  let
    val n = length ctor_maps;

    fun useIH set_nat = EVERY' [rtac trans, rtac @{thm image_UN}, rtac trans, rtac @{thm UN_cong},
      rtac refl, Goal.assume_rule_tac ctxt, rtac sym, rtac trans, rtac @{thm UN_cong},
      rtac set_nat, rtac refl, rtac @{thm UN_simps(10)}];

    fun mk_set_nat cset ctor_map ctor_set set_nats =
      EVERY' [rtac trans, rtac @{thm image_cong}, rtac ctor_set, rtac refl,
        rtac sym, rtac (trans OF [ctor_map RS HOL_arg_cong cset, ctor_set RS trans]),
        rtac sym, EVERY' (map rtac [trans, @{thm image_Un}, Un_cong]),
        rtac sym, rtac (nth set_nats (i - 1)),
        REPEAT_DETERM_N (n - 1) o EVERY' (map rtac [trans, @{thm image_Un}, Un_cong]),
        EVERY' (map useIH (drop m set_nats))];
  in
    (induct_tac THEN' EVERY' (map4 mk_set_nat csets ctor_maps ctor_sets set_mapss)) 1
  end;

fun mk_set_bd_tac m induct_tac bd_Cinfinite set_bdss ctor_sets i ctxt =
  let
    val n = length ctor_sets;

    fun useIH set_bd = EVERY' [rtac @{thm UNION_Cinfinite_bound}, rtac set_bd, rtac ballI,
      Goal.assume_rule_tac ctxt, rtac bd_Cinfinite];

    fun mk_set_nat ctor_set set_bds =
      EVERY' [rtac @{thm ordIso_ordLeq_trans}, rtac @{thm card_of_ordIso_subst}, rtac ctor_set,
        rtac (bd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound})), rtac (nth set_bds (i - 1)),
        REPEAT_DETERM_N (n - 1) o rtac (bd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound})),
        EVERY' (map useIH (drop m set_bds))];
  in
    (induct_tac THEN' EVERY' (map2 mk_set_nat ctor_sets set_bdss)) 1
  end;

fun mk_mcong_tac induct_tac set_setsss map_cong0s ctor_maps {context = ctxt, prems = _} =
  let
    fun use_asm thm = EVERY' [etac bspec, etac set_rev_mp, rtac thm];

    fun useIH set_sets = EVERY' [rtac mp, Goal.assume_rule_tac ctxt,
      CONJ_WRAP' (fn thm =>
        EVERY' [rtac ballI, etac bspec, etac set_rev_mp, etac thm]) set_sets];

    fun mk_map_cong0 ctor_map map_cong0 set_setss =
      EVERY' [rtac impI, REPEAT_DETERM o etac conjE,
        rtac trans, rtac ctor_map, rtac trans, rtac (map_cong0 RS arg_cong),
        EVERY' (map use_asm (map hd set_setss)),
        EVERY' (map useIH (transpose (map tl set_setss))),
        rtac sym, rtac ctor_map];
  in
    (induct_tac THEN' EVERY' (map3 mk_map_cong0 ctor_maps map_cong0s set_setsss)) 1
  end;

fun mk_le_rel_OO_tac m induct ctor_nchotomys ctor_Irels rel_mono_strongs rel_OOs 
    {context = ctxt, prems = _} =
  EVERY' (rtac induct ::
  map4 (fn nchotomy => fn Irel => fn rel_mono => fn rel_OO =>
    EVERY' [rtac impI, etac (nchotomy RS @{thm nchotomy_relcomppE}),
      REPEAT_DETERM_N 2 o dtac (Irel RS iffD1), rtac (Irel RS iffD2),
      rtac rel_mono, rtac (rel_OO RS @{thm predicate2_eqD} RS iffD2),
      rtac @{thm relcomppI}, atac, atac,
      REPEAT_DETERM_N m o EVERY' [rtac ballI, rtac ballI, rtac impI, atac],
      REPEAT_DETERM_N (length rel_OOs) o
        EVERY' [rtac ballI, rtac ballI, Goal.assume_rule_tac ctxt]])
  ctor_nchotomys ctor_Irels rel_mono_strongs rel_OOs) 1;

(* BNF tactics *)

fun mk_map_id0_tac map_id0s unique =
  (rtac sym THEN' rtac unique THEN'
  EVERY' (map (fn thm =>
    EVERY' [rtac trans, rtac @{thm id_comp}, rtac trans, rtac sym, rtac @{thm comp_id},
      rtac (thm RS sym RS arg_cong)]) map_id0s)) 1;

fun mk_map_comp0_tac map_comp0s ctor_maps unique iplus1 =
  let
    val i = iplus1 - 1;
    val unique' = Thm.permute_prems 0 i unique;
    val map_comp0s' = drop i map_comp0s @ take i map_comp0s;
    val ctor_maps' = drop i ctor_maps @ take i ctor_maps;
    fun mk_comp comp simp =
      EVERY' [rtac ext, rtac trans, rtac o_apply, rtac trans, rtac o_apply,
        rtac trans, rtac (simp RS arg_cong), rtac trans, rtac simp,
        rtac trans, rtac (comp RS arg_cong), rtac sym, rtac o_apply];
  in
    (rtac sym THEN' rtac unique' THEN' EVERY' (map2 mk_comp map_comp0s' ctor_maps')) 1
  end;

fun mk_set_map0_tac set_nat =
  EVERY' (map rtac [ext, trans, o_apply, sym, trans, o_apply, set_nat]) 1;

fun mk_bd_card_order_tac bd_card_orders =
  CONJ_WRAP_GEN' (rtac @{thm card_order_csum}) rtac bd_card_orders 1;

fun mk_wit_tac ctxt n ctor_set wit =
  REPEAT_DETERM (atac 1 ORELSE
    EVERY' [dtac set_rev_mp, rtac equalityD1, resolve_tac ctor_set,
    REPEAT_DETERM o
      (TRY o REPEAT_DETERM o etac UnE THEN' TRY o etac @{thm UN_E} THEN'
        (eresolve_tac wit ORELSE'
        (dresolve_tac wit THEN'
          (etac FalseE ORELSE'
          EVERY' [hyp_subst_tac ctxt, dtac set_rev_mp, rtac equalityD1, resolve_tac ctor_set,
            REPEAT_DETERM_N n o etac UnE]))))] 1);

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
      EVERY' [dtac (in_Irel RS iffD1), REPEAT_DETERM o eresolve_tac [exE, conjE, CollectE],
        rtac (in_rel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
        EVERY' (map2 (fn set_map0 => fn ctor_set_incl =>
          EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac set_map0,
            rtac ord_eq_le_trans, rtac trans_fun_cong_image_id_id_apply,
            rtac (ctor_set_incl RS subset_trans), etac le_arg_cong_ctor_dtor])
        passive_set_map0s ctor_set_incls),
        CONJ_WRAP' (fn (in_Irel, (set_map0, ctor_set_set_incls)) =>
          EVERY' [rtac ord_eq_le_trans, rtac set_map0, rtac @{thm image_subsetI}, rtac CollectI,
            rtac @{thm prod_caseI}, rtac (in_Irel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
            CONJ_WRAP' (fn thm =>
              EVERY' (map etac [thm RS subset_trans, le_arg_cong_ctor_dtor]))
            ctor_set_set_incls,
            rtac conjI, rtac refl, rtac refl])
        (in_Irels ~~ (active_set_map0s ~~ ctor_set_set_inclss)),
        CONJ_WRAP' (fn conv =>
          EVERY' [rtac trans, rtac map_comp0, rtac trans, rtac map_cong0,
          REPEAT_DETERM_N m o rtac @{thm fun_cong[OF comp_id]},
          REPEAT_DETERM_N n o EVERY' (map rtac [trans, o_apply, conv]),
          rtac (ctor_inject RS iffD1), rtac trans, rtac sym, rtac ctor_map,
          etac eq_arg_cong_ctor_dtor])
        fst_snd_convs];
    val only_if_tac =
      EVERY' [dtac (in_rel RS iffD1), REPEAT_DETERM o eresolve_tac [exE, conjE, CollectE],
        rtac (in_Irel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
        CONJ_WRAP' (fn (ctor_set, passive_set_map0) =>
          EVERY' [rtac ord_eq_le_trans, rtac ctor_set, rtac @{thm Un_least},
            rtac ord_eq_le_trans, rtac @{thm box_equals[OF _ refl]},
            rtac passive_set_map0, rtac trans_fun_cong_image_id_id_apply, atac,
            CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_least}))
              (fn (active_set_map0, in_Irel) => EVERY' [rtac ord_eq_le_trans,
                rtac @{thm UN_cong[OF _ refl]}, rtac active_set_map0, rtac @{thm UN_least},
                dtac set_rev_mp, etac @{thm image_mono}, etac imageE,
                dtac @{thm ssubst_mem[OF pair_collapse]},
                REPEAT_DETERM o eresolve_tac (CollectE :: conjE ::
                  @{thms prod_caseE iffD1[OF Pair_eq, elim_format]}),
                hyp_subst_tac ctxt,
                dtac (in_Irel RS iffD1), dtac @{thm someI_ex}, REPEAT_DETERM o etac conjE,
                TRY o
                  EVERY' [dtac (Thm.permute_prems 0 1 @{thm ssubst_mem}), atac, hyp_subst_tac ctxt],
                REPEAT_DETERM o eresolve_tac [CollectE, conjE], atac])
            (rev (active_set_map0s ~~ in_Irels))])
        (ctor_sets ~~ passive_set_map0s),
        rtac conjI,
        REPEAT_DETERM_N 2 o EVERY' [rtac trans, rtac ctor_map, rtac (ctor_inject RS iffD2),
          rtac trans, rtac map_comp0, rtac trans, rtac map_cong0,
          REPEAT_DETERM_N m o rtac @{thm fun_cong[OF comp_id]},
          EVERY' (map (fn in_Irel => EVERY' [rtac trans, rtac o_apply, dtac set_rev_mp, atac,
            dtac @{thm ssubst_mem[OF pair_collapse]},
            REPEAT_DETERM o
              eresolve_tac (CollectE :: conjE :: @{thms prod_caseE iffD1[OF Pair_eq, elim_format]}),
            hyp_subst_tac ctxt,
            dtac (in_Irel RS iffD1), dtac @{thm someI_ex}, REPEAT_DETERM o etac conjE, atac])
          in_Irels),
          atac]]
  in
    EVERY' [rtac iffI, if_tac, only_if_tac] 1
  end;

fun mk_rel_induct_tac m ctor_induct2 ks ctor_rels rel_mono_strongs {context = ctxt, prems = IHs} =
  let val n = length ks;
  in
    unfold_tac ctxt @{thms le_fun_def le_bool_def all_simps(1,2)[symmetric]} THEN
    EVERY' [REPEAT_DETERM o rtac allI, rtac ctor_induct2,
      EVERY' (map3 (fn IH => fn ctor_rel => fn rel_mono_strong =>
        EVERY' [rtac impI, dtac (ctor_rel RS iffD1), rtac (IH RS @{thm spec2} RS mp),
          etac rel_mono_strong,
          REPEAT_DETERM_N m o rtac @{thm ballI[OF ballI[OF imp_refl]]},
          EVERY' (map (fn j =>
            EVERY' [select_prem_tac n (dtac asm_rl) j, rtac @{thm ballI[OF ballI]},
              Goal.assume_rule_tac ctxt]) ks)])
      IHs ctor_rels rel_mono_strongs)] 1
  end;

fun mk_fold_transfer_tac m rel_induct map_transfers folds {context = ctxt, prems = _} =
  let
    val n = length map_transfers;
  in
    unfold_thms_tac ctxt
      @{thms fun_rel_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]} THEN
    unfold_thms_tac ctxt @{thms fun_rel_iff_leq_vimage2p} THEN
    HEADGOAL (EVERY'
      [REPEAT_DETERM o resolve_tac [allI, impI], rtac rel_induct,
      EVERY' (map (fn map_transfer => EVERY'
        [REPEAT_DETERM o resolve_tac [allI, impI, @{thm vimage2pI}],
        SELECT_GOAL (unfold_thms_tac ctxt folds),
        etac @{thm predicate2D_vimage2p},
        rtac (funpow (m + n + 1) (fn thm => thm RS @{thm fun_relD}) map_transfer),
        REPEAT_DETERM_N m o rtac @{thm id_transfer},
        REPEAT_DETERM_N n o rtac @{thm vimage2p_fun_rel},
        atac])
      map_transfers)])
  end;

end;
