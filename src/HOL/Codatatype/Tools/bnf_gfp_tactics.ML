(*  Title:      HOL/Codatatype/Tools/bnf_gfp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for the codatatype construction.
*)

signature BNF_GFP_TACTICS =
sig
  val mk_Lev_sbd_tac: cterm option list -> thm list -> thm list -> thm list list -> tactic
  val mk_bd_card_order_tac: thm -> tactic
  val mk_bd_cinfinite_tac: thm -> tactic
  val mk_bis_Gr_tac: thm -> thm list -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_bis_O_tac: int -> thm -> thm list -> thm list -> tactic
  val mk_bis_Union_tac: thm -> thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_bis_converse_tac: int -> thm -> thm list -> thm list -> tactic
  val mk_bis_rel_tac: int -> thm -> thm list -> thm list -> thm list -> thm list list -> tactic
  val mk_carT_set_tac: int -> int -> thm -> thm -> thm -> thm ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_card_of_carT_tac: int -> thm list -> thm -> thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_coalgT_tac: int -> thm list -> thm list -> thm list list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_coalg_final_tac: int -> thm -> thm list -> thm list -> thm list list -> thm list list ->
    tactic
  val mk_coalg_set_tac: thm -> tactic
  val mk_coalg_thePull_tac: int -> thm -> thm list -> thm list list -> (int -> tactic) list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_coind_wit_tac: thm -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_coiter_unique_mor_tac: thm list -> thm -> thm -> thm list -> tactic
  val mk_col_bd_tac: int -> int -> cterm option list -> thm list -> thm list -> thm -> thm ->
    thm list list -> tactic
  val mk_col_natural_tac: cterm option list -> thm list -> thm list -> thm list -> thm list list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_congruent_str_final_tac: int -> thm -> thm -> thm -> thm list -> tactic
  val mk_corec_tac: int -> thm list -> thm -> thm -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_equiv_lsbis_tac: thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_hset_minimal_tac: int -> thm list -> thm -> {prems: 'a, context: Proof.context} -> tactic
  val mk_hset_rec_minimal_tac: int -> cterm option list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_in_bd_tac: thm -> thm list -> thm -> thm -> thm -> thm -> thm list -> thm -> thm -> thm ->
    thm -> thm -> thm -> tactic
  val mk_incl_lsbis_tac: int -> int -> thm -> tactic
  val mk_isNode_hset_tac: int -> thm -> thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_length_Lev'_tac: thm -> tactic
  val mk_length_Lev_tac: cterm option list -> thm list -> thm list -> tactic
  val mk_map_comp_tac: int -> int -> thm list -> thm list -> thm list -> thm -> tactic
  val mk_mcong_tac: int -> (int -> tactic) -> thm list -> thm list -> thm list -> thm list list ->
    thm list list -> thm list list list -> tactic
  val mk_map_id_tac: thm list -> thm -> thm -> tactic
  val mk_map_tac: int -> int -> ctyp option -> thm -> thm -> thm -> tactic
  val mk_map_unique_tac: thm -> thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_mor_Abs_tac: thm list -> thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_mor_Rep_tac: int -> thm list -> thm list -> thm list -> thm list list -> thm list ->
    thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_mor_T_final_tac: thm -> thm list -> thm list -> tactic
  val mk_mor_UNIV_tac: thm list -> thm -> tactic
  val mk_mor_beh_tac: int -> thm -> thm -> thm list -> thm list -> thm list -> thm list ->
    thm list list -> thm list list -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list list -> thm list list list -> thm list list list ->
    thm list list list -> thm list list -> thm list list -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_mor_coiter_tac: int -> thm -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> tactic
  val mk_mor_comp_tac: thm -> thm list -> thm list -> thm list -> tactic
  val mk_mor_elim_tac: thm -> tactic
  val mk_mor_hset_rec_tac: int -> int -> cterm option list -> int -> thm list -> thm list ->
    thm list -> thm list list -> thm list list -> tactic
  val mk_mor_hset_tac: thm -> thm -> tactic
  val mk_mor_incl_tac: thm -> thm list -> tactic
  val mk_mor_str_tac: 'a list -> thm -> tactic
  val mk_mor_sum_case_tac: 'a list -> thm -> tactic
  val mk_mor_thePull_fst_tac: int -> thm -> thm list -> thm list -> (int -> tactic) list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_mor_thePull_snd_tac: int -> thm -> thm list -> thm list -> (int -> tactic) list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_mor_thePull_pick_tac: thm -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_prefCl_Lev_tac: cterm option list -> thm list -> thm list -> tactic
  val mk_pickWP_assms_tac: thm list -> thm list -> thm -> (int -> tactic)
  val mk_pick_col_tac: int -> int -> cterm option list -> thm list -> thm list -> thm list ->
    thm list list -> thm list -> (int -> tactic) list -> {prems: 'a, context: Proof.context} ->
    tactic
  val mk_raw_coind_tac: thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm list ->
    thm list -> thm list -> thm -> thm list -> tactic
  val mk_rel_coinduct_tac: 'a list -> thm -> thm -> tactic
  val mk_rel_coinduct_upto_tac: int -> ctyp option list -> cterm option list -> thm -> thm list ->
    thm list -> tactic
  val mk_rel_unfold_tac: thm list -> int -> thm -> thm -> thm -> thm -> thm list -> thm -> thm ->
    thm list -> thm list -> thm list list -> tactic
  val mk_rv_last_tac: ctyp option list -> cterm option list -> thm list -> thm list -> tactic
  val mk_sbis_lsbis_tac: thm list -> thm -> thm -> tactic
  val mk_set_Lev_tac: cterm option list -> thm list -> thm list -> thm list -> thm list ->
    thm list list -> tactic
  val mk_set_bd_tac: thm -> thm -> thm -> tactic
  val mk_set_hset_incl_hset_tac: int -> thm list -> thm -> int -> tactic
  val mk_set_image_Lev_tac: cterm option list -> thm list -> thm list -> thm list -> thm list ->
    thm list list -> thm list list -> tactic
  val mk_set_incl_hin_tac: thm list -> tactic
  val mk_set_incl_hset_tac: thm -> thm -> tactic
  val mk_set_le_tac: int -> thm -> thm list -> thm list list -> tactic
  val mk_set_natural_tac: thm -> thm -> tactic
  val mk_set_rv_Lev_tac: int -> cterm option list -> thm list -> thm list -> thm list -> thm list ->
    thm list list -> thm list list -> tactic
  val mk_set_simp_tac: int -> thm -> thm -> thm list -> tactic
  val mk_strT_hset_tac: int -> int -> int -> ctyp option list -> ctyp option list ->
    cterm option list -> thm list -> thm list -> thm list -> thm list -> thm list list ->
    thm list list -> thm list list -> thm -> thm list list -> tactic
  val mk_unf_coinduct_tac: int -> int list -> thm -> thm -> tactic
  val mk_unf_coinduct_upto_tac: int list -> ctyp option list -> cterm option list -> thm -> thm ->
    thm -> tactic
  val mk_unf_o_fld_tac: thm -> thm -> thm -> thm -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_unique_mor_tac: thm list -> thm -> tactic
  val mk_wit_tac: int -> thm list -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_wpull_tac: int -> thm -> thm -> thm -> thm -> thm -> thm list -> thm list -> tactic
end;

structure BNF_GFP_Tactics : BNF_GFP_TACTICS =
struct

open BNF_Tactics
open BNF_Util
open BNF_FP_Util
open BNF_GFP_Util

val Pair_eq_subst_id = @{thm Pair_eq[THEN subst, of "%x. x"]};
val fst_convol_fun_cong_sym = @{thm fst_convol} RS fun_cong RS sym;
val list_inject_subst_id = @{thm list.inject[THEN subst, of "%x. x"]};
val nat_induct = @{thm nat_induct};
val o_apply_trans_sym = o_apply RS trans RS sym;
val ord_eq_le_trans = @{thm ord_eq_le_trans};
val ord_eq_le_trans_trans_fun_cong_image_id_id_apply =
  @{thm ord_eq_le_trans[OF trans[OF fun_cong[OF image_id] id_apply]]};
val ordIso_ordLeq_trans = @{thm ordIso_ordLeq_trans};
val set_mp = @{thm set_mp};
val set_rev_mp = @{thm set_rev_mp};
val snd_convol_fun_cong_sym = @{thm snd_convol} RS fun_cong RS sym;
val ssubst_id = @{thm ssubst[of _ _ "%x. x"]};
val subst_id = @{thm subst[of _ _ "%x. x"]};
val trans_fun_cong_image_id_id_apply = @{thm trans[OF fun_cong[OF image_id] id_apply]};

fun mk_coalg_set_tac coalg_def =
  dtac (coalg_def RS subst_id) 1 THEN
  REPEAT_DETERM (etac conjE 1) THEN
  EVERY' [dtac @{thm rev_bspec}, atac] 1 THEN
  REPEAT_DETERM (eresolve_tac [CollectE, conjE] 1) THEN atac 1;

fun mk_mor_elim_tac mor_def =
  (dtac (subst OF [mor_def]) THEN'
  REPEAT o etac conjE THEN'
  TRY o rtac @{thm image_subsetI} THEN'
  etac bspec THEN'
  atac) 1;

fun mk_mor_incl_tac mor_def map_id's =
  (stac mor_def THEN'
  rtac conjI THEN'
  CONJ_WRAP' (K (EVERY' [rtac ballI, etac set_mp, stac @{thm id_apply}, atac]))
    map_id's THEN'
  CONJ_WRAP' (fn thm =>
   (EVERY' [rtac ballI, rtac (thm RS trans), rtac sym, rtac (@{thm id_apply} RS arg_cong)]))
  map_id's) 1;

fun mk_mor_comp_tac mor_def mor_images morEs map_comp_ids =
  let
    fun fbetw_tac image = EVERY' [rtac ballI, stac o_apply, etac image, etac image, atac];
    fun mor_tac ((mor_image, morE), map_comp_id) =
      EVERY' [rtac ballI, stac o_apply, rtac trans, rtac (map_comp_id RS sym), rtac trans,
        etac (morE RS arg_cong), atac, etac morE, etac mor_image, atac];
  in
    (stac mor_def THEN' rtac conjI THEN'
    CONJ_WRAP' fbetw_tac mor_images THEN'
    CONJ_WRAP' mor_tac ((mor_images ~~ morEs) ~~ map_comp_ids)) 1
  end;

fun mk_mor_UNIV_tac morEs mor_def =
  let
    val n = length morEs;
    fun mor_tac morE = EVERY' [rtac ext, rtac trans, rtac o_apply, rtac trans, etac morE,
      rtac UNIV_I, rtac sym, rtac o_apply];
  in
    EVERY' [rtac iffI, CONJ_WRAP' mor_tac morEs,
    stac mor_def, rtac conjI, CONJ_WRAP' (K (rtac ballI THEN' rtac UNIV_I)) morEs,
    CONJ_WRAP' (fn i =>
      EVERY' [dtac (mk_conjunctN n i), rtac ballI, etac @{thm pointfreeE}]) (1 upto n)] 1
  end;

fun mk_mor_str_tac ks mor_UNIV =
  (stac mor_UNIV THEN' CONJ_WRAP' (K (rtac refl)) ks) 1;

fun mk_mor_sum_case_tac ks mor_UNIV =
  (stac mor_UNIV THEN' CONJ_WRAP' (K (rtac @{thm sum_case_comp_Inl[symmetric]})) ks) 1;

fun mk_set_incl_hset_tac def rec_Suc =
  EVERY' (stac def ::
    map rtac [@{thm incl_UNION_I}, UNIV_I, @{thm ord_le_eq_trans}, @{thm Un_upper1},
      sym, rec_Suc]) 1;

fun mk_set_hset_incl_hset_tac n defs rec_Suc i =
  EVERY' (map (TRY oo stac) defs @
    map rtac [@{thm UN_least}, subsetI, @{thm UN_I}, UNIV_I, set_mp, equalityD2, rec_Suc, UnI2,
      mk_UnN n i] @
    [etac @{thm UN_I}, atac]) 1;

fun mk_set_incl_hin_tac incls =
  if null incls then rtac @{thm subset_UNIV} 1
  else EVERY' [rtac subsetI, rtac CollectI,
    CONJ_WRAP' (fn incl => EVERY' [rtac subset_trans, etac incl, atac]) incls] 1;

fun mk_hset_rec_minimal_tac m cts rec_0s rec_Sucs {context = ctxt, prems = _} =
  EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
    REPEAT_DETERM o rtac allI,
    CONJ_WRAP' (fn thm => EVERY'
      [rtac ord_eq_le_trans, rtac thm, rtac @{thm empty_subsetI}]) rec_0s,
    REPEAT_DETERM o rtac allI,
    CONJ_WRAP' (fn rec_Suc => EVERY'
      [rtac ord_eq_le_trans, rtac rec_Suc,
        if m = 0 then K all_tac
        else (rtac @{thm Un_least} THEN' Goal.assume_rule_tac ctxt),
        CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_least}))
          (K (EVERY' [rtac @{thm UN_least}, REPEAT_DETERM o eresolve_tac [allE, conjE],
            rtac subset_trans, atac, Goal.assume_rule_tac ctxt])) rec_0s])
      rec_Sucs] 1;

fun mk_hset_minimal_tac n hset_defs hset_rec_minimal {context = ctxt, prems = _} =
  (CONJ_WRAP' (fn def => (EVERY' [rtac ord_eq_le_trans, rtac def,
    rtac @{thm UN_least}, rtac rev_mp, rtac hset_rec_minimal,
    EVERY' (replicate ((n + 1) * n) (Goal.assume_rule_tac ctxt)), rtac impI,
    REPEAT_DETERM o eresolve_tac [allE, conjE], atac])) hset_defs) 1

fun mk_mor_hset_rec_tac m n cts j rec_0s rec_Sucs morEs set_naturalss coalg_setss =
  EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
    REPEAT_DETERM o rtac allI,
    CONJ_WRAP' (fn thm => EVERY' (map rtac [impI, thm RS trans, thm RS sym])) rec_0s,
    REPEAT_DETERM o rtac allI,
    CONJ_WRAP'
      (fn (rec_Suc, (morE, ((passive_set_naturals, active_set_naturals), coalg_sets))) =>
        EVERY' [rtac impI, rtac (rec_Suc RS trans), rtac (rec_Suc RS trans RS sym),
          if m = 0 then K all_tac
          else EVERY' [rtac @{thm Un_cong}, rtac box_equals,
            rtac (nth passive_set_naturals (j - 1) RS sym),
            rtac trans_fun_cong_image_id_id_apply, etac (morE RS arg_cong), atac],
          CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_cong}))
            (fn (i, (set_natural, coalg_set)) =>
              EVERY' [rtac sym, rtac trans, rtac (refl RSN (2, @{thm UN_cong})),
                etac (morE RS sym RS arg_cong RS trans), atac, rtac set_natural,
                rtac (@{thm UN_simps(10)} RS trans), rtac (refl RS @{thm UN_cong}),
                ftac coalg_set, atac, dtac set_mp, atac, rtac mp, rtac (mk_conjunctN n i),
                REPEAT_DETERM o etac allE, atac, atac])
            (rev ((1 upto n) ~~ (active_set_naturals ~~ coalg_sets)))])
      (rec_Sucs ~~ (morEs ~~ (map (chop m) set_naturalss ~~ map (drop m) coalg_setss)))] 1;

fun mk_mor_hset_tac hset_def mor_hset_rec =
  EVERY' [rtac (hset_def RS trans), rtac (refl RS @{thm UN_cong} RS trans), etac mor_hset_rec,
    atac, atac, rtac (hset_def RS sym)] 1

fun mk_bis_rel_tac m bis_def rel_defs map_comps map_congs set_naturalss =
  let
    val n = length rel_defs;
    val thms = ((1 upto n) ~~ map_comps ~~ map_congs ~~ set_naturalss ~~ rel_defs);

    fun mk_if_tac ((((i, map_comp), map_cong), set_naturals), rel_def) =
      EVERY' [rtac allI, rtac allI, rtac impI, dtac (mk_conjunctN n i),
        etac allE, etac allE, etac impE, atac, etac bexE, etac conjE,
        rtac (rel_def RS equalityD2 RS set_mp),
        rtac @{thm relcompI}, rtac @{thm converseI},
        EVERY' (map (fn thm =>
          EVERY' [rtac @{thm GrI}, REPEAT_DETERM o eresolve_tac [CollectE, conjE],
            rtac CollectI,
            CONJ_WRAP' (fn (i, thm) =>
              if i <= m
              then EVERY' [rtac ord_eq_le_trans, rtac thm, rtac subset_trans,
                etac @{thm image_mono}, rtac @{thm image_subsetI}, etac @{thm diagI}]
              else EVERY' [rtac ord_eq_le_trans, rtac trans, rtac thm,
                rtac trans_fun_cong_image_id_id_apply, atac])
            (1 upto (m + n) ~~ set_naturals),
            rtac trans, rtac trans, rtac map_comp, rtac map_cong, REPEAT_DETERM_N m o rtac thm,
            REPEAT_DETERM_N n o rtac (@{thm o_id} RS fun_cong), atac])
          @{thms fst_diag_id snd_diag_id})];

    fun mk_only_if_tac ((((i, map_comp), map_cong), set_naturals), rel_def) =
      EVERY' [dtac (mk_conjunctN n i), rtac allI, rtac allI, rtac impI,
        etac allE, etac allE, etac impE, atac,
        dtac (rel_def RS equalityD1 RS set_mp),
        REPEAT_DETERM o eresolve_tac [CollectE, @{thm relcompE}, @{thm converseE}],
        REPEAT_DETERM o eresolve_tac [@{thm GrE}, exE, conjE],
        REPEAT_DETERM o dtac Pair_eq_subst_id,
        REPEAT_DETERM o etac conjE,
        hyp_subst_tac,
        REPEAT_DETERM o eresolve_tac [CollectE, conjE],
        rtac bexI, rtac conjI, rtac trans, rtac map_comp,
        REPEAT_DETERM_N m o stac @{thm id_o},
        REPEAT_DETERM_N n o stac @{thm o_id},
        etac sym, rtac trans, rtac map_comp,
        REPEAT_DETERM_N m o stac @{thm id_o},
        REPEAT_DETERM_N n o stac @{thm o_id},
        rtac trans, rtac map_cong,
        REPEAT_DETERM_N m o EVERY' [rtac @{thm diagE'}, etac set_mp, atac],
        REPEAT_DETERM_N n o rtac refl,
        etac sym, rtac CollectI,
        CONJ_WRAP' (fn (i, thm) =>
          if i <= m
          then EVERY' [rtac ord_eq_le_trans, rtac thm, rtac @{thm image_subsetI},
            rtac @{thm diag_fst}, etac set_mp, atac]
          else EVERY' [rtac ord_eq_le_trans, rtac trans, rtac thm,
            rtac trans_fun_cong_image_id_id_apply, atac])
        (1 upto (m + n) ~~ set_naturals)];
  in
    EVERY' [rtac (bis_def RS trans),
      rtac iffI, etac conjE, etac conjI, CONJ_WRAP' mk_if_tac thms,
      etac conjE, etac conjI, CONJ_WRAP' mk_only_if_tac thms] 1
  end;

fun mk_bis_converse_tac m bis_rel rel_congs rel_converses =
  EVERY' [stac bis_rel, dtac (bis_rel RS subst_id),
    REPEAT_DETERM o etac conjE, rtac conjI,
    CONJ_WRAP' (K (EVERY' [rtac @{thm converse_shift}, etac subset_trans,
      rtac equalityD2, rtac @{thm converse_Times}])) rel_congs,
    CONJ_WRAP' (fn (rel_cong, rel_converse) =>
      EVERY' [rtac allI, rtac allI, rtac impI, rtac @{thm set_mp[OF equalityD2]},
        rtac (rel_cong RS trans),
        REPEAT_DETERM_N m o rtac @{thm diag_converse},
        REPEAT_DETERM_N (length rel_congs) o rtac refl,
        rtac rel_converse,
        REPEAT_DETERM o etac allE,
        rtac @{thm converseI}, etac mp, etac @{thm converseD}]) (rel_congs ~~ rel_converses)] 1;

fun mk_bis_O_tac m bis_rel rel_congs rel_Os =
  EVERY' [stac bis_rel, REPEAT_DETERM o dtac (bis_rel RS subst_id),
    REPEAT_DETERM o etac conjE, rtac conjI,
    CONJ_WRAP' (K (EVERY' [etac @{thm relcomp_subset_Sigma}, atac])) rel_congs,
    CONJ_WRAP' (fn (rel_cong, rel_O) =>
      EVERY' [rtac allI, rtac allI, rtac impI, rtac @{thm set_mp[OF equalityD2]},
        rtac (rel_cong RS trans),
        REPEAT_DETERM_N m o rtac @{thm diag_Comp},
        REPEAT_DETERM_N (length rel_congs) o rtac refl,
        rtac rel_O,
        etac @{thm relcompE},
        REPEAT_DETERM o dtac Pair_eq_subst_id,
        etac conjE, hyp_subst_tac,
        REPEAT_DETERM o etac allE, rtac @{thm relcompI},
        etac mp, atac, etac mp, atac]) (rel_congs ~~ rel_Os)] 1;

fun mk_bis_Gr_tac bis_rel rel_Grs mor_images morEs coalg_ins
  {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt (bis_rel :: @{thm diag_Gr} :: rel_Grs) THEN
  EVERY' [rtac conjI,
    CONJ_WRAP' (fn thm => rtac (@{thm Gr_incl} RS ssubst) THEN' etac thm) mor_images,
    CONJ_WRAP' (fn (coalg_in, morE) =>
      EVERY' [rtac allI, rtac allI, rtac impI, rtac @{thm GrI}, etac coalg_in,
        etac @{thm GrD1}, etac (morE RS trans), etac @{thm GrD1},
        etac (@{thm GrD2} RS arg_cong)]) (coalg_ins ~~ morEs)] 1;

fun mk_bis_Union_tac bis_def in_monos {context = ctxt, prems = _} =
  let
    val n = length in_monos;
    val ks = 1 upto n;
  in
    Local_Defs.unfold_tac ctxt [bis_def] THEN
    EVERY' [rtac conjI,
      CONJ_WRAP' (fn i =>
        EVERY' [rtac @{thm UN_least}, dtac bspec, atac,
          dtac conjunct1, etac (mk_conjunctN n i)]) ks,
      CONJ_WRAP' (fn (i, in_mono) =>
        EVERY' [rtac allI, rtac allI, rtac impI, etac @{thm UN_E}, dtac bspec, atac,
          dtac conjunct2, dtac (mk_conjunctN n i), etac allE, etac allE, dtac mp,
          atac, etac bexE, rtac bexI, atac, rtac in_mono,
          REPEAT_DETERM_N n o etac @{thm incl_UNION_I[OF _ subset_refl]},
          atac]) (ks ~~ in_monos)] 1
  end;

fun mk_sbis_lsbis_tac lsbis_defs bis_Union bis_cong =
  let
    val n = length lsbis_defs;
  in
    EVERY' [rtac (Thm.permute_prems 0 1 bis_cong), EVERY' (map rtac lsbis_defs),
      rtac bis_Union, rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, conjE, exE],
      hyp_subst_tac, etac bis_cong, EVERY' (map (rtac o mk_nth_conv n) (1 upto n))] 1
  end;

fun mk_incl_lsbis_tac n i lsbis_def =
  EVERY' [rtac @{thm xt1(3)}, rtac lsbis_def, rtac @{thm incl_UNION_I}, rtac CollectI,
    REPEAT_DETERM_N n o rtac exI, rtac conjI, rtac refl, atac, rtac equalityD2,
    rtac (mk_nth_conv n i)] 1;

fun mk_equiv_lsbis_tac sbis_lsbis lsbis_incl incl_lsbis bis_diag bis_converse bis_O =
  EVERY' [rtac (@{thm equiv_def} RS ssubst_id),

    rtac conjI, rtac (@{thm refl_on_def} RS ssubst_id),
    rtac conjI, rtac lsbis_incl, rtac ballI, rtac set_mp,
    rtac incl_lsbis, rtac bis_diag, atac, etac @{thm diagI},

    rtac conjI, rtac (@{thm sym_def} RS ssubst_id),
    rtac allI, rtac allI, rtac impI, rtac set_mp,
    rtac incl_lsbis, rtac bis_converse, rtac sbis_lsbis, etac @{thm converseI},

    rtac (@{thm trans_def} RS ssubst_id),
    rtac allI, rtac allI, rtac allI, rtac impI, rtac impI, rtac set_mp,
    rtac incl_lsbis, rtac bis_O, rtac sbis_lsbis, rtac sbis_lsbis,
    etac @{thm relcompI}, atac] 1;

fun mk_coalgT_tac m defs strT_defs set_naturalss {context = ctxt, prems = _} =
  let
    val n = length strT_defs;
    val ks = 1 upto n;
    fun coalg_tac (i, ((passive_sets, active_sets), def)) =
      EVERY' [rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
        hyp_subst_tac, rtac (def RS trans RS @{thm ssubst_mem}), etac (arg_cong RS trans),
        rtac (mk_sum_casesN n i), rtac CollectI,
        EVERY' (map (fn thm => EVERY' [rtac conjI, rtac (thm RS ord_eq_le_trans),
          etac ((trans OF [@{thm image_id} RS fun_cong, @{thm id_apply}]) RS ord_eq_le_trans)])
          passive_sets),
        CONJ_WRAP' (fn (i, thm) => EVERY' [rtac (thm RS ord_eq_le_trans),
          rtac @{thm image_subsetI}, rtac CollectI, rtac exI, rtac exI, rtac conjI, rtac refl,
          rtac conjI,
          rtac conjI, etac @{thm empty_Shift}, dtac set_rev_mp,
            etac equalityD1, etac CollectD,
          rtac conjI, etac @{thm Shift_clists},
          rtac conjI, etac @{thm Shift_prefCl},
          rtac conjI, rtac ballI,
            rtac conjI, dtac @{thm iffD1[OF ball_conj_distrib]}, dtac conjunct1,
            SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms Succ_Shift shift_def}),
            etac bspec, etac @{thm ShiftD},
            CONJ_WRAP' (fn i => EVERY' [rtac ballI, etac CollectE, dtac @{thm ShiftD},
              dtac bspec, etac thin_rl, atac, dtac conjunct2, dtac (mk_conjunctN n i),
              dtac bspec, rtac CollectI, etac @{thm set_mp[OF equalityD1[OF Succ_Shift]]},
              REPEAT_DETERM o eresolve_tac [exE, conjE], rtac exI,
              rtac conjI, rtac (@{thm shift_def} RS fun_cong RS trans),
              rtac (@{thm append_Cons} RS sym RS arg_cong RS trans), atac,
              REPEAT_DETERM_N m o (rtac conjI THEN' atac),
              CONJ_WRAP' (K (EVERY' [etac trans, rtac @{thm Collect_cong},
                rtac @{thm eqset_imp_iff}, rtac sym, rtac trans, rtac @{thm Succ_Shift},
                rtac (@{thm append_Cons} RS sym RS arg_cong)])) ks]) ks,
          rtac allI, rtac impI, REPEAT_DETERM o eresolve_tac [allE, impE],
          etac @{thm not_in_Shift}, rtac trans, rtac (@{thm shift_def} RS fun_cong), atac,
          dtac bspec, atac, dtac conjunct2, dtac (mk_conjunctN n i), dtac bspec,
          etac @{thm set_mp[OF equalityD1]}, atac,
          REPEAT_DETERM o eresolve_tac [exE, conjE], rtac exI,
          rtac conjI, rtac (@{thm shift_def} RS fun_cong RS trans),
          etac (@{thm append_Nil} RS sym RS arg_cong RS trans),
          REPEAT_DETERM_N m o (rtac conjI THEN' atac),
          CONJ_WRAP' (K (EVERY' [etac trans, rtac @{thm Collect_cong},
            rtac @{thm eqset_imp_iff}, rtac sym, rtac trans, rtac @{thm Succ_Shift},
            rtac (@{thm append_Nil} RS sym RS arg_cong)])) ks]) (ks ~~ active_sets)];
  in
    Local_Defs.unfold_tac ctxt defs THEN
    CONJ_WRAP' coalg_tac (ks ~~ (map (chop m) set_naturalss ~~ strT_defs)) 1
  end;

fun mk_card_of_carT_tac m isNode_defs sbd_sbd
  sbd_card_order sbd_Card_order sbd_Cinfinite sbd_Cnotzero in_sbds =
  let
    val n = length isNode_defs;
  in
    EVERY' [rtac (Thm.permute_prems 0 1 ctrans),
      rtac @{thm card_of_Sigma_ordLeq_Cinfinite}, rtac @{thm Cinfinite_cexp},
      if m = 0 then rtac @{thm ordLeq_refl} else rtac @{thm ordLeq_csum2},
      rtac @{thm Card_order_ctwo}, rtac @{thm Cinfinite_cexp},
      rtac @{thm ctwo_ordLeq_Cinfinite}, rtac sbd_Cinfinite, rtac sbd_Cinfinite,
      rtac ctrans, rtac @{thm card_of_diff},
      rtac ordIso_ordLeq_trans, rtac @{thm card_of_Field_ordIso},
      rtac @{thm Card_order_cpow}, rtac ordIso_ordLeq_trans,
      rtac @{thm cpow_cexp_ctwo}, rtac ctrans, rtac @{thm cexp_mono1_Cnotzero},
      if m = 0 then rtac @{thm ordLeq_refl} else rtac @{thm ordLeq_csum2},
      rtac @{thm Card_order_ctwo}, rtac @{thm ctwo_Cnotzero}, rtac @{thm Card_order_clists},
      rtac @{thm cexp_mono2_Cnotzero}, rtac ordIso_ordLeq_trans,
      rtac @{thm clists_Cinfinite},
      if n = 1 then rtac sbd_Cinfinite else rtac (sbd_Cinfinite RS @{thm Cinfinite_csum1}),
      rtac ordIso_ordLeq_trans, rtac sbd_sbd, rtac @{thm infinite_ordLeq_cexp},
      rtac sbd_Cinfinite,
      if m = 0 then rtac @{thm ctwo_Cnotzero} else rtac @{thm csum_Cnotzero2[OF ctwo_Cnotzero]},
      rtac @{thm Cnotzero_clists},
      rtac ballI, rtac ordIso_ordLeq_trans, rtac @{thm card_of_Func_Ffunc},
      rtac ordIso_ordLeq_trans, rtac @{thm Func_cexp},
      rtac ctrans, rtac @{thm cexp_mono},
      rtac @{thm ordLeq_ordIso_trans},
      CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1
          (sbd_Cinfinite RS @{thm Cinfinite_cexp[OF ordLeq_csum2[OF Card_order_ctwo]]}
        RSN (3, @{thm Un_Cinfinite_bound}))))
        (fn thm => EVERY' [rtac ctrans, rtac @{thm card_of_image}, rtac thm]) (rev in_sbds),
      rtac @{thm cexp_cong1_Cnotzero}, rtac @{thm csum_cong1},
      REPEAT_DETERM_N m o rtac @{thm csum_cong2},
      CONJ_WRAP_GEN' (rtac @{thm csum_cong})
        (K (rtac (sbd_Card_order RS @{thm card_of_Field_ordIso}))) in_sbds,
      rtac sbd_Card_order,
      rtac @{thm csum_Cnotzero2}, rtac @{thm ctwo_Cnotzero},
      rtac @{thm csum_Cnotzero2}, rtac @{thm ctwo_Cnotzero},
      rtac @{thm ordLeq_ordIso_trans}, etac @{thm clists_bound},
      rtac @{thm clists_Cinfinite}, TRY o rtac @{thm Cinfinite_csum1}, rtac sbd_Cinfinite,
      rtac disjI2, rtac @{thm cone_ordLeq_cexp}, rtac @{thm cone_ordLeq_cexp},
      rtac ctrans, rtac @{thm cone_ordLeq_ctwo}, rtac @{thm ordLeq_csum2},
      rtac @{thm Card_order_ctwo}, rtac FalseE, etac @{thm cpow_clists_czero}, atac,
      rtac @{thm card_of_Card_order},
      rtac ordIso_ordLeq_trans, rtac @{thm cexp_cprod},
      rtac @{thm csum_Cnotzero2}, rtac @{thm ctwo_Cnotzero},
      rtac ordIso_ordLeq_trans, rtac @{thm cexp_cong2_Cnotzero},
      rtac @{thm ordIso_transitive}, rtac @{thm cprod_cong2}, rtac sbd_sbd,
      rtac @{thm cprod_infinite}, rtac sbd_Cinfinite,
      rtac @{thm csum_Cnotzero2}, rtac @{thm ctwo_Cnotzero}, rtac @{thm Card_order_cprod},
      rtac ctrans, rtac @{thm cexp_mono1_Cnotzero},
      rtac ordIso_ordLeq_trans, rtac @{thm ordIso_transitive}, rtac @{thm csum_cong1},
      rtac @{thm ordIso_transitive},
      REPEAT_DETERM_N m o rtac @{thm csum_cong2},
      rtac sbd_sbd,
      BNF_Tactics.mk_rotate_eq_tac (rtac @{thm ordIso_refl} THEN'
        FIRST' [rtac @{thm card_of_Card_order},
          rtac @{thm Card_order_csum}, rtac sbd_Card_order])
        @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_com} @{thm csum_cong}
        (1 upto m + 1) (m + 1 :: (1 upto m)),
      if m = 0 then K all_tac else EVERY' [rtac @{thm ordIso_transitive}, rtac @{thm csum_assoc}],
      rtac @{thm csum_com}, rtac @{thm csum_cexp'}, rtac sbd_Cinfinite,
      if m = 0 then rtac @{thm Card_order_ctwo} else rtac @{thm Card_order_csum},
      if m = 0 then rtac @{thm ordLeq_refl} else rtac @{thm ordLeq_csum2},
      rtac @{thm Card_order_ctwo},
      rtac @{thm csum_Cnotzero2}, rtac @{thm ctwo_Cnotzero}, rtac sbd_Card_order,
      rtac ordIso_ordLeq_trans, rtac @{thm cexp_cprod_ordLeq},
      if m = 0 then rtac @{thm ctwo_Cnotzero} else rtac @{thm csum_Cnotzero2[OF ctwo_Cnotzero]},
      rtac sbd_Cinfinite, rtac sbd_Cnotzero, rtac @{thm ordLeq_refl}, rtac sbd_Card_order,
      rtac @{thm cexp_mono2_Cnotzero}, rtac @{thm infinite_ordLeq_cexp},
      rtac sbd_Cinfinite,
      if m = 0 then rtac @{thm ctwo_Cnotzero} else rtac @{thm csum_Cnotzero2[OF ctwo_Cnotzero]},
      rtac sbd_Cnotzero,
      rtac @{thm card_of_mono1}, rtac subsetI,
      REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE, @{thm prod_caseE}], hyp_subst_tac,
      rtac @{thm SigmaI}, rtac @{thm DiffI}, rtac set_mp, rtac equalityD2,
      rtac (@{thm cpow_def} RS arg_cong RS trans), rtac (@{thm Pow_def} RS arg_cong RS trans),
      rtac @{thm Field_card_of}, rtac CollectI, atac, rtac notI, etac @{thm singletonE},
      hyp_subst_tac, etac @{thm emptyE}, rtac (@{thm Ffunc_def} RS equalityD2 RS set_mp),
      rtac CollectI, rtac conjI, rtac ballI, dtac bspec, etac thin_rl, atac, dtac conjunct1,
      CONJ_WRAP_GEN' (etac disjE) (fn (i, def) => EVERY'
        [rtac (mk_UnN n i), dtac (def RS subst_id),
        REPEAT_DETERM o eresolve_tac [exE, conjE], rtac @{thm image_eqI}, atac, rtac CollectI,
        REPEAT_DETERM_N m o (rtac conjI THEN' atac),
        CONJ_WRAP' (K (EVERY' [etac ord_eq_le_trans, rtac subset_trans,
          rtac @{thm subset_UNIV}, rtac equalityD2, rtac @{thm Field_card_order},
          rtac sbd_card_order])) isNode_defs]) (1 upto n ~~ isNode_defs),
      atac] 1
  end;

fun mk_carT_set_tac n i carT_def strT_def isNode_def set_natural {context = ctxt, prems = _}=
  EVERY' [dtac (carT_def RS equalityD1 RS set_mp),
    REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
    dtac Pair_eq_subst_id,
    etac conjE, hyp_subst_tac,
    dtac (isNode_def RS subst_id),
    REPEAT_DETERM o eresolve_tac [exE, conjE],
    rtac (equalityD2 RS set_mp),
    rtac (strT_def RS arg_cong RS trans),
    etac (arg_cong RS trans),
    fo_rtac (mk_sum_casesN n i RS arg_cong RS trans) ctxt,
    rtac set_natural, rtac imageI, etac (equalityD2 RS set_mp), rtac CollectI,
    etac @{thm prefCl_Succ}, atac] 1;

fun mk_strT_hset_tac n m j arg_cong_cTs cTs cts carT_defs strT_defs isNode_defs
  set_incl_hsets set_hset_incl_hsetss coalg_setss carT_setss coalgT set_naturalss =
  let
    val set_naturals = map (fn xs => nth xs (j - 1)) set_naturalss;
    val ks = 1 upto n;
    fun base_tac (i, (cT, (strT_def, (set_incl_hset, set_natural)))) =
      CONJ_WRAP' (fn (i', (carT_def, isNode_def)) => rtac impI THEN' etac conjE THEN'
        (if i = i'
        then EVERY' [rtac @{thm xt1(4)}, rtac set_incl_hset,
          rtac (strT_def RS arg_cong RS trans), etac (arg_cong RS trans),
          rtac (Thm.permute_prems 0 1 (set_natural RS box_equals)),
          rtac (trans OF [@{thm image_id} RS fun_cong, @{thm id_apply}]),
          rtac (mk_sum_casesN n i RS (Drule.instantiate' [cT] [] arg_cong) RS sym)]
        else EVERY' [dtac (carT_def RS equalityD1 RS set_mp),
          REPEAT_DETERM o eresolve_tac [CollectE, exE], etac conjE,
          dtac conjunct2, dtac Pair_eq_subst_id, etac conjE,
          hyp_subst_tac, dtac (isNode_def RS subst_id),
          REPEAT_DETERM o eresolve_tac [exE, conjE],
          rtac (mk_InN_not_InM i i' RS notE), etac (sym RS trans), atac]))
      (ks ~~ (carT_defs ~~ isNode_defs));
    fun step_tac (i, (coalg_sets, (carT_sets, set_hset_incl_hsets))) =
      dtac (mk_conjunctN n i) THEN'
      CONJ_WRAP' (fn (coalg_set, (carT_set, set_hset_incl_hset)) =>
        EVERY' [rtac impI, etac conjE, etac impE, rtac conjI,
          rtac (coalgT RS coalg_set RS set_mp), atac, etac carT_set, atac, atac,
          etac (@{thm shift_def} RS fun_cong RS trans), etac subset_trans,
          rtac set_hset_incl_hset, etac carT_set, atac, atac])
      (coalg_sets ~~ (carT_sets ~~ set_hset_incl_hsets));
  in
    EVERY' [rtac (Drule.instantiate' cTs cts @{thm list.induct}),
      REPEAT_DETERM o rtac allI, rtac impI,
      CONJ_WRAP' base_tac
        (ks ~~ (arg_cong_cTs ~~ (strT_defs ~~ (set_incl_hsets ~~ set_naturals)))),
      REPEAT_DETERM o rtac allI, rtac impI,
      REPEAT_DETERM o eresolve_tac [allE, impE], etac @{thm ShiftI},
      CONJ_WRAP' (fn i => dtac (mk_conjunctN n i) THEN' rtac (mk_sumEN n) THEN'
        CONJ_WRAP_GEN' (K all_tac) step_tac
          (ks ~~ (drop m coalg_setss ~~ (carT_setss ~~ set_hset_incl_hsetss)))) ks] 1
  end;

fun mk_isNode_hset_tac n isNode_def strT_hsets {context = ctxt, prems = _} =
  let
    val m = length strT_hsets;
  in
    if m = 0 then atac 1
    else (Local_Defs.unfold_tac ctxt [isNode_def] THEN
      EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
        rtac exI, rtac conjI, atac,
        CONJ_WRAP' (fn (thm, i) =>  if i > m then atac
          else EVERY' [rtac (thm RS subset_trans), atac, rtac conjI, atac, atac, atac])
        (strT_hsets @ (replicate n mp) ~~ (1 upto (m + n)))] 1)
  end;

fun mk_Lev_sbd_tac cts Lev_0s Lev_Sucs to_sbdss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn Lev_0 =>
        EVERY' (map rtac [ord_eq_le_trans, Lev_0, @{thm Nil_clists}])) Lev_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (Lev_Suc, to_sbds) =>
        EVERY' [rtac ord_eq_le_trans, rtac Lev_Suc,
          CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_least}))
            (fn (i, to_sbd) => EVERY' [rtac subsetI,
              REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
              rtac @{thm Cons_clists}, rtac (mk_InN_Field n i), etac to_sbd,
              etac set_rev_mp, REPEAT_DETERM o etac allE,
              etac (mk_conjunctN n i)])
          (rev (ks ~~ to_sbds))])
      (Lev_Sucs ~~ to_sbdss)] 1
  end;

fun mk_length_Lev_tac cts Lev_0s Lev_Sucs =
  let
    val n = length Lev_0s;
    val ks = n downto 1;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn Lev_0 =>
        EVERY' [rtac impI, dtac (Lev_0 RS equalityD1 RS set_mp),
          etac @{thm singletonE}, etac ssubst, rtac @{thm list.size(3)}]) Lev_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn Lev_Suc =>
        EVERY' [rtac impI, dtac (Lev_Suc RS equalityD1 RS set_mp),
          CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
            (fn i => EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
              rtac trans, rtac @{thm length_Cons}, rtac @{thm arg_cong[of _ _ Suc]},
              REPEAT_DETERM o etac allE, dtac (mk_conjunctN n i), etac mp, atac]) ks])
      Lev_Sucs] 1
  end;

fun mk_length_Lev'_tac length_Lev =
  EVERY' [ftac length_Lev, etac ssubst, atac] 1;

fun mk_prefCl_Lev_tac cts Lev_0s Lev_Sucs =
  let
    val n = length Lev_0s;
    val ks = n downto 1;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn Lev_0 =>
        EVERY' [rtac impI, etac conjE, dtac (Lev_0 RS equalityD1 RS set_mp),
          etac @{thm singletonE}, hyp_subst_tac, dtac @{thm prefix_Nil[THEN subst, of "%x. x"]},
          hyp_subst_tac, rtac @{thm set_mp[OF equalityD2[OF trans[OF arg_cong[OF list.size(3)]]]]},
          rtac Lev_0, rtac @{thm singletonI}]) Lev_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (Lev_0, Lev_Suc) =>
        EVERY' [rtac impI, etac conjE, dtac (Lev_Suc RS equalityD1 RS set_mp),
          CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
            (fn i => EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
              dtac @{thm prefix_Cons[THEN subst, of "%x. x"]}, etac disjE, hyp_subst_tac,
              rtac @{thm set_mp[OF equalityD2[OF trans[OF arg_cong[OF list.size(3)]]]]},
              rtac Lev_0, rtac @{thm singletonI},
              REPEAT_DETERM o eresolve_tac [exE, conjE], hyp_subst_tac,
              rtac @{thm set_mp[OF equalityD2[OF trans[OF arg_cong[OF length_Cons]]]]},
              rtac Lev_Suc, rtac (mk_UnN n i), rtac CollectI, REPEAT_DETERM o rtac exI, rtac conjI,
              rtac refl, etac conjI, REPEAT_DETERM o etac allE, dtac (mk_conjunctN n i),
              etac mp, etac conjI, atac]) ks])
      (Lev_0s ~~ Lev_Sucs)] 1
  end;

fun mk_rv_last_tac cTs cts rv_Nils rv_Conss =
  let
    val n = length rv_Nils;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' cTs cts @{thm list.induct}),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn rv_Cons =>
        CONJ_WRAP' (fn (i, rv_Nil) => (EVERY' [rtac exI,
          rtac (@{thm append_Nil} RS arg_cong RS trans),
          rtac (rv_Cons RS trans), rtac (mk_sum_casesN n i RS arg_cong RS trans), rtac rv_Nil]))
        (ks ~~ rv_Nils))
      rv_Conss,
      REPEAT_DETERM o rtac allI, rtac (mk_sumEN n),
      EVERY' (map (fn i =>
        CONJ_WRAP' (fn rv_Cons => EVERY' [REPEAT_DETERM o etac allE, dtac (mk_conjunctN n i),
          CONJ_WRAP' (fn i' => EVERY' [dtac (mk_conjunctN n i'), etac exE, rtac exI,
            rtac (@{thm append_Cons} RS arg_cong RS trans),
            rtac (rv_Cons RS trans), etac (@{thm sum_case_cong} RS arg_cong RS trans),
            rtac (mk_sum_casesN n i RS arg_cong RS trans), atac])
          ks])
        rv_Conss)
      ks)] 1
  end;

fun mk_set_rv_Lev_tac m cts Lev_0s Lev_Sucs rv_Nils rv_Conss coalg_setss from_to_sbdss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (i, ((Lev_0, rv_Nil), coalg_sets)) =>
        EVERY' [rtac impI, REPEAT_DETERM o etac conjE,
          dtac (Lev_0 RS equalityD1 RS set_mp), etac @{thm singletonE}, etac ssubst,
          rtac (rv_Nil RS arg_cong RS ssubst_id),
          rtac (mk_sum_casesN n i RS ssubst_id),
          CONJ_WRAP' (fn thm => etac thm THEN' atac) (take m coalg_sets)])
      (ks ~~ ((Lev_0s ~~ rv_Nils) ~~ coalg_setss)),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((Lev_Suc, rv_Cons), (from_to_sbds, coalg_sets)) =>
        EVERY' [rtac impI, etac conjE, dtac (Lev_Suc RS equalityD1 RS set_mp),
          CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
            (fn (i, (from_to_sbd, coalg_set)) =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
              rtac (rv_Cons RS arg_cong RS ssubst_id),
              rtac (mk_sum_casesN n i RS arg_cong RS trans RS ssubst_id),
              etac (from_to_sbd RS arg_cong), REPEAT_DETERM o etac allE,
              dtac (mk_conjunctN n i), etac mp, etac conjI, etac set_rev_mp,
              etac coalg_set, atac])
          (rev (ks ~~ (from_to_sbds ~~ drop m coalg_sets)))])
      ((Lev_Sucs ~~ rv_Conss) ~~ (from_to_sbdss ~~ coalg_setss))] 1
  end;

fun mk_set_Lev_tac cts Lev_0s Lev_Sucs rv_Nils rv_Conss from_to_sbdss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((i, (Lev_0, Lev_Suc)), rv_Nil) =>
        EVERY' [rtac impI, dtac (Lev_0 RS equalityD1 RS set_mp),
          etac @{thm singletonE}, hyp_subst_tac,
          CONJ_WRAP' (fn i' => rtac impI THEN' dtac (sym RS trans) THEN' rtac rv_Nil THEN'
            (if i = i'
            then EVERY' [dtac (mk_InN_inject n i), hyp_subst_tac,
              CONJ_WRAP' (fn (i'', Lev_0'') =>
                EVERY' [rtac impI, rtac @{thm ssubst_mem[OF append_Nil]},
                  rtac (Lev_Suc RS equalityD2 RS set_mp), rtac (mk_UnN n i''),
                  rtac CollectI, REPEAT_DETERM o rtac exI, rtac conjI, rtac refl,
                  etac conjI, rtac (Lev_0'' RS equalityD2 RS set_mp),
                  rtac @{thm singletonI}])
              (ks ~~ Lev_0s)]
            else etac (mk_InN_not_InM i' i RS notE)))
          ks])
      ((ks ~~ (Lev_0s ~~ Lev_Sucs)) ~~ rv_Nils),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((Lev_Suc, rv_Cons), from_to_sbds) =>
        EVERY' [rtac impI, dtac (Lev_Suc RS equalityD1 RS set_mp),
          CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
            (fn (i, from_to_sbd) =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
                CONJ_WRAP' (fn i' => rtac impI THEN'
                  CONJ_WRAP' (fn i'' =>
                    EVERY' [rtac impI, rtac (Lev_Suc RS equalityD2 RS set_mp),
                      rtac @{thm ssubst_mem[OF append_Cons]}, rtac (mk_UnN n i),
                      rtac CollectI, REPEAT_DETERM o rtac exI, rtac conjI, rtac refl,
                      rtac conjI, atac, dtac (sym RS trans RS sym),
                      rtac (rv_Cons RS trans), rtac (mk_sum_casesN n i RS trans),
                      etac (from_to_sbd RS arg_cong), REPEAT_DETERM o etac allE,
                      dtac (mk_conjunctN n i), dtac mp, atac,
                      dtac (mk_conjunctN n i'), dtac mp, atac,
                      dtac (mk_conjunctN n i''), etac mp, atac])
                  ks)
                ks])
          (rev (ks ~~ from_to_sbds))])
      ((Lev_Sucs ~~ rv_Conss) ~~ from_to_sbdss)] 1
  end;

fun mk_set_image_Lev_tac cts Lev_0s Lev_Sucs rv_Nils rv_Conss from_to_sbdss to_sbd_injss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((i, (Lev_0, Lev_Suc)), rv_Nil) =>
        EVERY' [rtac impI, dtac (Lev_0 RS equalityD1 RS set_mp),
          etac @{thm singletonE}, hyp_subst_tac,
          CONJ_WRAP' (fn i' => rtac impI THEN'
            CONJ_WRAP' (fn i'' => rtac impI  THEN' dtac (sym RS trans) THEN' rtac rv_Nil THEN'
              (if i = i''
              then EVERY' [dtac @{thm ssubst_mem[OF sym[OF append_Nil]]},
                dtac (Lev_Suc RS equalityD1 RS set_mp), dtac (mk_InN_inject n i),
                hyp_subst_tac,
                CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
                  (fn k => REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE] THEN'
                    dtac list_inject_subst_id THEN' etac conjE THEN'
                    (if k = i'
                    then EVERY' [dtac (mk_InN_inject n k), hyp_subst_tac, etac imageI]
                    else etac (mk_InN_not_InM i' k RS notE)))
                (rev ks)]
              else etac (mk_InN_not_InM i'' i RS notE)))
            ks)
          ks])
      ((ks ~~ (Lev_0s ~~ Lev_Sucs)) ~~ rv_Nils),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((Lev_Suc, rv_Cons), (from_to_sbds, to_sbd_injs)) =>
        EVERY' [rtac impI, dtac (Lev_Suc RS equalityD1 RS set_mp),
          CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
            (fn (i, (from_to_sbd, to_sbd_inj)) =>
              REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE] THEN' hyp_subst_tac THEN'
              CONJ_WRAP' (fn i' => rtac impI THEN'
                dtac @{thm ssubst_mem[OF sym[OF append_Cons]]} THEN'
                dtac (Lev_Suc RS equalityD1 RS set_mp) THEN'
                CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE)) (fn k =>
                  REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE] THEN'
                  dtac list_inject_subst_id THEN' etac conjE THEN'
                  (if k = i
                  then EVERY' [dtac (mk_InN_inject n i),
                    dtac (Thm.permute_prems 0 2 (to_sbd_inj RS subst_id)),
                    atac, atac, hyp_subst_tac] THEN'
                    CONJ_WRAP' (fn i'' =>
                      EVERY' [rtac impI, dtac (sym RS trans),
                        rtac (rv_Cons RS trans), rtac (mk_sum_casesN n i RS arg_cong RS trans),
                        etac (from_to_sbd RS arg_cong),
                        REPEAT_DETERM o etac allE,
                        dtac (mk_conjunctN n i), dtac mp, atac,
                        dtac (mk_conjunctN n i'), dtac mp, atac,
                        dtac (mk_conjunctN n i''), etac mp, etac sym])
                    ks
                  else etac (mk_InN_not_InM i k RS notE)))
                (rev ks))
              ks)
          (rev (ks ~~ (from_to_sbds ~~ to_sbd_injs)))])
      ((Lev_Sucs ~~ rv_Conss) ~~ (from_to_sbdss ~~ to_sbd_injss))] 1
  end;

fun mk_mor_beh_tac m mor_def mor_cong beh_defs carT_defs strT_defs isNode_defs
  to_sbd_injss from_to_sbdss Lev_0s Lev_Sucs rv_Nils rv_Conss Lev_sbds length_Levs length_Lev's
  prefCl_Levs rv_lastss set_rv_Levsss set_Levsss set_image_Levsss set_naturalss coalg_setss
  map_comp_ids map_congs map_arg_congs {context = ctxt, prems = _} =
  let
    val n = length beh_defs;
    val ks = 1 upto n;

    fun fbetw_tac (i, (carT_def, (isNode_def, (Lev_0, (rv_Nil, (Lev_sbd,
      ((length_Lev, length_Lev'), (prefCl_Lev, (rv_lasts, (set_naturals,
        (coalg_sets, (set_rv_Levss, (set_Levss, set_image_Levss))))))))))))) =
      EVERY' [rtac ballI, rtac (carT_def RS equalityD2 RS set_mp),
        rtac CollectI, REPEAT_DETERM o rtac exI, rtac conjI, rtac refl, rtac conjI,
        rtac conjI,
          rtac @{thm UN_I}, rtac UNIV_I, rtac (Lev_0 RS equalityD2 RS set_mp),
          rtac @{thm singletonI},
        rtac conjI,
          rtac @{thm UN_least}, rtac Lev_sbd,
        rtac conjI,
          rtac @{thm prefCl_UN}, rtac ssubst, rtac @{thm PrefCl_def}, REPEAT_DETERM o rtac allI,
          rtac impI, etac conjE, rtac exI, rtac conjI, rtac @{thm ord_le_eq_trans},
          etac @{thm prefix_length_le}, etac length_Lev, rtac prefCl_Lev, etac conjI, atac,
        rtac conjI,
          rtac ballI, etac @{thm UN_E}, rtac conjI,
          if n = 1 then K all_tac else rtac (mk_sumEN n),
          EVERY' (map6 (fn i => fn isNode_def => fn set_naturals =>
            fn set_rv_Levs => fn set_Levs => fn set_image_Levs =>
            EVERY' [rtac (mk_disjIN n i), rtac (isNode_def RS ssubst),
              rtac exI, rtac conjI,
              (if n = 1 then rtac @{thm if_P} THEN' etac length_Lev'
              else rtac (@{thm if_P} RS arg_cong RS trans) THEN' etac length_Lev' THEN'
                etac (@{thm sum_case_cong} RS trans) THEN' rtac (mk_sum_casesN n i)),
              EVERY' (map2 (fn set_natural => fn set_rv_Lev =>
                EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac (set_natural RS trans),
                  rtac trans_fun_cong_image_id_id_apply,
                  etac set_rv_Lev, TRY o atac, etac conjI, atac])
              (take m set_naturals) set_rv_Levs),
              CONJ_WRAP' (fn (set_natural, (set_Lev, set_image_Lev)) =>
                EVERY' [rtac (set_natural RS trans), rtac equalityI, rtac @{thm image_subsetI},
                  rtac CollectI, rtac @{thm SuccI}, rtac @{thm UN_I}, rtac UNIV_I, etac set_Lev,
                  if n = 1 then rtac refl else atac, atac, rtac subsetI,
                  REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
                  rtac set_image_Lev, atac, dtac length_Lev, hyp_subst_tac, dtac length_Lev',
                  etac @{thm set_mp[OF equalityD1[OF arg_cong[OF length_append_singleton]]]},
                  if n = 1 then rtac refl else atac])
              (drop m set_naturals ~~ (set_Levs ~~ set_image_Levs))])
          ks isNode_defs set_naturalss set_rv_Levss set_Levss set_image_Levss),
          CONJ_WRAP' (fn (i, (rv_last, (isNode_def, (set_naturals,
            (set_rv_Levs, (set_Levs, set_image_Levs)))))) =>
            EVERY' [rtac ballI,
              REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
              rtac (rev_mp OF [rv_last, impI]), etac exE, rtac (isNode_def RS ssubst),
              rtac exI, rtac conjI,
              (if n = 1 then rtac @{thm if_P} THEN' etac length_Lev'
              else rtac (@{thm if_P} RS trans) THEN' etac length_Lev' THEN'
                etac (@{thm sum_case_cong} RS trans) THEN' rtac (mk_sum_casesN n i)),
              EVERY' (map2 (fn set_natural => fn set_rv_Lev =>
                EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac (set_natural RS trans),
                  rtac trans_fun_cong_image_id_id_apply,
                  etac set_rv_Lev, TRY o atac, etac conjI, atac])
              (take m set_naturals) set_rv_Levs),
              CONJ_WRAP' (fn (set_natural, (set_Lev, set_image_Lev)) =>
                EVERY' [rtac (set_natural RS trans), rtac equalityI, rtac @{thm image_subsetI},
                  rtac CollectI, rtac @{thm SuccI}, rtac @{thm UN_I}, rtac UNIV_I, etac set_Lev,
                  if n = 1 then rtac refl else atac, atac, rtac subsetI,
                  REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
                  REPEAT_DETERM_N 4 o etac thin_rl,
                  rtac set_image_Lev,
                  atac, dtac length_Lev, hyp_subst_tac, dtac length_Lev',
                  etac @{thm set_mp[OF equalityD1[OF arg_cong[OF length_append_singleton]]]},
                  if n = 1 then rtac refl else atac])
              (drop m set_naturals ~~ (set_Levs ~~ set_image_Levs))])
          (ks ~~ (rv_lasts ~~ (isNode_defs ~~ (set_naturalss ~~
            (set_rv_Levss ~~ (set_Levss ~~ set_image_Levss)))))),
        (**)
          rtac allI, rtac impI, rtac @{thm if_not_P}, rtac notI,
          etac notE, etac @{thm UN_I[OF UNIV_I]},
        (*root isNode*)
          rtac (isNode_def RS ssubst), rtac exI, rtac conjI, rtac (@{thm if_P} RS trans),
          rtac length_Lev', rtac (Lev_0 RS equalityD2 RS set_mp), rtac @{thm singletonI},
          CONVERSION (Conv.top_conv
            (K (Conv.try_conv (Conv.rewr_conv (rv_Nil RS eq_reflection)))) ctxt),
          if n = 1 then rtac refl else rtac (mk_sum_casesN n i),
          EVERY' (map2 (fn set_natural => fn coalg_set =>
            EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac (set_natural RS trans),
              rtac trans_fun_cong_image_id_id_apply, etac coalg_set, atac])
            (take m set_naturals) (take m coalg_sets)),
          CONJ_WRAP' (fn (set_natural, (set_Lev, set_image_Lev)) =>
            EVERY' [rtac (set_natural RS trans), rtac equalityI, rtac @{thm image_subsetI},
              rtac CollectI, rtac @{thm SuccI}, rtac @{thm UN_I}, rtac UNIV_I, rtac set_Lev,
              rtac (Lev_0 RS equalityD2 RS set_mp), rtac @{thm singletonI}, rtac rv_Nil,
              atac, rtac subsetI,
              REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
              rtac set_image_Lev, rtac (Lev_0 RS equalityD2 RS set_mp),
              rtac @{thm singletonI}, dtac length_Lev',
              etac @{thm set_mp[OF equalityD1[OF arg_cong[OF
                trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]]},
              rtac rv_Nil])
          (drop m set_naturals ~~ (nth set_Levss (i - 1) ~~ nth set_image_Levss (i - 1)))];

    fun mor_tac (i, (strT_def, (((Lev_0, Lev_Suc), (rv_Nil, rv_Cons)),
      ((map_comp_id, (map_cong, map_arg_cong)), (length_Lev', (from_to_sbds, to_sbd_injs)))))) =
      EVERY' [rtac ballI, rtac sym, rtac trans, rtac strT_def,
        rtac (@{thm if_P} RS
          (if n = 1 then map_arg_cong else @{thm sum_case_cong}) RS trans),
        rtac (@{thm list.size(3)} RS arg_cong RS trans RS equalityD2 RS set_mp),
        rtac Lev_0, rtac @{thm singletonI},
        CONVERSION (Conv.top_conv
          (K (Conv.try_conv (Conv.rewr_conv (rv_Nil RS eq_reflection)))) ctxt),
        if n = 1 then K all_tac
        else (rtac (@{thm sum_case_cong} RS trans) THEN'
          rtac (mk_sum_casesN n i) THEN' rtac (mk_sum_casesN n i RS trans)),
        rtac (map_comp_id RS trans), rtac (map_cong OF replicate m refl),
        EVERY' (map3 (fn i' => fn to_sbd_inj => fn from_to_sbd =>
          DETERM o EVERY' [rtac trans, rtac o_apply, rtac ssubst, rtac @{thm Pair_eq}, rtac conjI,
            rtac trans, rtac @{thm Shift_def},
            rtac equalityI, rtac subsetI, etac thin_rl, etac thin_rl,
            REPEAT_DETERM o eresolve_tac [CollectE, @{thm UN_E}], dtac length_Lev', dtac asm_rl,
            etac thin_rl, dtac @{thm set_rev_mp[OF _ equalityD1]},
            rtac (@{thm length_Cons} RS arg_cong RS trans), rtac Lev_Suc,
            CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE)) (fn i'' =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
                dtac list_inject_subst_id, etac conjE,
                if i' = i'' then EVERY' [dtac (mk_InN_inject n i'),
                  dtac (Thm.permute_prems 0 2 (to_sbd_inj RS subst_id)),
                  atac, atac, hyp_subst_tac, etac @{thm UN_I[OF UNIV_I]}]
                else etac (mk_InN_not_InM i' i'' RS notE)])
            (rev ks),
            rtac @{thm UN_least}, rtac subsetI, rtac CollectI, rtac @{thm UN_I[OF UNIV_I]},
            rtac (Lev_Suc RS equalityD2 RS set_mp), rtac (mk_UnN n i'), rtac CollectI,
            REPEAT_DETERM o rtac exI, rtac conjI, rtac refl, etac conjI, atac,
            rtac trans, rtac @{thm shift_def}, rtac ssubst, rtac @{thm fun_eq_iff}, rtac allI,
            rtac @{thm if_cong}, rtac (@{thm length_Cons} RS arg_cong RS trans), rtac iffI,
            dtac asm_rl, dtac asm_rl, dtac asm_rl,
            dtac (Lev_Suc RS equalityD1 RS set_mp),
            CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE)) (fn i'' =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
                dtac list_inject_subst_id, etac conjE,
                if i' = i'' then EVERY' [dtac (mk_InN_inject n i'),
                  dtac (Thm.permute_prems 0 2 (to_sbd_inj RS subst_id)),
                  atac, atac, hyp_subst_tac, atac]
                else etac (mk_InN_not_InM i' i'' RS notE)])
            (rev ks),
            rtac (Lev_Suc RS equalityD2 RS set_mp), rtac (mk_UnN n i'), rtac CollectI,
            REPEAT_DETERM o rtac exI, rtac conjI, rtac refl, etac conjI, atac,
            CONVERSION (Conv.top_conv
              (K (Conv.try_conv (Conv.rewr_conv (rv_Cons RS eq_reflection)))) ctxt),
            if n = 1 then K all_tac
            else rtac @{thm sum_case_cong} THEN' rtac (mk_sum_casesN n i' RS trans),
            SELECT_GOAL (Local_Defs.unfold_tac ctxt [from_to_sbd]), rtac refl,
            rtac refl])
        ks to_sbd_injs from_to_sbds)];
  in
    (rtac mor_cong THEN'
    EVERY' (map (fn thm => rtac (thm RS ext)) beh_defs) THEN'
    stac mor_def THEN' rtac conjI THEN'
    CONJ_WRAP' fbetw_tac
      (ks ~~ (carT_defs ~~ (isNode_defs ~~ (Lev_0s ~~ (rv_Nils ~~ (Lev_sbds ~~
        ((length_Levs ~~ length_Lev's) ~~ (prefCl_Levs ~~ (rv_lastss ~~
          (set_naturalss ~~ (coalg_setss ~~
            (set_rv_Levsss ~~ (set_Levsss ~~ set_image_Levsss))))))))))))) THEN'
    CONJ_WRAP' mor_tac
      (ks ~~ (strT_defs ~~ (((Lev_0s ~~ Lev_Sucs) ~~ (rv_Nils ~~ rv_Conss)) ~~
        ((map_comp_ids ~~ (map_congs ~~ map_arg_congs)) ~~
          (length_Lev's ~~ (from_to_sbdss ~~ to_sbd_injss))))))) 1
  end;

fun mk_congruent_str_final_tac m lsbisE map_comp_id map_cong equiv_LSBISs =
  EVERY' [rtac @{thm congruentI}, dtac lsbisE,
    REPEAT_DETERM o eresolve_tac [CollectE, conjE, bexE], rtac (o_apply RS trans),
    etac (sym RS arg_cong RS trans), rtac (map_comp_id RS trans),
    rtac (map_cong RS trans), REPEAT_DETERM_N m o rtac refl,
    EVERY' (map (fn equiv_LSBIS =>
      EVERY' [rtac @{thm equiv_proj}, rtac equiv_LSBIS, etac set_mp, atac])
    equiv_LSBISs), rtac sym, rtac (o_apply RS trans),
    etac (sym RS arg_cong RS trans), rtac map_comp_id] 1;

fun mk_coalg_final_tac m coalg_def congruent_str_finals equiv_LSBISs set_naturalss coalgT_setss =
  EVERY' [stac coalg_def,
    CONJ_WRAP' (fn ((set_naturals, coalgT_sets), (equiv_LSBIS, congruent_str_final)) =>
      EVERY' [rtac @{thm univ_preserves}, rtac equiv_LSBIS, rtac congruent_str_final,
        rtac ballI, rtac @{thm ssubst_mem}, rtac o_apply, rtac CollectI,
        EVERY' (map2 (fn set_natural => fn coalgT_set =>
          EVERY' [rtac conjI, rtac (set_natural RS ord_eq_le_trans),
            rtac ord_eq_le_trans_trans_fun_cong_image_id_id_apply,
            etac coalgT_set])
        (take m set_naturals) (take m coalgT_sets)),
        CONJ_WRAP' (fn (equiv_LSBIS, (set_natural, coalgT_set)) =>
          EVERY' [rtac (set_natural RS ord_eq_le_trans),
            rtac @{thm image_subsetI}, rtac ssubst, rtac @{thm proj_in_iff},
            rtac equiv_LSBIS, etac set_rev_mp, etac coalgT_set])
        (equiv_LSBISs ~~ drop m (set_naturals ~~ coalgT_sets))])
    ((set_naturalss ~~ coalgT_setss) ~~ (equiv_LSBISs ~~ congruent_str_finals))] 1;

fun mk_mor_T_final_tac mor_def congruent_str_finals equiv_LSBISs =
  EVERY' [stac mor_def, rtac conjI,
    CONJ_WRAP' (fn equiv_LSBIS =>
      EVERY' [rtac ballI, rtac ssubst, rtac @{thm proj_in_iff}, rtac equiv_LSBIS, atac])
    equiv_LSBISs,
    CONJ_WRAP' (fn (equiv_LSBIS, congruent_str_final) =>
      EVERY' [rtac ballI, rtac sym, rtac trans, rtac @{thm univ_commute}, rtac equiv_LSBIS,
        rtac congruent_str_final, atac, rtac o_apply])
    (equiv_LSBISs ~~ congruent_str_finals)] 1;

fun mk_mor_Rep_tac m defs Reps Abs_inverses coalg_final_setss map_comp_ids map_congLs
  {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt defs THEN
  EVERY' [rtac conjI,
    CONJ_WRAP' (fn thm => rtac ballI THEN' rtac thm) Reps,
    CONJ_WRAP' (fn (Rep, ((map_comp_id, map_congL), coalg_final_sets)) =>
      EVERY' [rtac ballI, rtac (map_comp_id RS trans), rtac map_congL,
        EVERY' (map2 (fn Abs_inverse => fn coalg_final_set =>
          EVERY' [rtac ballI, rtac (o_apply RS trans), rtac Abs_inverse,
            etac set_rev_mp, rtac coalg_final_set, rtac Rep])
        Abs_inverses (drop m coalg_final_sets))])
    (Reps ~~ ((map_comp_ids ~~ map_congLs) ~~ coalg_final_setss))] 1;

fun mk_mor_Abs_tac defs Abs_inverses {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt defs THEN
  EVERY' [rtac conjI,
    CONJ_WRAP' (K (rtac ballI THEN' rtac UNIV_I)) Abs_inverses,
    CONJ_WRAP' (fn thm => rtac ballI THEN' etac (thm RS arg_cong RS sym)) Abs_inverses] 1;

fun mk_mor_coiter_tac m mor_UNIV unf_defs coiter_defs Abs_inverses morEs map_comp_ids map_congs =
  EVERY' [rtac ssubst_id, rtac mor_UNIV,
    CONJ_WRAP' (fn ((Abs_inverse, morE), ((unf_def, coiter_def), (map_comp_id, map_cong))) =>
      EVERY' [rtac ext, rtac (o_apply RS trans RS sym), rtac (unf_def RS trans),
        rtac (coiter_def RS arg_cong RS trans), rtac (Abs_inverse RS arg_cong RS trans),
        rtac (morE RS arg_cong RS trans), rtac (map_comp_id RS trans),
        rtac (o_apply RS trans RS sym), rtac map_cong,
        REPEAT_DETERM_N m o rtac refl,
        EVERY' (map (fn thm => rtac (thm RS trans) THEN' rtac (o_apply RS sym)) coiter_defs)])
    ((Abs_inverses ~~ morEs) ~~ ((unf_defs ~~ coiter_defs) ~~ (map_comp_ids ~~ map_congs)))] 1;

fun mk_raw_coind_tac bis_def bis_cong bis_O bis_converse bis_Gr tcoalg coalgT mor_T_final
  sbis_lsbis lsbis_incls incl_lsbiss equiv_LSBISs mor_Rep Rep_injects =
  let
    val n = length Rep_injects;
  in
    EVERY' [rtac rev_mp, ftac (bis_def RS subst_id),
      REPEAT_DETERM o etac conjE, rtac bis_cong, rtac bis_O, rtac bis_converse,
      rtac bis_Gr, rtac tcoalg, rtac mor_Rep, rtac bis_O, atac, rtac bis_Gr, rtac tcoalg,
      rtac mor_Rep, REPEAT_DETERM_N n o etac @{thm relImage_Gr},
      rtac impI, rtac rev_mp, rtac bis_cong, rtac bis_O, rtac bis_Gr, rtac coalgT,
      rtac mor_T_final, rtac bis_O, rtac sbis_lsbis, rtac bis_converse, rtac bis_Gr, rtac coalgT,
      rtac mor_T_final, EVERY' (map (fn thm => rtac (thm RS @{thm relInvImage_Gr})) lsbis_incls),
      rtac impI,
      CONJ_WRAP' (fn (Rep_inject, (equiv_LSBIS , (incl_lsbis, lsbis_incl))) =>
        EVERY' [rtac subset_trans, rtac @{thm relInvImage_UNIV_relImage}, rtac subset_trans,
          rtac @{thm relInvImage_mono}, rtac subset_trans, etac incl_lsbis,
          rtac ord_eq_le_trans, rtac @{thm sym[OF relImage_relInvImage]},
          rtac @{thm xt1(3)}, rtac @{thm Sigma_cong},
          rtac @{thm proj_image}, rtac @{thm proj_image}, rtac lsbis_incl,
          rtac subset_trans, rtac @{thm relImage_mono}, rtac incl_lsbis, atac,
          rtac @{thm relImage_proj}, rtac equiv_LSBIS, rtac @{thm relInvImage_diag},
          rtac Rep_inject])
      (Rep_injects ~~ (equiv_LSBISs ~~ (incl_lsbiss ~~ lsbis_incls)))] 1
  end;

fun mk_unique_mor_tac raw_coinds bis =
  CONJ_WRAP' (fn raw_coind =>
    EVERY' [rtac impI, rtac (bis RS raw_coind RS set_mp RS @{thm IdD}), atac,
      etac conjunct1, atac, etac conjunct2, rtac @{thm image2_eqI}, rtac refl, rtac refl, atac])
  raw_coinds 1;

fun mk_coiter_unique_mor_tac raw_coinds bis mor coiter_defs =
  CONJ_WRAP' (fn (raw_coind, coiter_def) =>
    EVERY' [rtac ext, etac (bis RS raw_coind RS set_mp RS @{thm IdD}), rtac mor,
      rtac @{thm image2_eqI}, rtac refl, rtac (coiter_def RS arg_cong RS trans),
      rtac (o_apply RS sym), rtac UNIV_I]) (raw_coinds ~~ coiter_defs) 1;

fun mk_unf_o_fld_tac fld_def coiter map_comp_id map_congL coiter_o_unfs
  {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt [fld_def] THEN EVERY' [rtac ext, rtac trans, rtac o_apply,
    rtac trans, rtac coiter, rtac trans, rtac map_comp_id, rtac trans, rtac map_congL,
    EVERY' (map (fn thm =>
      rtac ballI THEN' rtac (trans OF [thm RS fun_cong, @{thm id_apply}])) coiter_o_unfs),
    rtac sym, rtac @{thm id_apply}] 1;

fun mk_corec_tac m corec_defs coiter map_cong corec_Inls {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt corec_defs THEN EVERY' [rtac trans, rtac (o_apply RS arg_cong),
    rtac trans, rtac coiter, fo_rtac (@{thm sum.cases(2)} RS arg_cong RS trans) ctxt, rtac map_cong,
    REPEAT_DETERM_N m o rtac refl,
    EVERY' (map (fn thm => rtac @{thm sum_case_expand_Inr} THEN' rtac thm) corec_Inls)] 1;

fun mk_rel_coinduct_tac ks raw_coind bis_rel =
  EVERY' [rtac rev_mp, rtac raw_coind, rtac ssubst, rtac bis_rel, rtac conjI,
    CONJ_WRAP' (K (rtac @{thm ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]]})) ks,
    CONJ_WRAP' (K (EVERY' [rtac allI, rtac allI, rtac impI,
      REPEAT_DETERM o etac allE, etac mp, etac CollectE, etac @{thm splitD}])) ks,
    rtac impI, REPEAT_DETERM o etac conjE,
    CONJ_WRAP' (K (EVERY' [rtac impI, rtac @{thm IdD}, etac set_mp,
      rtac CollectI, etac @{thm prod_caseI}])) ks] 1;

fun mk_rel_coinduct_upto_tac m cTs cts rel_coinduct rel_monos rel_Ids =
  EVERY' [rtac rev_mp, rtac (Drule.instantiate' cTs cts rel_coinduct),
    EVERY' (map2 (fn rel_mono => fn rel_Id =>
      EVERY' [REPEAT_DETERM o resolve_tac [allI, impI], REPEAT_DETERM o etac allE,
        etac disjE, etac mp, atac, hyp_subst_tac, rtac (rel_mono RS set_mp),
        REPEAT_DETERM_N m o rtac @{thm subset_refl},
        REPEAT_DETERM_N (length rel_monos) o rtac @{thm Id_subset},
        rtac (rel_Id RS equalityD2 RS set_mp), rtac @{thm IdI}])
    rel_monos rel_Ids),
    rtac impI, REPEAT_DETERM o etac conjE,
    CONJ_WRAP' (K (rtac impI THEN' etac mp THEN' etac disjI1)) rel_Ids] 1;

fun mk_unf_coinduct_tac m ks raw_coind bis_def =
  let
    val n = length ks;
  in
    EVERY' [rtac rev_mp, rtac raw_coind, rtac ssubst, rtac bis_def, rtac conjI,
      CONJ_WRAP' (K (rtac @{thm ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]]})) ks,
      CONJ_WRAP' (fn i => EVERY' [select_prem_tac n (dtac asm_rl) i, REPEAT_DETERM o rtac allI,
        rtac impI, REPEAT_DETERM o dtac @{thm meta_spec}, etac CollectE, etac @{thm meta_impE},
        atac, etac exE, etac conjE, etac conjE, rtac bexI, rtac conjI,
        etac @{thm fst_conv[THEN subst]}, etac @{thm snd_conv[THEN subst]},
        rtac CollectI, REPEAT_DETERM_N m o (rtac conjI THEN' rtac @{thm subset_UNIV}),
        CONJ_WRAP' (fn i' => EVERY' [rtac subsetI, rtac CollectI, dtac (mk_conjunctN n i'),
          REPEAT_DETERM o etac allE, etac mp, rtac @{thm ssubst_mem[OF pair_collapse]}, atac])
        ks])
      ks,
      rtac impI,
      CONJ_WRAP' (fn i => EVERY' [rtac impI, dtac (mk_conjunctN n i),
        rtac @{thm subst[OF pair_in_Id_conv]}, etac set_mp,
        rtac CollectI, etac (refl RSN (2, @{thm subst_Pair}))]) ks] 1
  end;

fun mk_unf_coinduct_upto_tac ks cTs cts unf_coinduct bis_def bis_diag =
  EVERY' [rtac rev_mp, rtac (Drule.instantiate' cTs cts unf_coinduct),
    EVERY' (map (fn i =>
      EVERY' [etac disjE, REPEAT_DETERM o dtac @{thm meta_spec}, etac @{thm meta_mp},
        atac, rtac rev_mp, rtac subst, rtac bis_def, rtac bis_diag,
        rtac impI, dtac conjunct2, dtac (mk_conjunctN (length ks) i), REPEAT_DETERM o etac allE,
        etac impE, etac @{thm diag_UNIV_I}, REPEAT_DETERM o eresolve_tac [bexE, conjE, CollectE],
        rtac exI, rtac conjI, etac conjI, atac,
        CONJ_WRAP' (K (EVERY' [REPEAT_DETERM o resolve_tac [allI, impI],
          rtac disjI2, rtac @{thm diagE}, etac set_mp, atac])) ks])
    ks),
    rtac impI, REPEAT_DETERM o etac conjE,
    CONJ_WRAP' (K (rtac impI THEN' etac mp THEN' etac disjI1)) ks] 1;

fun mk_map_tac m n cT coiter map_comp' map_cong =
  EVERY' [rtac ext, rtac (o_apply RS trans RS sym), rtac (o_apply RS trans RS sym),
    rtac (coiter RS trans), rtac (Thm.permute_prems 0 1 (map_comp' RS box_equals)), rtac map_cong,
    REPEAT_DETERM_N m o rtac (@{thm id_o} RS fun_cong),
    REPEAT_DETERM_N n o rtac (@{thm o_id} RS fun_cong),
    rtac (o_apply RS (Drule.instantiate' [cT] [] arg_cong) RS sym)] 1;

fun mk_set_le_tac n hset_minimal set_hsets set_hset_hsetss =
  EVERY' [rtac hset_minimal,
    REPEAT_DETERM_N n o rtac @{thm Un_upper1},
    REPEAT_DETERM_N n o
      EVERY' (map3 (fn i => fn set_hset => fn set_hset_hsets =>
        EVERY' [rtac subsetI, rtac @{thm UnI2}, rtac (mk_UnN n i), etac @{thm UN_I},
          etac UnE, etac set_hset, REPEAT_DETERM_N (n - 1) o etac UnE,
          EVERY' (map (fn thm => EVERY' [etac @{thm UN_E}, etac thm, atac]) set_hset_hsets)])
      (1 upto n) set_hsets set_hset_hsetss)] 1;

fun mk_set_simp_tac n set_le set_incl_hset set_hset_incl_hsets =
  EVERY' [rtac equalityI, rtac set_le, rtac @{thm Un_least}, rtac set_incl_hset,
    REPEAT_DETERM_N (n - 1) o rtac @{thm Un_least},
    EVERY' (map (fn thm => rtac @{thm UN_least} THEN' etac thm) set_hset_incl_hsets)] 1;

fun mk_map_id_tac maps coiter_unique coiter_unf =
  EVERY' [rtac (coiter_unique RS trans), EVERY' (map (fn thm => rtac (thm RS sym)) maps),
    rtac coiter_unf] 1;

fun mk_map_comp_tac m n maps map_comps map_congs coiter_unique =
  EVERY' [rtac coiter_unique,
    EVERY' (map3 (fn map_thm => fn map_comp => fn map_cong =>
      EVERY' (map rtac
        ([@{thm o_assoc} RS trans,
        @{thm arg_cong2[of _ _ _ _ "op o"]} OF [map_comp RS sym, refl] RS trans,
        @{thm o_assoc} RS trans RS sym,
        @{thm arg_cong2[of _ _ _ _ "op o"]} OF [map_thm, refl] RS trans,
        @{thm o_assoc} RS sym RS trans, map_thm RS arg_cong RS trans, @{thm o_assoc} RS trans,
        @{thm arg_cong2[of _ _ _ _ "op o"]} OF [map_comp RS sym, refl] RS trans,
        ext, o_apply RS trans,  o_apply RS trans RS sym, map_cong] @
        replicate m (@{thm id_o} RS fun_cong) @
        replicate n (@{thm o_id} RS fun_cong))))
    maps map_comps map_congs)] 1;

fun mk_mcong_tac m coinduct_tac map_comp's map_simps map_congs set_naturalss set_hsetss
  set_hset_hsetsss =
  let
    val n = length map_comp's;
    val ks = 1 upto n;
  in
    EVERY' ([rtac rev_mp,
      coinduct_tac] @
      maps (fn (((((map_comp'_trans, map_simps_trans), map_cong), set_naturals), set_hsets),
        set_hset_hsetss) =>
        [REPEAT_DETERM o eresolve_tac [exE, conjE], hyp_subst_tac, rtac exI, rtac conjI, rtac conjI,
         rtac map_comp'_trans, rtac sym, rtac map_simps_trans, rtac map_cong,
         REPEAT_DETERM_N m o (rtac o_apply_trans_sym THEN' rtac @{thm id_apply}),
         REPEAT_DETERM_N n o rtac fst_convol_fun_cong_sym,
         rtac map_comp'_trans, rtac sym, rtac map_simps_trans, rtac map_cong,
         EVERY' (maps (fn set_hset =>
           [rtac o_apply_trans_sym, rtac (@{thm id_apply} RS trans), etac CollectE,
           REPEAT_DETERM o etac conjE, etac bspec, etac set_hset]) set_hsets),
         REPEAT_DETERM_N n o rtac snd_convol_fun_cong_sym,
         CONJ_WRAP' (fn (set_natural, set_hset_hsets) =>
           EVERY' [REPEAT_DETERM o rtac allI, rtac impI, rtac @{thm image_convolD},
             etac set_rev_mp, rtac ord_eq_le_trans, rtac set_natural,
             rtac @{thm image_mono}, rtac subsetI, rtac CollectI, etac CollectE,
             REPEAT_DETERM o etac conjE,
             CONJ_WRAP' (fn set_hset_hset =>
               EVERY' [rtac ballI, etac bspec, etac set_hset_hset, atac]) set_hset_hsets])
           (drop m set_naturals ~~ set_hset_hsetss)])
        (map (fn th => th RS trans) map_comp's ~~ map (fn th => th RS trans) map_simps ~~
          map_congs ~~ set_naturalss ~~ set_hsetss ~~ set_hset_hsetsss) @
      [rtac impI,
       CONJ_WRAP' (fn k =>
         EVERY' [rtac impI, dtac (mk_conjunctN n k), etac mp, rtac exI, rtac conjI, etac CollectI,
           rtac conjI, rtac refl, rtac refl]) ks]) 1
  end

fun mk_map_unique_tac coiter_unique map_comps {context = ctxt, prems = _} =
  rtac coiter_unique 1 THEN
  Local_Defs.unfold_tac ctxt (map (fn thm => thm RS sym) map_comps @ @{thms o_assoc id_o o_id}) THEN
  ALLGOALS (etac sym);

fun mk_col_natural_tac cts rec_0s rec_Sucs map_simps set_naturalss
  {context = ctxt, prems = _} =
  let
    val n = length map_simps;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI, SELECT_GOAL (Local_Defs.unfold_tac ctxt rec_0s),
      CONJ_WRAP' (K (rtac @{thm image_empty})) rec_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (rec_Suc, (map_simp, set_nats)) => EVERY'
        [SELECT_GOAL (Local_Defs.unfold_tac ctxt
          (rec_Suc :: map_simp :: set_nats @ @{thms image_Un image_UN UN_simps(10)})),
        rtac @{thm Un_cong}, rtac refl,
        CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_cong}))
          (fn i => EVERY' [rtac @{thm UN_cong[OF refl]},
            REPEAT_DETERM o etac allE, etac (mk_conjunctN n i)]) (n downto 1)])
      (rec_Sucs ~~ (map_simps ~~ set_naturalss))] 1
  end;

fun mk_set_natural_tac hset_def col_natural =
  EVERY' (map rtac [ext, (o_apply RS trans), (hset_def RS trans), sym,
    (o_apply RS trans), (@{thm image_cong} OF [hset_def, refl] RS trans),
    (@{thm image_UN} RS trans), (refl RS @{thm UN_cong}), col_natural]) 1;

fun mk_col_bd_tac m j cts rec_0s rec_Sucs sbd_Card_order sbd_Cinfinite set_sbdss =
  let
    val n = length rec_0s;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn rec_0 => EVERY' (map rtac [ordIso_ordLeq_trans,
        @{thm card_of_ordIso_subst}, rec_0, @{thm Card_order_empty}, sbd_Card_order])) rec_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (rec_Suc, set_sbds) => EVERY'
        [rtac ordIso_ordLeq_trans, rtac @{thm card_of_ordIso_subst}, rtac rec_Suc,
        rtac (sbd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound})), rtac (nth set_sbds (j - 1)),
        REPEAT_DETERM_N (n - 1) o rtac (sbd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound})),
        EVERY' (map2 (fn i => fn set_sbd => EVERY' [rtac @{thm UNION_Cinfinite_bound},
          rtac set_sbd, rtac ballI, REPEAT_DETERM o etac allE,
          etac (mk_conjunctN n i), rtac sbd_Cinfinite]) (1 upto n) (drop m set_sbds))])
      (rec_Sucs ~~ set_sbdss)] 1
  end;

fun mk_set_bd_tac sbd_Cinfinite hset_def col_bd =
  EVERY' (map rtac [ordIso_ordLeq_trans, @{thm card_of_ordIso_subst}, hset_def,
    ctrans, @{thm UNION_Cinfinite_bound}, ordIso_ordLeq_trans, @{thm card_of_nat},
    @{thm natLeq_ordLeq_cinfinite}, sbd_Cinfinite, ballI, col_bd, sbd_Cinfinite,
    ctrans, @{thm infinite_ordLeq_cexp}, sbd_Cinfinite, @{thm cexp_ordLeq_ccexp}]) 1;

fun mk_in_bd_tac isNode_hset isNode_hsets carT_def card_of_carT mor_image Rep_inverse mor_hsets
  sbd_Cnotzero sbd_Card_order mor_Rep coalgT mor_T_final tcoalg =
  let
    val n = length isNode_hsets;
    val in_hin_tac = rtac CollectI THEN'
      CONJ_WRAP' (fn mor_hset => EVERY' (map etac
        [mor_hset OF [coalgT, mor_T_final] RS sym RS ord_eq_le_trans,
        arg_cong RS sym RS ord_eq_le_trans,
        mor_hset OF [tcoalg, mor_Rep, UNIV_I] RS ord_eq_le_trans])) mor_hsets;
  in
    EVERY' [rtac (Thm.permute_prems 0 1 @{thm ordLeq_transitive}), rtac ctrans,
      rtac @{thm card_of_image}, rtac ordIso_ordLeq_trans,
      rtac @{thm card_of_ordIso_subst}, rtac @{thm sym[OF proj_image]}, rtac ctrans,
      rtac @{thm card_of_image}, rtac ctrans, rtac card_of_carT, rtac @{thm cexp_mono2_Cnotzero},
      rtac @{thm cexp_ordLeq_ccexp},  rtac @{thm csum_Cnotzero2}, rtac @{thm ctwo_Cnotzero},
      rtac @{thm Cnotzero_cexp}, rtac sbd_Cnotzero, rtac sbd_Card_order,
      rtac @{thm card_of_mono1}, rtac subsetI, rtac @{thm image_eqI}, rtac sym,
      rtac Rep_inverse, REPEAT_DETERM o eresolve_tac [CollectE, conjE],
      rtac set_mp, rtac equalityD2, rtac @{thm sym[OF proj_image]}, rtac imageE,
      rtac set_rev_mp, rtac mor_image, rtac mor_Rep, rtac UNIV_I, rtac equalityD2,
      rtac @{thm proj_image},  rtac @{thm image_eqI}, atac,
      ftac (carT_def RS equalityD1 RS set_mp),
      REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac,
      rtac (carT_def RS equalityD2 RS set_mp), rtac CollectI, REPEAT_DETERM o rtac exI,
      rtac conjI, rtac refl, rtac conjI, etac conjI, etac conjI, etac conjI, rtac conjI,
      rtac ballI, dtac bspec, atac, REPEAT_DETERM o etac conjE, rtac conjI,
      CONJ_WRAP_GEN' (etac disjE) (fn (i, isNode_hset) =>
        EVERY' [rtac (mk_disjIN n i), rtac isNode_hset, atac, atac, atac, in_hin_tac])
      (1 upto n ~~ isNode_hsets),
      CONJ_WRAP' (fn isNode_hset =>
        EVERY' [rtac ballI, rtac isNode_hset, atac, ftac CollectD, etac @{thm SuccD},
          etac bspec, atac, in_hin_tac])
      isNode_hsets,
      atac, rtac isNode_hset, atac, atac, atac, in_hin_tac] 1
  end;

fun mk_bd_card_order_tac sbd_card_order =
  EVERY' (map rtac [@{thm card_order_ccexp}, sbd_card_order, sbd_card_order]) 1;

fun mk_bd_cinfinite_tac sbd_Cinfinite =
  EVERY' (map rtac [@{thm cinfinite_ccexp}, @{thm ctwo_ordLeq_Cinfinite},
    sbd_Cinfinite, sbd_Cinfinite]) 1;

fun mk_pickWP_assms_tac set_incl_hsets set_incl_hins map_eq =
  let
    val m = length set_incl_hsets;
  in
    EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac CollectI,
      EVERY' (map (fn thm => rtac conjI THEN' etac (thm RS @{thm subset_trans})) set_incl_hsets),
      CONJ_WRAP' (fn thm => rtac thm THEN' REPEAT_DETERM_N m o atac) set_incl_hins,
      REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac CollectI,
      EVERY' (map (fn thm => rtac conjI THEN' etac (thm RS @{thm subset_trans})) set_incl_hsets),
      CONJ_WRAP' (fn thm => rtac thm THEN' REPEAT_DETERM_N m o atac) set_incl_hins,
      REPEAT_DETERM o eresolve_tac [CollectE, conjE], etac map_eq]
  end;

fun mk_coalg_thePull_tac m coalg_def map_wpulls set_naturalss pickWP_assms_tacs
  {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt [coalg_def] THEN
  CONJ_WRAP' (fn (map_wpull, (pickWP_assms_tac, set_naturals)) =>
    EVERY' [rtac ballI, dtac @{thm set_mp[OF equalityD1[OF thePull_def]]},
      REPEAT_DETERM o eresolve_tac [CollectE, @{thm prod_caseE}],
      hyp_subst_tac, rtac rev_mp, rtac (map_wpull RS @{thm pickWP(1)}),
      EVERY' (map (etac o mk_conjunctN m) (1 upto m)),
      pickWP_assms_tac,
      SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms o_apply prod.cases}), rtac impI,
      REPEAT_DETERM o eresolve_tac [CollectE, conjE],
      rtac CollectI,
      REPEAT_DETERM_N m o (rtac conjI THEN' rtac @{thm subset_UNIV}),
      CONJ_WRAP' (fn set_natural =>
        EVERY' [rtac ord_eq_le_trans, rtac trans, rtac set_natural,
          rtac trans_fun_cong_image_id_id_apply, atac])
      (drop m set_naturals)])
  (map_wpulls ~~ (pickWP_assms_tacs ~~ set_naturalss)) 1;

fun mk_mor_thePull_nth_tac conv pick m mor_def map_wpulls map_comps pickWP_assms_tacs
  {context = ctxt, prems = _} =
  let
    val n = length map_comps;
  in
    Local_Defs.unfold_tac ctxt [mor_def] THEN
    EVERY' [rtac conjI,
      CONJ_WRAP' (K (rtac ballI THEN' rtac UNIV_I)) (1 upto n),
      CONJ_WRAP' (fn (map_wpull, (pickWP_assms_tac, map_comp)) =>
        EVERY' [rtac ballI, dtac @{thm set_mp[OF equalityD1[OF thePull_def]]},
          REPEAT_DETERM o eresolve_tac [CollectE, @{thm prod_caseE}, conjE],
          hyp_subst_tac,
          SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms o_apply prod.cases}),
          rtac (map_comp RS trans),
          SELECT_GOAL (Local_Defs.unfold_tac ctxt (conv :: @{thms o_id id_o})),
          rtac (map_wpull RS pick), REPEAT_DETERM_N m o atac,
          pickWP_assms_tac])
      (map_wpulls ~~ (pickWP_assms_tacs ~~ map_comps))] 1
  end;

val mk_mor_thePull_fst_tac = mk_mor_thePull_nth_tac @{thm fst_conv} @{thm pickWP(2)};
val mk_mor_thePull_snd_tac = mk_mor_thePull_nth_tac @{thm snd_conv} @{thm pickWP(3)};

fun mk_mor_thePull_pick_tac mor_def coiters map_comps {context = ctxt, prems = _} =
  Local_Defs.unfold_tac ctxt [mor_def, @{thm thePull_def}] THEN rtac conjI 1 THEN
  CONJ_WRAP' (K (rtac ballI THEN' rtac UNIV_I)) coiters 1 THEN
  CONJ_WRAP' (fn (coiter, map_comp) =>
    EVERY' [rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, @{thm prod_caseE}, conjE],
      hyp_subst_tac,
      SELECT_GOAL (Local_Defs.unfold_tac ctxt (coiter :: map_comp :: @{thms comp_def id_def})),
      rtac refl])
  (coiters ~~ map_comps) 1;

fun mk_pick_col_tac m j cts rec_0s rec_Sucs coiters set_naturalss map_wpulls pickWP_assms_tacs
  {context = ctxt, prems = _} =
  let
    val n = length rec_0s;
    val ks = n downto 1;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn thm => EVERY'
        [rtac impI, rtac ord_eq_le_trans, rtac thm, rtac @{thm empty_subsetI}]) rec_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (rec_Suc, ((coiter, set_naturals), (map_wpull, pickWP_assms_tac))) =>
        EVERY' [rtac impI, dtac @{thm set_mp[OF equalityD1[OF thePull_def]]},
          REPEAT_DETERM o eresolve_tac [CollectE, @{thm prod_caseE}],
          hyp_subst_tac, rtac rev_mp, rtac (map_wpull RS @{thm pickWP(1)}),
          EVERY' (map (etac o mk_conjunctN m) (1 upto m)),
          pickWP_assms_tac,
          rtac impI, REPEAT_DETERM o eresolve_tac [CollectE, conjE],
          rtac ord_eq_le_trans, rtac rec_Suc,
          rtac @{thm Un_least},
          SELECT_GOAL (Local_Defs.unfold_tac ctxt [coiter, nth set_naturals (j - 1),
            @{thm prod.cases}]),
          etac ord_eq_le_trans_trans_fun_cong_image_id_id_apply,
          CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_least})) (fn (i, set_natural) =>
            EVERY' [rtac @{thm UN_least},
              SELECT_GOAL (Local_Defs.unfold_tac ctxt [coiter, set_natural, @{thm prod.cases}]),
              etac imageE, hyp_subst_tac, REPEAT_DETERM o etac allE,
              dtac (mk_conjunctN n i), etac mp, etac set_mp, atac])
          (ks ~~ rev (drop m set_naturals))])
      (rec_Sucs ~~ ((coiters ~~ set_naturalss) ~~ (map_wpulls ~~ pickWP_assms_tacs)))] 1
  end;

fun mk_wpull_tac m coalg_thePull mor_thePull_fst mor_thePull_snd mor_thePull_pick
  mor_unique pick_cols hset_defs =
  EVERY' [rtac (@{thm wpull_def} RS ssubst_id), REPEAT_DETERM o rtac allI, rtac impI,
    REPEAT_DETERM o etac conjE, rtac bexI, rtac conjI,
    rtac box_equals, rtac mor_unique,
    rtac coalg_thePull, REPEAT_DETERM_N (m - 1) o etac conjI, atac,
    rtac mor_thePull_pick, REPEAT_DETERM_N (m - 1) o etac conjI, atac,
    rtac mor_thePull_fst, REPEAT_DETERM_N (m - 1) o etac conjI, atac,
    rtac @{thm set_mp[OF equalityD2[OF thePull_def]]}, rtac CollectI,
    rtac @{thm prod_caseI}, etac conjI, etac conjI, atac, rtac o_apply, rtac @{thm fst_conv},
    rtac box_equals, rtac mor_unique,
    rtac coalg_thePull, REPEAT_DETERM_N (m - 1) o etac conjI, atac,
    rtac mor_thePull_pick, REPEAT_DETERM_N (m - 1) o etac conjI, atac,
    rtac mor_thePull_snd, REPEAT_DETERM_N (m - 1) o etac conjI, atac,
    rtac @{thm set_mp[OF equalityD2[OF thePull_def]]}, rtac CollectI,
    rtac @{thm prod_caseI}, etac conjI, etac conjI, atac, rtac o_apply, rtac @{thm snd_conv},
    rtac CollectI,
    CONJ_WRAP' (fn (pick, def) =>
      EVERY' [rtac (def RS ord_eq_le_trans), rtac @{thm UN_least},
        rtac pick, REPEAT_DETERM_N (m - 1) o etac conjI, atac,
        rtac @{thm set_mp[OF equalityD2[OF thePull_def]]}, rtac CollectI,
        rtac @{thm prod_caseI}, etac conjI, etac conjI, atac])
    (pick_cols ~~ hset_defs)] 1;

fun mk_wit_tac n unf_flds set_simp wit coind_wits {context = ctxt, prems = _} =
  ALLGOALS (TRY o (eresolve_tac coind_wits THEN' rtac refl)) THEN
  REPEAT_DETERM (atac 1 ORELSE
    EVERY' [dtac set_rev_mp, rtac equalityD1, resolve_tac set_simp,
    K (Local_Defs.unfold_tac ctxt unf_flds),
    REPEAT_DETERM_N n o etac UnE,
    REPEAT_DETERM o
      (TRY o REPEAT_DETERM o etac UnE THEN' TRY o etac @{thm UN_E} THEN'
        (eresolve_tac wit ORELSE'
        (dresolve_tac wit THEN'
          (etac FalseE ORELSE'
          EVERY' [hyp_subst_tac, dtac set_rev_mp, rtac equalityD1, resolve_tac set_simp,
            K (Local_Defs.unfold_tac ctxt unf_flds), REPEAT_DETERM_N n o etac UnE]))))] 1);

fun mk_coind_wit_tac induct coiters set_nats wits {context = ctxt, prems = _} =
  rtac induct 1 THEN ALLGOALS (TRY o rtac impI THEN' TRY o hyp_subst_tac) THEN
  Local_Defs.unfold_tac ctxt (coiters @ set_nats @ @{thms image_id id_apply}) THEN
  ALLGOALS (REPEAT_DETERM o etac imageE THEN' TRY o hyp_subst_tac) THEN
  ALLGOALS (TRY o
    FIRST' [rtac TrueI, rtac refl, etac (refl RSN (2, mp)), dresolve_tac wits THEN' etac FalseE])

fun mk_rel_unfold_tac in_Jrels i in_rel map_comp map_cong map_simp set_simps unf_inject unf_fld
  set_naturals set_incls set_set_inclss =
  let
    val m = length set_incls;
    val n = length set_set_inclss;
    val (passive_set_naturals, active_set_naturals) = chop m set_naturals;
    val in_Jrel = nth in_Jrels (i - 1);
    val if_tac =
      EVERY' [dtac (in_Jrel RS iffD1), REPEAT_DETERM o eresolve_tac [exE, conjE, CollectE],
        rtac (in_rel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
        EVERY' (map2 (fn set_natural => fn set_incl =>
          EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac set_natural,
            rtac ord_eq_le_trans, rtac trans_fun_cong_image_id_id_apply,
            etac (set_incl RS @{thm subset_trans})])
        passive_set_naturals set_incls),
        CONJ_WRAP' (fn (in_Jrel, (set_natural, set_set_incls)) =>
          EVERY' [rtac ord_eq_le_trans, rtac set_natural, rtac @{thm image_subsetI},
            rtac (in_Jrel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
            CONJ_WRAP' (fn thm => etac (thm RS @{thm subset_trans}) THEN' atac) set_set_incls,
            rtac conjI, rtac refl, rtac refl])
        (in_Jrels ~~ (active_set_naturals ~~ set_set_inclss)),
        CONJ_WRAP' (fn conv =>
          EVERY' [rtac trans, rtac map_comp, rtac trans, rtac map_cong,
          REPEAT_DETERM_N m o rtac @{thm fun_cong[OF o_id]},
          REPEAT_DETERM_N n o EVERY' (map rtac [trans, o_apply, conv]),
          rtac trans, rtac sym, rtac map_simp, rtac (unf_inject RS iffD2), atac])
        @{thms fst_conv snd_conv}];
    val only_if_tac =
      EVERY' [dtac (in_rel RS iffD1), REPEAT_DETERM o eresolve_tac [exE, conjE, CollectE],
        rtac (in_Jrel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
        CONJ_WRAP' (fn (set_simp, passive_set_natural) =>
          EVERY' [rtac ord_eq_le_trans, rtac set_simp, rtac @{thm Un_least},
            rtac ord_eq_le_trans, rtac box_equals, rtac passive_set_natural,
            rtac (unf_fld RS sym RS arg_cong), rtac trans_fun_cong_image_id_id_apply, atac,
            CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_least}))
              (fn (active_set_natural, in_Jrel) => EVERY' [rtac ord_eq_le_trans,
                rtac @{thm UN_cong[OF _ refl]}, rtac @{thm box_equals[OF _ _ refl]},
                rtac active_set_natural, rtac (unf_fld RS sym RS arg_cong), rtac @{thm UN_least},
                dtac set_rev_mp, etac @{thm image_mono}, etac imageE,
                dtac @{thm ssubst_mem[OF pair_collapse]}, dtac (in_Jrel RS iffD1),
                dtac @{thm someI_ex}, REPEAT_DETERM o etac conjE,
                dtac (Thm.permute_prems 0 1 @{thm ssubst_mem}), atac,
                hyp_subst_tac, REPEAT_DETERM o eresolve_tac [CollectE, conjE], atac])
            (rev (active_set_naturals ~~ in_Jrels))])
        (set_simps ~~ passive_set_naturals),
        rtac conjI,
        REPEAT_DETERM_N 2 o EVERY'[rtac (unf_inject RS iffD1), rtac trans, rtac map_simp,
          rtac box_equals, rtac map_comp, rtac (unf_fld RS sym RS arg_cong), rtac trans,
          rtac map_cong, REPEAT_DETERM_N m o rtac @{thm fun_cong[OF o_id]},
          EVERY' (map (fn in_Jrel => EVERY' [rtac trans, rtac o_apply, dtac set_rev_mp, atac,
            dtac @{thm ssubst_mem[OF pair_collapse]}, dtac (in_Jrel RS iffD1), dtac @{thm someI_ex},
            REPEAT_DETERM o etac conjE, atac]) in_Jrels),
          atac]]
  in
    EVERY' [rtac iffI, if_tac, only_if_tac] 1
  end;

end;
