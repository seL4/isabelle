(*  Title:      HOL/BNF/Tools/bnf_gfp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for the codatatype construction.
*)

signature BNF_GFP_TACTICS =
sig
  val mk_Lev_sbd_tac: Proof.context -> cterm option list -> thm list -> thm list ->
    thm list list -> tactic
  val mk_bis_Gr_tac: thm -> thm list -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_bis_O_tac: Proof.context -> int -> thm -> thm list -> thm list -> tactic
  val mk_bis_Union_tac: thm -> thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_bis_converse_tac: int -> thm -> thm list -> thm list -> tactic
  val mk_bis_rel_tac: Proof.context -> int -> thm -> thm list -> thm list -> thm list ->
    thm list list -> tactic
  val mk_coalgT_tac: int -> thm list -> thm list -> thm list list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_coalg_final_tac: int -> thm -> thm list -> thm list -> thm list list -> thm list list ->
    tactic
  val mk_coalg_set_tac: thm -> tactic
  val mk_coind_wit_tac: thm -> thm list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_col_bd_tac: int -> int -> cterm option list -> thm list -> thm list -> thm -> thm ->
    thm list list -> tactic
  val mk_col_natural_tac: cterm option list -> thm list -> thm list -> thm list -> thm list list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_congruent_str_final_tac: int -> thm -> thm -> thm -> thm list -> tactic
  val mk_corec_tac: int -> thm list -> thm -> thm -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_corec_unique_mor_tac: thm list -> thm list -> thm -> {prems: 'a, context: Proof.context} ->
    tactic
  val mk_dtor_map_coinduct_tac: int -> int list -> thm -> thm -> tactic
  val mk_dtor_coinduct_tac: int -> thm -> thm -> thm list -> tactic
  val mk_dtor_rel_tac: Proof.context -> thm list -> int -> thm -> thm -> thm -> thm -> thm list ->
    thm -> thm -> thm list -> thm list -> thm list list -> tactic
  val mk_dtor_o_ctor_tac: thm -> thm -> thm -> thm -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_equiv_lsbis_tac: thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_hset_minimal_tac: int -> thm list -> thm -> {prems: 'a, context: Proof.context} -> tactic
  val mk_hset_rec_minimal_tac: int -> cterm option list -> thm list -> thm list ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_incl_lsbis_tac: int -> int -> thm -> tactic
  val mk_length_Lev'_tac: thm -> tactic
  val mk_length_Lev_tac: Proof.context -> cterm option list -> thm list -> thm list -> tactic
  val mk_map_comp0_tac: thm list -> thm list -> thm -> tactic
  val mk_mcong_tac: Proof.context -> int -> (int -> tactic) -> thm list -> thm list -> thm list ->
    thm list list -> thm list list -> thm list list list -> tactic
  val mk_map_id0_tac: thm list -> thm -> thm -> tactic
  val mk_map_tac: int -> int -> ctyp option -> thm -> thm -> thm -> tactic
  val mk_dtor_map_unique_tac: thm -> thm list -> Proof.context -> tactic
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
  val mk_mor_comp_tac: thm -> thm list -> thm list -> thm list -> tactic
  val mk_mor_elim_tac: thm -> tactic
  val mk_mor_hset_rec_tac: int -> int -> cterm option list -> int -> thm list -> thm list ->
    thm list -> thm list list -> thm list list -> tactic
  val mk_mor_incl_tac: thm -> thm list -> tactic
  val mk_mor_str_tac: 'a list -> thm -> tactic
  val mk_mor_sum_case_tac: 'a list -> thm -> tactic
  val mk_mor_unfold_tac: int -> thm -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> tactic
  val mk_prefCl_Lev_tac: Proof.context -> cterm option list -> thm list -> thm list -> tactic
  val mk_raw_coind_tac: thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm list ->
    thm list -> thm list -> thm -> thm list -> tactic
  val mk_rel_coinduct_tac: thm list -> thm list -> thm list list -> thm list -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_rel_coinduct_coind_tac: int -> thm -> int list -> thm list -> thm list -> thm list ->
    thm list list -> thm list -> thm list -> {prems: 'a, context: Proof.context} -> tactic
  val mk_rel_coinduct_ind_tac: int -> int list -> thm list -> thm list list -> int -> thm ->
    {prems: 'a, context: Proof.context} -> tactic
  val mk_rv_last_tac: ctyp option list -> cterm option list -> thm list -> thm list -> tactic
  val mk_sbis_lsbis_tac: Proof.context -> thm list -> thm -> thm -> tactic
  val mk_set_Lev_tac: Proof.context -> cterm option list -> thm list -> thm list -> thm list ->
    thm list -> thm list list -> tactic
  val mk_set_bd_tac: thm -> thm -> thm -> tactic
  val mk_set_hset_incl_hset_tac: int -> thm list -> thm -> int -> tactic
  val mk_set_image_Lev_tac: Proof.context -> cterm option list -> thm list -> thm list ->
    thm list -> thm list -> thm list list -> thm list list -> tactic
  val mk_set_incl_hset_tac: thm -> thm -> tactic
  val mk_set_ge_tac: int  -> thm -> thm list -> tactic
  val mk_set_le_tac: int -> thm -> thm list -> thm list list -> tactic
  val mk_set_map0_tac: thm -> thm -> tactic
  val mk_set_rv_Lev_tac: Proof.context -> int -> cterm option list -> thm list -> thm list ->
    thm list -> thm list -> thm list list -> thm list list -> tactic
  val mk_unfold_unique_mor_tac: thm list -> thm -> thm -> thm list -> tactic
  val mk_unfold_transfer_tac: int -> thm -> thm list -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_wit_tac: int -> thm list -> thm list -> thm list -> thm list -> Proof.context -> tactic
  val mk_le_rel_OO_tac: thm -> thm list -> thm list -> tactic
end;

structure BNF_GFP_Tactics : BNF_GFP_TACTICS =
struct

open BNF_Tactics
open BNF_Util
open BNF_FP_Util
open BNF_GFP_Util

val fst_convol_fun_cong_sym = @{thm fst_convol} RS fun_cong RS sym;
val list_inject_iffD1 = @{thm list.inject[THEN iffD1]};
val nat_induct = @{thm nat_induct};
val o_apply_trans_sym = o_apply RS trans RS sym;
val ord_eq_le_trans = @{thm ord_eq_le_trans};
val ord_eq_le_trans_trans_fun_cong_image_id_id_apply =
  @{thm ord_eq_le_trans[OF trans[OF fun_cong[OF image_id] id_apply]]};
val ordIso_ordLeq_trans = @{thm ordIso_ordLeq_trans};
val snd_convol_fun_cong_sym = @{thm snd_convol} RS fun_cong RS sym;
val sum_case_weak_cong = @{thm sum_case_weak_cong};
val trans_fun_cong_image_id_id_apply = @{thm trans[OF fun_cong[OF image_id] id_apply]};
val Collect_splitD_set_mp = @{thm Collect_splitD[OF set_mp]};
val rev_bspec = Drule.rotate_prems 1 bspec;
val Un_cong = @{thm arg_cong2[of _ _ _ _ "op \<union>"]};
val conversep_in_rel_Id_on =
   @{thm trans[OF conversep_in_rel arg_cong[of _ _ in_rel, OF converse_Id_on]]};
val relcompp_in_rel_Id_on =
   @{thm   trans[OF relcompp_in_rel arg_cong[of _ _ in_rel, OF Id_on_Comp[symmetric]]]};
val converse_shift = @{thm converse_subset_swap} RS iffD1;

fun mk_coalg_set_tac coalg_def =
  dtac (coalg_def RS iffD1) 1 THEN
  REPEAT_DETERM (etac conjE 1) THEN
  EVERY' [dtac rev_bspec, atac] 1 THEN
  REPEAT_DETERM (eresolve_tac [CollectE, conjE] 1) THEN atac 1;

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
   (EVERY' [rtac ballI, rtac (thm RS trans), rtac sym, rtac (id_apply RS arg_cong)])) map_ids) 1;

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
      EVERY' [dtac (mk_conjunctN n i), rtac ballI, etac @{thm comp_eq_dest}]) (1 upto n)] 1
  end;

fun mk_mor_str_tac ks mor_UNIV =
  (stac mor_UNIV THEN' CONJ_WRAP' (K (rtac refl)) ks) 1;

fun mk_mor_sum_case_tac ks mor_UNIV =
  (stac mor_UNIV THEN' CONJ_WRAP' (K (rtac @{thm sum_case_o_inj(1)[symmetric]})) ks) 1;

fun mk_set_incl_hset_tac def rec_Suc =
  EVERY' (stac def ::
    map rtac [@{thm SUP_upper2}, UNIV_I, @{thm ord_le_eq_trans}, @{thm Un_upper1},
      sym, rec_Suc]) 1;

fun mk_set_hset_incl_hset_tac n defs rec_Suc i =
  EVERY' (map (TRY oo stac) defs @
    map rtac [@{thm UN_least}, subsetI, @{thm UN_I}, UNIV_I, set_mp, equalityD2, rec_Suc, UnI2,
      mk_UnIN n i] @
    [etac @{thm UN_I}, atac]) 1;

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

fun mk_mor_hset_rec_tac m n cts j rec_0s rec_Sucs morEs set_map0ss coalg_setss =
  EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
    REPEAT_DETERM o rtac allI,
    CONJ_WRAP' (fn thm => EVERY' (map rtac [impI, thm RS trans, thm RS sym])) rec_0s,
    REPEAT_DETERM o rtac allI,
    CONJ_WRAP'
      (fn (rec_Suc, (morE, ((passive_set_map0s, active_set_map0s), coalg_sets))) =>
        EVERY' [rtac impI, rtac (rec_Suc RS trans), rtac (rec_Suc RS trans RS sym),
          if m = 0 then K all_tac
          else EVERY' [rtac Un_cong, rtac box_equals,
            rtac (nth passive_set_map0s (j - 1) RS sym),
            rtac trans_fun_cong_image_id_id_apply, etac (morE RS arg_cong), atac],
          CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 Un_cong))
            (fn (i, (set_map0, coalg_set)) =>
              EVERY' [rtac sym, rtac trans, rtac (refl RSN (2, @{thm UN_cong})),
                etac (morE RS sym RS arg_cong RS trans), atac, rtac set_map0,
                rtac (@{thm UN_simps(10)} RS trans), rtac (refl RS @{thm UN_cong}),
                ftac coalg_set, atac, dtac set_mp, atac, rtac mp, rtac (mk_conjunctN n i),
                REPEAT_DETERM o etac allE, atac, atac])
            (rev ((1 upto n) ~~ (active_set_map0s ~~ coalg_sets)))])
      (rec_Sucs ~~ (morEs ~~ (map (chop m) set_map0ss ~~ map (drop m) coalg_setss)))] 1;

fun mk_bis_rel_tac ctxt m bis_def rel_OO_Grps map_comp0s map_cong0s set_map0ss =
  let
    val n = length rel_OO_Grps;
    val thms = ((1 upto n) ~~ map_comp0s ~~ map_cong0s ~~ set_map0ss ~~ rel_OO_Grps);

    fun mk_if_tac ((((i, map_comp0), map_cong0), set_map0s), rel_OO_Grp) =
      EVERY' [rtac allI, rtac allI, rtac impI, dtac (mk_conjunctN n i),
        etac allE, etac allE, etac impE, atac, etac bexE, etac conjE,
        rtac (rel_OO_Grp RS sym RS @{thm eq_refl} RS @{thm predicate2D}),
        rtac @{thm relcomppI}, rtac @{thm conversepI},
        EVERY' (map (fn thm =>
          EVERY' [rtac @{thm GrpI},
            rtac trans, rtac trans, rtac map_comp0, rtac map_cong0, REPEAT_DETERM_N m o rtac thm,
            REPEAT_DETERM_N n o rtac (@{thm o_id} RS fun_cong), atac,
            REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac CollectI,
            CONJ_WRAP' (fn (i, thm) =>
              if i <= m
              then EVERY' [rtac ord_eq_le_trans, rtac thm, rtac subset_trans,
                etac @{thm image_mono}, rtac @{thm image_subsetI},
                etac @{thm Collect_split_in_relI[OF Id_onI]}]
              else EVERY' [rtac ord_eq_le_trans, rtac trans, rtac thm,
                rtac trans_fun_cong_image_id_id_apply, etac @{thm Collect_split_in_rel_leI}])
            (1 upto (m + n) ~~ set_map0s)])
          @{thms fst_diag_id snd_diag_id})];

    fun mk_only_if_tac ((((i, map_comp0), map_cong0), set_map0s), rel_OO_Grp) =
      EVERY' [dtac (mk_conjunctN n i), rtac allI, rtac allI, rtac impI,
        etac allE, etac allE, etac impE, atac,
        dtac (rel_OO_Grp RS @{thm eq_refl} RS @{thm predicate2D}),
        REPEAT_DETERM o eresolve_tac ([CollectE, conjE, exE] @
          @{thms GrpE relcomppE conversepE CollectE Collect_split_in_rel_leE}),
        hyp_subst_tac ctxt,
        rtac bexI, rtac conjI, rtac trans, rtac map_comp0, rtac trans, rtac map_cong0,
        REPEAT_DETERM_N m o rtac (@{thm id_o} RS fun_cong),
        REPEAT_DETERM_N n o rtac (@{thm o_id} RS fun_cong),
        atac, rtac trans, rtac map_comp0, rtac trans, rtac map_cong0,
        REPEAT_DETERM_N m o rtac (@{thm id_o} RS fun_cong),
        REPEAT_DETERM_N n o rtac (@{thm o_id} RS fun_cong),
        rtac trans, rtac map_cong0,
        REPEAT_DETERM_N m o EVERY' [rtac @{thm Id_onD'}, etac set_mp, atac],
        REPEAT_DETERM_N n o rtac refl,
        atac, rtac CollectI,
        CONJ_WRAP' (fn (i, thm) =>
          if i <= m
          then EVERY' [rtac ord_eq_le_trans, rtac thm, rtac @{thm image_subsetI},
            rtac @{thm Id_on_fst}, etac set_mp, atac]
          else EVERY' [rtac ord_eq_le_trans, rtac trans, rtac thm,
            rtac trans_fun_cong_image_id_id_apply, atac])
        (1 upto (m + n) ~~ set_map0s)];
  in
    EVERY' [rtac (bis_def RS trans),
      rtac iffI, etac conjE, etac conjI, CONJ_WRAP' mk_if_tac thms,
      etac conjE, etac conjI, CONJ_WRAP' mk_only_if_tac thms] 1
  end;

fun mk_bis_converse_tac m bis_rel rel_congs rel_converseps =
  EVERY' [stac bis_rel, dtac (bis_rel RS iffD1),
    REPEAT_DETERM o etac conjE, rtac conjI,
    CONJ_WRAP' (K (EVERY' [rtac converse_shift, etac subset_trans,
      rtac equalityD2, rtac @{thm converse_Times}])) rel_congs,
    CONJ_WRAP' (fn (rel_cong, rel_conversep) =>
      EVERY' [rtac allI, rtac allI, rtac impI,
        rtac (rel_cong RS @{thm eq_refl} RS @{thm predicate2D}),
        REPEAT_DETERM_N m o rtac conversep_in_rel_Id_on,
        REPEAT_DETERM_N (length rel_congs) o rtac @{thm conversep_in_rel},
        rtac (rel_conversep RS sym RS @{thm eq_refl} RS @{thm predicate2D}),
        REPEAT_DETERM o etac allE,
        rtac @{thm conversepI}, etac mp, etac @{thm converseD}]) (rel_congs ~~ rel_converseps)] 1;

fun mk_bis_O_tac ctxt m bis_rel rel_congs rel_OOs =
  EVERY' [stac bis_rel, REPEAT_DETERM o dtac (bis_rel RS iffD1),
    REPEAT_DETERM o etac conjE, rtac conjI,
    CONJ_WRAP' (K (EVERY' [etac @{thm relcomp_subset_Sigma}, atac])) rel_congs,
    CONJ_WRAP' (fn (rel_cong, rel_OO) =>
      EVERY' [rtac allI, rtac allI, rtac impI,
        rtac (rel_cong RS @{thm eq_refl} RS @{thm predicate2D}),
        REPEAT_DETERM_N m o rtac relcompp_in_rel_Id_on,
        REPEAT_DETERM_N (length rel_congs) o rtac @{thm relcompp_in_rel},
        rtac (rel_OO RS sym RS @{thm eq_refl} RS @{thm predicate2D}),
        etac @{thm relcompE},
        REPEAT_DETERM o dtac Pair_eqD,
        etac conjE, hyp_subst_tac ctxt,
        REPEAT_DETERM o etac allE, rtac @{thm relcomppI},
        etac mp, atac, etac mp, atac]) (rel_congs ~~ rel_OOs)] 1;

fun mk_bis_Gr_tac bis_rel rel_Grps mor_images morEs coalg_ins
  {context = ctxt, prems = _} =
  unfold_thms_tac ctxt (bis_rel :: @{thm Id_on_Gr} :: @{thm in_rel_Gr} :: rel_Grps) THEN
  EVERY' [rtac conjI,
    CONJ_WRAP' (fn thm => rtac (@{thm Gr_incl} RS ssubst) THEN' etac thm) mor_images,
    CONJ_WRAP' (fn (coalg_in, morE) =>
      EVERY' [rtac allI, rtac allI, rtac impI, rtac @{thm GrpI}, etac (morE RS trans),
        etac @{thm GrD1}, etac (@{thm GrD2} RS arg_cong), etac coalg_in, etac @{thm GrD1}])
    (coalg_ins ~~ morEs)] 1;

fun mk_bis_Union_tac bis_def in_monos {context = ctxt, prems = _} =
  let
    val n = length in_monos;
    val ks = 1 upto n;
  in
    unfold_thms_tac ctxt [bis_def] THEN
    EVERY' [rtac conjI,
      CONJ_WRAP' (fn i =>
        EVERY' [rtac @{thm UN_least}, dtac bspec, atac,
          dtac conjunct1, etac (mk_conjunctN n i)]) ks,
      CONJ_WRAP' (fn (i, in_mono) =>
        EVERY' [rtac allI, rtac allI, rtac impI, etac @{thm UN_E}, dtac bspec, atac,
          dtac conjunct2, dtac (mk_conjunctN n i), etac allE, etac allE, dtac mp,
          atac, etac bexE, rtac bexI, atac, rtac in_mono,
          REPEAT_DETERM_N n o etac @{thm SUP_upper2[OF _ subset_refl]},
          atac]) (ks ~~ in_monos)] 1
  end;

fun mk_sbis_lsbis_tac ctxt lsbis_defs bis_Union bis_cong =
  let
    val n = length lsbis_defs;
  in
    EVERY' [rtac (Thm.permute_prems 0 1 bis_cong), EVERY' (map rtac lsbis_defs),
      rtac bis_Union, rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, conjE, exE],
      hyp_subst_tac ctxt, etac bis_cong, EVERY' (map (rtac o mk_nth_conv n) (1 upto n))] 1
  end;

fun mk_incl_lsbis_tac n i lsbis_def =
  EVERY' [rtac @{thm xt1(3)}, rtac lsbis_def, rtac @{thm SUP_upper2}, rtac CollectI,
    REPEAT_DETERM_N n o rtac exI, rtac conjI, rtac refl, atac, rtac equalityD2,
    rtac (mk_nth_conv n i)] 1;

fun mk_equiv_lsbis_tac sbis_lsbis lsbis_incl incl_lsbis bis_Id_on bis_converse bis_O =
  EVERY' [rtac (@{thm equiv_def} RS iffD2),

    rtac conjI, rtac (@{thm refl_on_def} RS iffD2),
    rtac conjI, rtac lsbis_incl, rtac ballI, rtac set_mp,
    rtac incl_lsbis, rtac bis_Id_on, atac, etac @{thm Id_onI},

    rtac conjI, rtac (@{thm sym_def} RS iffD2),
    rtac allI, rtac allI, rtac impI, rtac set_mp,
    rtac incl_lsbis, rtac bis_converse, rtac sbis_lsbis, etac @{thm converseI},

    rtac (@{thm trans_def} RS iffD2),
    rtac allI, rtac allI, rtac allI, rtac impI, rtac impI, rtac set_mp,
    rtac incl_lsbis, rtac bis_O, rtac sbis_lsbis, rtac sbis_lsbis,
    etac @{thm relcompI}, atac] 1;

fun mk_coalgT_tac m defs strT_defs set_map0ss {context = ctxt, prems = _} =
  let
    val n = length strT_defs;
    val ks = 1 upto n;
    fun coalg_tac (i, ((passive_sets, active_sets), def)) =
      EVERY' [rtac ballI, REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
        hyp_subst_tac ctxt, rtac (def RS trans RS @{thm ssubst_mem}), etac (arg_cong RS trans),
        rtac (mk_sum_casesN n i), rtac CollectI,
        EVERY' (map (fn thm => EVERY' [rtac conjI, rtac (thm RS ord_eq_le_trans),
          etac ((trans OF [@{thm image_id} RS fun_cong, id_apply]) RS ord_eq_le_trans)])
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
            SELECT_GOAL (unfold_thms_tac ctxt @{thms Succ_Shift shift_def}),
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
    unfold_thms_tac ctxt defs THEN
    CONJ_WRAP' coalg_tac (ks ~~ (map (chop m) set_map0ss ~~ strT_defs)) 1
  end;

fun mk_Lev_sbd_tac ctxt cts Lev_0s Lev_Sucs to_sbdss =
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
              REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac ctxt,
              rtac @{thm Cons_clists}, rtac (mk_InN_Field n i), etac to_sbd,
              etac set_rev_mp, REPEAT_DETERM o etac allE,
              etac (mk_conjunctN n i)])
          (rev (ks ~~ to_sbds))])
      (Lev_Sucs ~~ to_sbdss)] 1
  end;

fun mk_length_Lev_tac ctxt cts Lev_0s Lev_Sucs =
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
            (fn i =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac ctxt,
                rtac trans, rtac @{thm length_Cons}, rtac @{thm arg_cong[of _ _ Suc]},
                REPEAT_DETERM o etac allE, dtac (mk_conjunctN n i), etac mp, atac]) ks])
      Lev_Sucs] 1
  end;

fun mk_length_Lev'_tac length_Lev =
  EVERY' [ftac length_Lev, etac ssubst, atac] 1;

fun mk_prefCl_Lev_tac ctxt cts Lev_0s Lev_Sucs =
  let
    val n = length Lev_0s;
    val ks = n downto 1;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn Lev_0 =>
        EVERY' [rtac impI, etac conjE, dtac (Lev_0 RS equalityD1 RS set_mp),
          etac @{thm singletonE}, hyp_subst_tac ctxt,
          dtac @{thm prefixeq_Nil[THEN subst, of "%x. x"]},
          hyp_subst_tac ctxt,
          rtac @{thm set_mp[OF equalityD2[OF trans[OF arg_cong[OF list.size(3)]]]]},
          rtac Lev_0, rtac @{thm singletonI}]) Lev_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (Lev_0, Lev_Suc) =>
        EVERY' [rtac impI, etac conjE, dtac (Lev_Suc RS equalityD1 RS set_mp),
          CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
            (fn i =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac ctxt,
              dtac @{thm prefixeq_Cons[THEN subst, of "%x. x"]}, etac disjE, hyp_subst_tac ctxt,
              rtac @{thm set_mp[OF equalityD2[OF trans[OF arg_cong[OF list.size(3)]]]]},
              rtac Lev_0, rtac @{thm singletonI},
              REPEAT_DETERM o eresolve_tac [exE, conjE], hyp_subst_tac ctxt,
              rtac @{thm set_mp[OF equalityD2[OF trans[OF arg_cong[OF length_Cons]]]]},
              rtac Lev_Suc, rtac (mk_UnIN n i), rtac CollectI, REPEAT_DETERM o rtac exI, rtac conjI,
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
            rtac (rv_Cons RS trans), etac (sum_case_weak_cong RS arg_cong RS trans),
            rtac (mk_sum_casesN n i RS arg_cong RS trans), atac])
          ks])
        rv_Conss)
      ks)] 1
  end;

fun mk_set_rv_Lev_tac ctxt m cts Lev_0s Lev_Sucs rv_Nils rv_Conss coalg_setss from_to_sbdss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (i, ((Lev_0, rv_Nil), coalg_sets)) =>
        EVERY' [rtac impI, REPEAT_DETERM o etac conjE,
          dtac (Lev_0 RS equalityD1 RS set_mp), etac @{thm singletonE}, etac ssubst,
          rtac (rv_Nil RS arg_cong RS iffD2),
          rtac (mk_sum_casesN n i RS iffD2),
          CONJ_WRAP' (fn thm => etac thm THEN' atac) (take m coalg_sets)])
      (ks ~~ ((Lev_0s ~~ rv_Nils) ~~ coalg_setss)),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((Lev_Suc, rv_Cons), (from_to_sbds, coalg_sets)) =>
        EVERY' [rtac impI, etac conjE, dtac (Lev_Suc RS equalityD1 RS set_mp),
          CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
            (fn (i, (from_to_sbd, coalg_set)) =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac ctxt,
              rtac (rv_Cons RS arg_cong RS iffD2),
              rtac (mk_sum_casesN n i RS arg_cong RS trans RS iffD2),
              etac (from_to_sbd RS arg_cong), REPEAT_DETERM o etac allE,
              dtac (mk_conjunctN n i), etac mp, etac conjI, etac set_rev_mp,
              etac coalg_set, atac])
          (rev (ks ~~ (from_to_sbds ~~ drop m coalg_sets)))])
      ((Lev_Sucs ~~ rv_Conss) ~~ (from_to_sbdss ~~ coalg_setss))] 1
  end;

fun mk_set_Lev_tac ctxt cts Lev_0s Lev_Sucs rv_Nils rv_Conss from_to_sbdss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((i, (Lev_0, Lev_Suc)), rv_Nil) =>
        EVERY' [rtac impI, dtac (Lev_0 RS equalityD1 RS set_mp),
          etac @{thm singletonE}, hyp_subst_tac ctxt,
          CONJ_WRAP' (fn i' => rtac impI THEN' dtac (sym RS trans) THEN' rtac rv_Nil THEN'
            (if i = i'
            then EVERY' [dtac (mk_InN_inject n i), hyp_subst_tac ctxt,
              CONJ_WRAP' (fn (i'', Lev_0'') =>
                EVERY' [rtac impI, rtac @{thm ssubst_mem[OF append_Nil]},
                  rtac (Lev_Suc RS equalityD2 RS set_mp), rtac (mk_UnIN n i''),
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
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE], hyp_subst_tac ctxt,
                CONJ_WRAP' (fn i' => rtac impI THEN'
                  CONJ_WRAP' (fn i'' =>
                    EVERY' [rtac impI, rtac (Lev_Suc RS equalityD2 RS set_mp),
                      rtac @{thm ssubst_mem[OF append_Cons]}, rtac (mk_UnIN n i),
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

fun mk_set_image_Lev_tac ctxt cts Lev_0s Lev_Sucs rv_Nils rv_Conss from_to_sbdss to_sbd_injss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn ((i, (Lev_0, Lev_Suc)), rv_Nil) =>
        EVERY' [rtac impI, dtac (Lev_0 RS equalityD1 RS set_mp),
          etac @{thm singletonE}, hyp_subst_tac ctxt,
          CONJ_WRAP' (fn i' => rtac impI THEN'
            CONJ_WRAP' (fn i'' => rtac impI  THEN' dtac (sym RS trans) THEN' rtac rv_Nil THEN'
              (if i = i''
              then EVERY' [dtac @{thm ssubst_mem[OF sym[OF append_Nil]]},
                dtac (Lev_Suc RS equalityD1 RS set_mp), dtac (mk_InN_inject n i),
                hyp_subst_tac ctxt,
                CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE))
                  (fn k => REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE] THEN'
                    dtac list_inject_iffD1 THEN' etac conjE THEN'
                    (if k = i'
                    then EVERY' [dtac (mk_InN_inject n k), hyp_subst_tac ctxt, etac imageI]
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
              REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE] THEN' hyp_subst_tac ctxt THEN'
              CONJ_WRAP' (fn i' => rtac impI THEN'
                dtac @{thm ssubst_mem[OF sym[OF append_Cons]]} THEN'
                dtac (Lev_Suc RS equalityD1 RS set_mp) THEN'
                CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE)) (fn k =>
                  REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE] THEN'
                  dtac list_inject_iffD1 THEN' etac conjE THEN'
                  (if k = i
                  then EVERY' [dtac (mk_InN_inject n i),
                    dtac (Thm.permute_prems 0 2 (to_sbd_inj RS iffD1)),
                    atac, atac, hyp_subst_tac ctxt] THEN'
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
  prefCl_Levs rv_lastss set_rv_Levsss set_Levsss set_image_Levsss set_map0ss coalg_setss
  map_comp_ids map_cong0s map_arg_congs {context = ctxt, prems = _} =
  let
    val n = length beh_defs;
    val ks = 1 upto n;

    fun fbetw_tac (i, (carT_def, (isNode_def, (Lev_0, (rv_Nil, (Lev_sbd,
      ((length_Lev, length_Lev'), (prefCl_Lev, (rv_lasts, (set_map0s,
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
          etac @{thm prefixeq_length_le}, etac length_Lev, rtac prefCl_Lev, etac conjI, atac,
        rtac conjI,
          rtac ballI, etac @{thm UN_E}, rtac conjI,
          if n = 1 then K all_tac else rtac (mk_sumEN n),
          EVERY' (map6 (fn i => fn isNode_def => fn set_map0s =>
            fn set_rv_Levs => fn set_Levs => fn set_image_Levs =>
            EVERY' [rtac (mk_disjIN n i), rtac (isNode_def RS ssubst),
              rtac exI, rtac conjI,
              (if n = 1 then rtac @{thm if_P} THEN' etac length_Lev'
              else rtac (@{thm if_P} RS arg_cong RS trans) THEN' etac length_Lev' THEN'
                etac (sum_case_weak_cong RS trans) THEN' rtac (mk_sum_casesN n i)),
              EVERY' (map2 (fn set_map0 => fn set_rv_Lev =>
                EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac (set_map0 RS trans),
                  rtac trans_fun_cong_image_id_id_apply,
                  etac set_rv_Lev, TRY o atac, etac conjI, atac])
              (take m set_map0s) set_rv_Levs),
              CONJ_WRAP' (fn (set_map0, (set_Lev, set_image_Lev)) =>
                EVERY' [rtac (set_map0 RS trans), rtac equalityI, rtac @{thm image_subsetI},
                  rtac CollectI, rtac @{thm SuccI}, rtac @{thm UN_I}, rtac UNIV_I, etac set_Lev,
                  if n = 1 then rtac refl else atac, atac, rtac subsetI,
                  REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
                  rtac set_image_Lev, atac, dtac length_Lev, hyp_subst_tac ctxt, dtac length_Lev',
                  etac @{thm set_mp[OF equalityD1[OF arg_cong[OF length_append_singleton]]]},
                  if n = 1 then rtac refl else atac])
              (drop m set_map0s ~~ (set_Levs ~~ set_image_Levs))])
          ks isNode_defs set_map0ss set_rv_Levss set_Levss set_image_Levss),
          CONJ_WRAP' (fn (i, (rv_last, (isNode_def, (set_map0s,
            (set_rv_Levs, (set_Levs, set_image_Levs)))))) =>
            EVERY' [rtac ballI,
              REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
              rtac (rev_mp OF [rv_last, impI]), etac exE, rtac (isNode_def RS ssubst),
              rtac exI, rtac conjI,
              (if n = 1 then rtac @{thm if_P} THEN' etac length_Lev'
              else rtac (@{thm if_P} RS trans) THEN' etac length_Lev' THEN'
                etac (sum_case_weak_cong RS trans) THEN' rtac (mk_sum_casesN n i)),
              EVERY' (map2 (fn set_map0 => fn set_rv_Lev =>
                EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac (set_map0 RS trans),
                  rtac trans_fun_cong_image_id_id_apply,
                  etac set_rv_Lev, TRY o atac, etac conjI, atac])
              (take m set_map0s) set_rv_Levs),
              CONJ_WRAP' (fn (set_map0, (set_Lev, set_image_Lev)) =>
                EVERY' [rtac (set_map0 RS trans), rtac equalityI, rtac @{thm image_subsetI},
                  rtac CollectI, rtac @{thm SuccI}, rtac @{thm UN_I}, rtac UNIV_I, etac set_Lev,
                  if n = 1 then rtac refl else atac, atac, rtac subsetI,
                  REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
                  REPEAT_DETERM_N 4 o etac thin_rl,
                  rtac set_image_Lev,
                  atac, dtac length_Lev, hyp_subst_tac ctxt, dtac length_Lev',
                  etac @{thm set_mp[OF equalityD1[OF arg_cong[OF length_append_singleton]]]},
                  if n = 1 then rtac refl else atac])
              (drop m set_map0s ~~ (set_Levs ~~ set_image_Levs))])
          (ks ~~ (rv_lasts ~~ (isNode_defs ~~ (set_map0ss ~~
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
          EVERY' (map2 (fn set_map0 => fn coalg_set =>
            EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac (set_map0 RS trans),
              rtac trans_fun_cong_image_id_id_apply, etac coalg_set, atac])
            (take m set_map0s) (take m coalg_sets)),
          CONJ_WRAP' (fn (set_map0, (set_Lev, set_image_Lev)) =>
            EVERY' [rtac (set_map0 RS trans), rtac equalityI, rtac @{thm image_subsetI},
              rtac CollectI, rtac @{thm SuccI}, rtac @{thm UN_I}, rtac UNIV_I, rtac set_Lev,
              rtac (Lev_0 RS equalityD2 RS set_mp), rtac @{thm singletonI}, rtac rv_Nil,
              atac, rtac subsetI,
              REPEAT_DETERM o eresolve_tac [CollectE, @{thm SuccE}, @{thm UN_E}],
              rtac set_image_Lev, rtac (Lev_0 RS equalityD2 RS set_mp),
              rtac @{thm singletonI}, dtac length_Lev',
              etac @{thm set_mp[OF equalityD1[OF arg_cong[OF
                trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]]},
              rtac rv_Nil])
          (drop m set_map0s ~~ (nth set_Levss (i - 1) ~~ nth set_image_Levss (i - 1)))];

    fun mor_tac (i, (strT_def, (((Lev_0, Lev_Suc), (rv_Nil, rv_Cons)),
      ((map_comp_id, (map_cong0, map_arg_cong)), (length_Lev', (from_to_sbds, to_sbd_injs)))))) =
      EVERY' [rtac ballI, rtac sym, rtac trans, rtac strT_def,
        rtac (@{thm if_P} RS
          (if n = 1 then map_arg_cong else sum_case_weak_cong) RS trans),
        rtac (@{thm list.size(3)} RS arg_cong RS trans RS equalityD2 RS set_mp),
        rtac Lev_0, rtac @{thm singletonI},
        CONVERSION (Conv.top_conv
          (K (Conv.try_conv (Conv.rewr_conv (rv_Nil RS eq_reflection)))) ctxt),
        if n = 1 then K all_tac
        else (rtac (sum_case_weak_cong RS trans) THEN'
          rtac (mk_sum_casesN n i) THEN' rtac (mk_sum_casesN n i RS trans)),
        rtac (map_comp_id RS trans), rtac (map_cong0 OF replicate m refl),
        EVERY' (map3 (fn i' => fn to_sbd_inj => fn from_to_sbd =>
          DETERM o EVERY' [rtac trans, rtac o_apply, rtac Pair_eqI, rtac conjI,
            rtac trans, rtac @{thm Shift_def},
            rtac equalityI, rtac subsetI, etac thin_rl, etac thin_rl,
            REPEAT_DETERM o eresolve_tac [CollectE, @{thm UN_E}], dtac length_Lev', dtac asm_rl,
            etac thin_rl, dtac @{thm set_rev_mp[OF _ equalityD1]},
            rtac (@{thm length_Cons} RS arg_cong RS trans), rtac Lev_Suc,
            CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE)) (fn i'' =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
                dtac list_inject_iffD1, etac conjE,
                if i' = i'' then EVERY' [dtac (mk_InN_inject n i'),
                  dtac (Thm.permute_prems 0 2 (to_sbd_inj RS iffD1)),
                  atac, atac, hyp_subst_tac ctxt, etac @{thm UN_I[OF UNIV_I]}]
                else etac (mk_InN_not_InM i' i'' RS notE)])
            (rev ks),
            rtac @{thm UN_least}, rtac subsetI, rtac CollectI, rtac @{thm UN_I[OF UNIV_I]},
            rtac (Lev_Suc RS equalityD2 RS set_mp), rtac (mk_UnIN n i'), rtac CollectI,
            REPEAT_DETERM o rtac exI, rtac conjI, rtac refl, etac conjI, atac,
            rtac trans, rtac @{thm shift_def}, rtac ssubst, rtac @{thm fun_eq_iff}, rtac allI,
            rtac @{thm if_cong}, rtac (@{thm length_Cons} RS arg_cong RS trans), rtac iffI,
            dtac asm_rl, dtac asm_rl, dtac asm_rl,
            dtac (Lev_Suc RS equalityD1 RS set_mp),
            CONJ_WRAP_GEN' (etac (Thm.permute_prems 1 1 UnE)) (fn i'' =>
              EVERY' [REPEAT_DETERM o eresolve_tac [CollectE, exE, conjE],
                dtac list_inject_iffD1, etac conjE,
                if i' = i'' then EVERY' [dtac (mk_InN_inject n i'),
                  dtac (Thm.permute_prems 0 2 (to_sbd_inj RS iffD1)),
                  atac, atac, hyp_subst_tac ctxt, atac]
                else etac (mk_InN_not_InM i' i'' RS notE)])
            (rev ks),
            rtac (Lev_Suc RS equalityD2 RS set_mp), rtac (mk_UnIN n i'), rtac CollectI,
            REPEAT_DETERM o rtac exI, rtac conjI, rtac refl, etac conjI, atac,
            CONVERSION (Conv.top_conv
              (K (Conv.try_conv (Conv.rewr_conv (rv_Cons RS eq_reflection)))) ctxt),
            if n = 1 then K all_tac
            else rtac sum_case_weak_cong THEN' rtac (mk_sum_casesN n i' RS trans),
            SELECT_GOAL (unfold_thms_tac ctxt [from_to_sbd]), rtac refl,
            rtac refl])
        ks to_sbd_injs from_to_sbds)];
  in
    (rtac mor_cong THEN'
    EVERY' (map (fn thm => rtac (thm RS ext)) beh_defs) THEN'
    stac mor_def THEN' rtac conjI THEN'
    CONJ_WRAP' fbetw_tac
      (ks ~~ (carT_defs ~~ (isNode_defs ~~ (Lev_0s ~~ (rv_Nils ~~ (Lev_sbds ~~
        ((length_Levs ~~ length_Lev's) ~~ (prefCl_Levs ~~ (rv_lastss ~~
          (set_map0ss ~~ (coalg_setss ~~
            (set_rv_Levsss ~~ (set_Levsss ~~ set_image_Levsss))))))))))))) THEN'
    CONJ_WRAP' mor_tac
      (ks ~~ (strT_defs ~~ (((Lev_0s ~~ Lev_Sucs) ~~ (rv_Nils ~~ rv_Conss)) ~~
        ((map_comp_ids ~~ (map_cong0s ~~ map_arg_congs)) ~~
          (length_Lev's ~~ (from_to_sbdss ~~ to_sbd_injss))))))) 1
  end;

fun mk_congruent_str_final_tac m lsbisE map_comp_id map_cong0 equiv_LSBISs =
  EVERY' [rtac @{thm congruentI}, dtac lsbisE,
    REPEAT_DETERM o eresolve_tac [CollectE, conjE, bexE], rtac (o_apply RS trans),
    etac (sym RS arg_cong RS trans), rtac (map_comp_id RS trans),
    rtac (map_cong0 RS trans), REPEAT_DETERM_N m o rtac refl,
    EVERY' (map (fn equiv_LSBIS =>
      EVERY' [rtac @{thm equiv_proj}, rtac equiv_LSBIS, etac set_mp, atac])
    equiv_LSBISs), rtac sym, rtac (o_apply RS trans),
    etac (sym RS arg_cong RS trans), rtac map_comp_id] 1;

fun mk_coalg_final_tac m coalg_def congruent_str_finals equiv_LSBISs set_map0ss coalgT_setss =
  EVERY' [stac coalg_def,
    CONJ_WRAP' (fn ((set_map0s, coalgT_sets), (equiv_LSBIS, congruent_str_final)) =>
      EVERY' [rtac @{thm univ_preserves}, rtac equiv_LSBIS, rtac congruent_str_final,
        rtac ballI, rtac @{thm ssubst_mem}, rtac o_apply, rtac CollectI,
        EVERY' (map2 (fn set_map0 => fn coalgT_set =>
          EVERY' [rtac conjI, rtac (set_map0 RS ord_eq_le_trans),
            rtac ord_eq_le_trans_trans_fun_cong_image_id_id_apply,
            etac coalgT_set])
        (take m set_map0s) (take m coalgT_sets)),
        CONJ_WRAP' (fn (equiv_LSBIS, (set_map0, coalgT_set)) =>
          EVERY' [rtac (set_map0 RS ord_eq_le_trans),
            rtac @{thm image_subsetI}, rtac ssubst, rtac @{thm proj_in_iff},
            rtac equiv_LSBIS, etac set_rev_mp, etac coalgT_set])
        (equiv_LSBISs ~~ drop m (set_map0s ~~ coalgT_sets))])
    ((set_map0ss ~~ coalgT_setss) ~~ (equiv_LSBISs ~~ congruent_str_finals))] 1;

fun mk_mor_T_final_tac mor_def congruent_str_finals equiv_LSBISs =
  EVERY' [stac mor_def, rtac conjI,
    CONJ_WRAP' (fn equiv_LSBIS =>
      EVERY' [rtac ballI, rtac ssubst, rtac @{thm proj_in_iff}, rtac equiv_LSBIS, atac])
    equiv_LSBISs,
    CONJ_WRAP' (fn (equiv_LSBIS, congruent_str_final) =>
      EVERY' [rtac ballI, rtac sym, rtac trans, rtac @{thm univ_commute}, rtac equiv_LSBIS,
        rtac congruent_str_final, atac, rtac o_apply])
    (equiv_LSBISs ~~ congruent_str_finals)] 1;

fun mk_mor_Rep_tac m defs Reps Abs_inverses coalg_final_setss map_comp_ids map_cong0Ls
  {context = ctxt, prems = _} =
  unfold_thms_tac ctxt defs THEN
  EVERY' [rtac conjI,
    CONJ_WRAP' (fn thm => rtac ballI THEN' rtac thm) Reps,
    CONJ_WRAP' (fn (Rep, ((map_comp_id, map_cong0L), coalg_final_sets)) =>
      EVERY' [rtac ballI, rtac (map_comp_id RS trans), rtac map_cong0L,
        EVERY' (map2 (fn Abs_inverse => fn coalg_final_set =>
          EVERY' [rtac ballI, rtac (o_apply RS trans), rtac Abs_inverse,
            etac set_rev_mp, rtac coalg_final_set, rtac Rep])
        Abs_inverses (drop m coalg_final_sets))])
    (Reps ~~ ((map_comp_ids ~~ map_cong0Ls) ~~ coalg_final_setss))] 1;

fun mk_mor_Abs_tac defs Abs_inverses {context = ctxt, prems = _} =
  unfold_thms_tac ctxt defs THEN
  EVERY' [rtac conjI,
    CONJ_WRAP' (K (rtac ballI THEN' rtac UNIV_I)) Abs_inverses,
    CONJ_WRAP' (fn thm => rtac ballI THEN' etac (thm RS arg_cong RS sym)) Abs_inverses] 1;

fun mk_mor_unfold_tac m mor_UNIV dtor_defs unfold_defs Abs_inverses morEs map_comp_ids map_cong0s =
  EVERY' [rtac iffD2, rtac mor_UNIV,
    CONJ_WRAP' (fn ((Abs_inverse, morE), ((dtor_def, unfold_def), (map_comp_id, map_cong0))) =>
      EVERY' [rtac ext, rtac (o_apply RS trans RS sym), rtac (dtor_def RS trans),
        rtac (unfold_def RS arg_cong RS trans), rtac (Abs_inverse RS arg_cong RS trans),
        rtac (morE RS arg_cong RS trans), rtac (map_comp_id RS trans),
        rtac (o_apply RS trans RS sym), rtac map_cong0,
        REPEAT_DETERM_N m o rtac refl,
        EVERY' (map (fn thm => rtac (thm RS trans) THEN' rtac (o_apply RS sym)) unfold_defs)])
    ((Abs_inverses ~~ morEs) ~~ ((dtor_defs ~~ unfold_defs) ~~ (map_comp_ids ~~ map_cong0s)))] 1;

fun mk_raw_coind_tac bis_def bis_cong bis_O bis_converse bis_Gr tcoalg coalgT mor_T_final
  sbis_lsbis lsbis_incls incl_lsbiss equiv_LSBISs mor_Rep Rep_injects =
  let
    val n = length Rep_injects;
  in
    EVERY' [rtac rev_mp, ftac (bis_def RS iffD1),
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
          rtac @{thm relImage_proj}, rtac equiv_LSBIS, rtac @{thm relInvImage_Id_on},
          rtac Rep_inject])
      (Rep_injects ~~ (equiv_LSBISs ~~ (incl_lsbiss ~~ lsbis_incls)))] 1
  end;

fun mk_unfold_unique_mor_tac raw_coinds bis mor unfold_defs =
  CONJ_WRAP' (fn (raw_coind, unfold_def) =>
    EVERY' [rtac ext, etac (bis RS raw_coind RS set_mp RS @{thm IdD}), rtac mor,
      rtac @{thm image2_eqI}, rtac refl, rtac (unfold_def RS arg_cong RS trans),
      rtac (o_apply RS sym), rtac UNIV_I]) (raw_coinds ~~ unfold_defs) 1;

fun mk_dtor_o_ctor_tac ctor_def unfold map_comp_id map_cong0L unfold_o_dtors
  {context = ctxt, prems = _} =
  unfold_thms_tac ctxt [ctor_def] THEN EVERY' [rtac ext, rtac trans, rtac o_apply,
    rtac trans, rtac unfold, rtac trans, rtac map_comp_id, rtac trans, rtac map_cong0L,
    EVERY' (map (fn thm =>
      rtac ballI THEN' rtac (trans OF [thm RS fun_cong, id_apply])) unfold_o_dtors),
    rtac sym, rtac id_apply] 1;

fun mk_corec_tac m corec_defs unfold map_cong0 corec_Inls {context = ctxt, prems = _} =
  unfold_thms_tac ctxt corec_defs THEN EVERY' [rtac trans, rtac (o_apply RS arg_cong),
    rtac trans, rtac unfold, fo_rtac (@{thm sum.cases(2)} RS arg_cong RS trans) ctxt, rtac map_cong0,
    REPEAT_DETERM_N m o rtac refl,
    EVERY' (map (fn thm => rtac @{thm sum_case_expand_Inr} THEN' rtac thm) corec_Inls)] 1;

fun mk_corec_unique_mor_tac corec_defs corec_Inls unfold_unique_mor {context = ctxt, prems = _} =
  unfold_thms_tac ctxt
    (corec_defs @ map (fn thm => thm RS @{thm sum_case_expand_Inr'}) corec_Inls) THEN
  etac unfold_unique_mor 1;

fun mk_dtor_coinduct_tac m raw_coind bis_rel rel_congs =
  EVERY' [rtac rev_mp, rtac raw_coind, rtac ssubst, rtac bis_rel, rtac conjI,
    CONJ_WRAP' (K (rtac @{thm ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]]}))
    rel_congs,
    CONJ_WRAP' (fn rel_cong => EVERY' [rtac allI, rtac allI, rtac impI,
      REPEAT_DETERM o etac allE, rtac (rel_cong RS @{thm eq_refl} RS @{thm predicate2D}),
      REPEAT_DETERM_N m o rtac @{thm in_rel_Id_on_UNIV[symmetric]},
      REPEAT_DETERM_N (length rel_congs) o rtac @{thm in_rel_Collect_split_eq[symmetric]},
      etac mp, etac CollectE, etac @{thm splitD}])
    rel_congs,
    rtac impI, REPEAT_DETERM o etac conjE,
    CONJ_WRAP' (K (EVERY' [rtac impI, rtac @{thm IdD}, etac set_mp,
      rtac CollectI, etac @{thm prod_caseI}])) rel_congs] 1;

fun mk_dtor_map_coinduct_tac m ks raw_coind bis_def =
  let
    val n = length ks;
  in
    EVERY' [rtac rev_mp, rtac raw_coind, rtac ssubst, rtac bis_def, rtac conjI,
      CONJ_WRAP' (K (rtac @{thm ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]]})) ks,
      CONJ_WRAP' (fn i => EVERY' [select_prem_tac n (dtac asm_rl) i, REPEAT_DETERM o rtac allI,
        rtac impI, REPEAT_DETERM o dtac @{thm meta_spec}, etac CollectE, etac @{thm meta_impE},
        atac, etac exE, etac conjE, etac conjE, rtac bexI, rtac conjI,
        etac @{thm fst_conv[THEN subst]}, etac @{thm snd_conv[THEN subst]},
        rtac CollectI, REPEAT_DETERM_N m o (rtac conjI THEN' rtac subset_UNIV),
        CONJ_WRAP' (fn i' => EVERY' [rtac subsetI, rtac CollectI, dtac (mk_conjunctN n i'),
          REPEAT_DETERM o etac allE, etac mp, rtac @{thm ssubst_mem[OF pair_collapse]}, atac])
        ks])
      ks,
      rtac impI,
      CONJ_WRAP' (fn i => EVERY' [rtac impI, dtac (mk_conjunctN n i),
        rtac @{thm subst[OF pair_in_Id_conv]}, etac set_mp,
        rtac CollectI, etac (refl RSN (2, @{thm subst_Pair}))]) ks] 1
  end;

fun mk_map_tac m n cT unfold map_comp map_cong0 =
  EVERY' [rtac ext, rtac (o_apply RS trans RS sym), rtac (o_apply RS trans RS sym),
    rtac (unfold RS trans), rtac (Thm.permute_prems 0 1 (map_comp RS box_equals)), rtac map_cong0,
    REPEAT_DETERM_N m o rtac (@{thm id_o} RS fun_cong),
    REPEAT_DETERM_N n o rtac (@{thm o_id} RS fun_cong),
    rtac (o_apply RS (Drule.instantiate' [cT] [] arg_cong) RS sym)] 1;

fun mk_set_le_tac n hset_minimal set_hsets set_hset_hsetss =
  EVERY' [rtac hset_minimal,
    REPEAT_DETERM_N n o rtac @{thm Un_upper1},
    REPEAT_DETERM_N n o
      EVERY' (map3 (fn i => fn set_hset => fn set_hset_hsets =>
        EVERY' [rtac subsetI, rtac @{thm UnI2}, rtac (mk_UnIN n i), etac @{thm UN_I},
          etac UnE, etac set_hset, REPEAT_DETERM_N (n - 1) o etac UnE,
          EVERY' (map (fn thm => EVERY' [etac @{thm UN_E}, etac thm, atac]) set_hset_hsets)])
      (1 upto n) set_hsets set_hset_hsetss)] 1;

fun mk_set_ge_tac n set_incl_hset set_hset_incl_hsets =
  EVERY' [rtac @{thm Un_least}, rtac set_incl_hset,
    REPEAT_DETERM_N (n - 1) o rtac @{thm Un_least},
    EVERY' (map (fn thm => rtac @{thm UN_least} THEN' etac thm) set_hset_incl_hsets)] 1;

fun mk_map_id0_tac maps unfold_unique unfold_dtor =
  EVERY' [rtac (unfold_unique RS trans), EVERY' (map (rtac o mk_sym) maps),
    rtac unfold_dtor] 1;

fun mk_map_comp0_tac maps map_comp0s map_unique =
  EVERY' [rtac map_unique,
    EVERY' (map2 (fn map_thm => fn map_comp0 =>
      EVERY' (map rtac
        [@{thm o_assoc} RS trans,
        @{thm arg_cong2[of _ _ _ _ "op o"]} OF [map_thm, refl] RS trans,
        @{thm o_assoc} RS sym RS trans, map_thm RS arg_cong RS trans, @{thm o_assoc} RS trans,
        @{thm arg_cong2[of _ _ _ _ "op o"]} OF [map_comp0 RS sym, refl]]))
    maps map_comp0s)] 1;

fun mk_mcong_tac ctxt m coinduct_tac map_comps dtor_maps map_cong0s set_map0ss set_hsetss
  set_hset_hsetsss =
  let
    val n = length map_comps;
    val ks = 1 upto n;
  in
    EVERY' ([rtac rev_mp,
      coinduct_tac] @
      maps (fn (((((map_comp_trans, dtor_maps_trans), map_cong0), set_map0s), set_hsets),
        set_hset_hsetss) =>
        [REPEAT_DETERM o eresolve_tac [exE, conjE], hyp_subst_tac ctxt, rtac exI, rtac conjI,
         rtac conjI, rtac map_comp_trans, rtac sym, rtac dtor_maps_trans, rtac map_cong0,
         REPEAT_DETERM_N m o (rtac o_apply_trans_sym THEN' rtac id_apply),
         REPEAT_DETERM_N n o rtac fst_convol_fun_cong_sym,
         rtac map_comp_trans, rtac sym, rtac dtor_maps_trans, rtac map_cong0,
         EVERY' (maps (fn set_hset =>
           [rtac o_apply_trans_sym, rtac (id_apply RS trans), etac CollectE,
           REPEAT_DETERM o etac conjE, etac bspec, etac set_hset]) set_hsets),
         REPEAT_DETERM_N n o rtac snd_convol_fun_cong_sym,
         CONJ_WRAP' (fn (set_map0, set_hset_hsets) =>
           EVERY' [REPEAT_DETERM o rtac allI, rtac impI, rtac @{thm image_convolD},
             etac set_rev_mp, rtac ord_eq_le_trans, rtac set_map0,
             rtac @{thm image_mono}, rtac subsetI, rtac CollectI, etac CollectE,
             REPEAT_DETERM o etac conjE,
             CONJ_WRAP' (fn set_hset_hset =>
               EVERY' [rtac ballI, etac bspec, etac set_hset_hset, atac]) set_hset_hsets])
           (drop m set_map0s ~~ set_hset_hsetss)])
        (map (fn th => th RS trans) map_comps ~~ map (fn th => th RS trans) dtor_maps ~~
          map_cong0s ~~ set_map0ss ~~ set_hsetss ~~ set_hset_hsetsss) @
      [rtac impI,
       CONJ_WRAP' (fn k =>
         EVERY' [rtac impI, dtac (mk_conjunctN n k), etac mp, rtac exI, rtac conjI, etac CollectI,
           rtac conjI, rtac refl, rtac refl]) ks]) 1
  end

fun mk_dtor_map_unique_tac unfold_unique sym_map_comps ctxt =
  rtac unfold_unique 1 THEN
  unfold_thms_tac ctxt (sym_map_comps @ @{thms o_assoc id_o o_id}) THEN
  ALLGOALS (etac sym);

fun mk_col_natural_tac cts rec_0s rec_Sucs dtor_maps set_map0ss
  {context = ctxt, prems = _} =
  let
    val n = length dtor_maps;
  in
    EVERY' [rtac (Drule.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac allI, SELECT_GOAL (unfold_thms_tac ctxt rec_0s),
      CONJ_WRAP' (K (rtac @{thm image_empty})) rec_0s,
      REPEAT_DETERM o rtac allI,
      CONJ_WRAP' (fn (rec_Suc, (dtor_map, set_nats)) => EVERY'
        [SELECT_GOAL (unfold_thms_tac ctxt
          (rec_Suc :: dtor_map :: set_nats @ @{thms image_Un image_UN UN_simps(10)})),
        rtac Un_cong, rtac refl,
        CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 Un_cong))
          (fn i => EVERY' [rtac @{thm UN_cong[OF refl]},
            REPEAT_DETERM o etac allE, etac (mk_conjunctN n i)]) (n downto 1)])
      (rec_Sucs ~~ (dtor_maps ~~ set_map0ss))] 1
  end;

fun mk_set_map0_tac hset_def col_natural =
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
    @{thm UNION_Cinfinite_bound}, ordIso_ordLeq_trans, @{thm card_of_nat},
    @{thm natLeq_ordLeq_cinfinite}, sbd_Cinfinite, ballI, col_bd, sbd_Cinfinite]) 1;

fun mk_le_rel_OO_tac coinduct rel_Jrels rel_OOs =
  EVERY' (rtac coinduct :: map2 (fn rel_Jrel => fn rel_OO =>
    let val Jrel_imp_rel = rel_Jrel RS iffD1;
    in
      EVERY' [rtac (rel_OO RS sym RS @{thm eq_refl} RS @{thm predicate2D}), etac @{thm relcomppE},
      rtac @{thm relcomppI}, etac Jrel_imp_rel, etac Jrel_imp_rel]
    end)
  rel_Jrels rel_OOs) 1;

fun mk_wit_tac n dtor_ctors dtor_set wit coind_wits ctxt =
  ALLGOALS (TRY o (eresolve_tac coind_wits THEN' rtac refl)) THEN
  REPEAT_DETERM (atac 1 ORELSE
    EVERY' [dtac set_rev_mp, rtac equalityD1, resolve_tac dtor_set,
    K (unfold_thms_tac ctxt dtor_ctors),
    REPEAT_DETERM_N n o etac UnE,
    REPEAT_DETERM o
      (TRY o REPEAT_DETERM o etac UnE THEN' TRY o etac @{thm UN_E} THEN'
        (eresolve_tac wit ORELSE'
        (dresolve_tac wit THEN'
          (etac FalseE ORELSE'
          EVERY' [hyp_subst_tac ctxt, dtac set_rev_mp, rtac equalityD1, resolve_tac dtor_set,
            K (unfold_thms_tac ctxt dtor_ctors), REPEAT_DETERM_N n o etac UnE]))))] 1);

fun mk_coind_wit_tac induct unfolds set_nats wits {context = ctxt, prems = _} =
  rtac induct 1 THEN ALLGOALS (TRY o rtac impI THEN' TRY o hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt (unfolds @ set_nats @ @{thms image_id id_apply}) THEN
  ALLGOALS (REPEAT_DETERM o etac imageE THEN' TRY o hyp_subst_tac ctxt) THEN
  ALLGOALS (TRY o
    FIRST' [rtac TrueI, rtac refl, etac (refl RSN (2, mp)), dresolve_tac wits THEN' etac FalseE])

fun mk_dtor_rel_tac ctxt in_Jrels i in_rel map_comp0 map_cong0 dtor_map dtor_sets dtor_inject
    dtor_ctor set_map0s dtor_set_incls dtor_set_set_inclss =
  let
    val m = length dtor_set_incls;
    val n = length dtor_set_set_inclss;
    val (passive_set_map0s, active_set_map0s) = chop m set_map0s;
    val in_Jrel = nth in_Jrels (i - 1);
    val if_tac =
      EVERY' [dtac (in_Jrel RS iffD1), REPEAT_DETERM o eresolve_tac [exE, conjE, CollectE],
        rtac (in_rel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
        EVERY' (map2 (fn set_map0 => fn set_incl =>
          EVERY' [rtac conjI, rtac ord_eq_le_trans, rtac set_map0,
            rtac ord_eq_le_trans, rtac trans_fun_cong_image_id_id_apply,
            etac (set_incl RS @{thm subset_trans})])
        passive_set_map0s dtor_set_incls),
        CONJ_WRAP' (fn (in_Jrel, (set_map0, dtor_set_set_incls)) =>
          EVERY' [rtac ord_eq_le_trans, rtac set_map0, rtac @{thm image_subsetI}, rtac CollectI,
            rtac @{thm prod_caseI}, rtac (in_Jrel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
            CONJ_WRAP' (fn thm => etac (thm RS @{thm subset_trans}) THEN' atac) dtor_set_set_incls,
            rtac conjI, rtac refl, rtac refl])
        (in_Jrels ~~ (active_set_map0s ~~ dtor_set_set_inclss)),
        CONJ_WRAP' (fn conv =>
          EVERY' [rtac trans, rtac map_comp0, rtac trans, rtac map_cong0,
          REPEAT_DETERM_N m o rtac @{thm fun_cong[OF o_id]},
          REPEAT_DETERM_N n o EVERY' (map rtac [trans, o_apply, conv]),
          rtac trans, rtac sym, rtac dtor_map, rtac (dtor_inject RS iffD2), atac])
        @{thms fst_conv snd_conv}];
    val only_if_tac =
      EVERY' [dtac (in_rel RS iffD1), REPEAT_DETERM o eresolve_tac [exE, conjE, CollectE],
        rtac (in_Jrel RS iffD2), rtac exI, rtac conjI, rtac CollectI,
        CONJ_WRAP' (fn (dtor_set, passive_set_map0) =>
          EVERY' [rtac ord_eq_le_trans, rtac dtor_set, rtac @{thm Un_least},
            rtac ord_eq_le_trans, rtac box_equals, rtac passive_set_map0,
            rtac (dtor_ctor RS sym RS arg_cong), rtac trans_fun_cong_image_id_id_apply, atac,
            CONJ_WRAP_GEN' (rtac (Thm.permute_prems 0 1 @{thm Un_least}))
              (fn (active_set_map0, in_Jrel) => EVERY' [rtac ord_eq_le_trans,
                rtac @{thm UN_cong[OF _ refl]}, rtac @{thm box_equals[OF _ _ refl]},
                rtac active_set_map0, rtac (dtor_ctor RS sym RS arg_cong), rtac @{thm UN_least},
                dtac set_rev_mp, etac @{thm image_mono}, etac imageE,
                dtac @{thm ssubst_mem[OF pair_collapse]},
                REPEAT_DETERM o eresolve_tac (CollectE :: conjE ::
                  @{thms prod_caseE iffD1[OF Pair_eq, elim_format]}),
                hyp_subst_tac ctxt,
                dtac (in_Jrel RS iffD1),
                dtac @{thm someI_ex}, REPEAT_DETERM o etac conjE,
                TRY o
                  EVERY' [dtac (Thm.permute_prems 0 1 @{thm ssubst_mem}), atac, hyp_subst_tac ctxt],
                REPEAT_DETERM o eresolve_tac [CollectE, conjE], atac])
            (rev (active_set_map0s ~~ in_Jrels))])
        (dtor_sets ~~ passive_set_map0s),
        rtac conjI,
        REPEAT_DETERM_N 2 o EVERY'[rtac (dtor_inject RS iffD1), rtac trans, rtac dtor_map,
          rtac box_equals, rtac map_comp0, rtac (dtor_ctor RS sym RS arg_cong), rtac trans,
          rtac map_cong0, REPEAT_DETERM_N m o rtac @{thm fun_cong[OF o_id]},
          EVERY' (map (fn in_Jrel => EVERY' [rtac trans, rtac o_apply, dtac set_rev_mp, atac,
            dtac @{thm ssubst_mem[OF pair_collapse]},
            REPEAT_DETERM o
              eresolve_tac (CollectE :: conjE :: @{thms prod_caseE iffD1[OF Pair_eq, elim_format]}),
            hyp_subst_tac ctxt, dtac (in_Jrel RS iffD1),
            dtac @{thm someI_ex}, REPEAT_DETERM o etac conjE, atac]) in_Jrels),
          atac]]
  in
    EVERY' [rtac iffI, if_tac, only_if_tac] 1
  end;

fun mk_rel_coinduct_coind_tac m coinduct ks map_comp0s map_congs map_arg_congs set_map0ss 
  dtor_unfolds dtor_maps {context = ctxt, prems = _} =
  let val n = length ks;
  in
    EVERY' [DETERM o rtac coinduct,
      EVERY' (map7 (fn i => fn map_comp0 => fn map_cong => fn map_arg_cong => fn set_map0s =>
          fn dtor_unfold => fn dtor_map =>
        EVERY' [REPEAT_DETERM o eresolve_tac [exE, conjE],
          select_prem_tac (length ks) (dtac @{thm spec2}) i, dtac mp, atac,
          REPEAT_DETERM o eresolve_tac [CollectE, conjE], hyp_subst_tac ctxt,
          rtac exI, rtac conjI, rtac conjI,
          rtac (map_comp0 RS trans), rtac (dtor_map RS trans RS sym),
          rtac (dtor_unfold RS map_arg_cong RS trans), rtac (trans OF [map_comp0, map_cong]),
          REPEAT_DETERM_N m o rtac @{thm trans[OF fun_cong[OF o_id] sym[OF fun_cong[OF id_o]]]},
          REPEAT_DETERM_N n o (rtac @{thm sym[OF trans[OF o_apply]]} THEN' rtac @{thm fst_conv}),
          rtac (map_comp0 RS trans), rtac (map_cong RS trans),
          REPEAT_DETERM_N m o rtac @{thm fun_cong[OF id_o]},
          REPEAT_DETERM_N n o (rtac @{thm trans[OF o_apply]} THEN' rtac @{thm snd_conv}),
          etac (@{thm prod.cases} RS map_arg_cong RS trans),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms prod.cases}), 
          CONJ_WRAP' (fn set_map0 =>
            EVERY' [REPEAT_DETERM o resolve_tac [allI, impI],
              dtac (set_map0 RS equalityD1 RS set_mp),
              REPEAT_DETERM o
                eresolve_tac (imageE :: conjE :: @{thms iffD1[OF Pair_eq, elim_format]}),
              hyp_subst_tac ctxt, rtac exI, rtac conjI, etac Collect_splitD_set_mp, atac,
              rtac (o_apply RS trans), rtac (@{thm surjective_pairing} RS arg_cong)])
          (drop m set_map0s)])
      ks map_comp0s map_congs map_arg_congs set_map0ss dtor_unfolds dtor_maps)] 1
  end;

val split_id_unfolds = @{thms prod.cases image_id id_apply};

fun mk_rel_coinduct_ind_tac m ks unfolds set_map0ss j set_induct {context = ctxt, prems = _} =
  let val n = length ks;
  in
    rtac set_induct 1 THEN
    EVERY' (map3 (fn unfold => fn set_map0s => fn i =>
      EVERY' [REPEAT_DETERM o resolve_tac [allI, impI], etac conjE,
        select_prem_tac n (dtac @{thm spec2}) i, dtac mp, atac,
        REPEAT_DETERM o eresolve_tac [CollectE, conjE, Collect_splitD_set_mp, set_rev_mp],
        hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt ([unfold, nth set_map0s (j - 1)] @ split_id_unfolds)),
        rtac subset_refl])
    unfolds set_map0ss ks) 1 THEN
    EVERY' (map3 (fn unfold => fn set_map0s => fn i =>
      EVERY' (map (fn set_map0 =>
        EVERY' [REPEAT_DETERM o resolve_tac [allI, impI], etac conjE,
        select_prem_tac n (dtac @{thm spec2}) i, dtac mp, atac,
        REPEAT_DETERM o eresolve_tac [CollectE, conjE], hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt ([unfold, set_map0] @ split_id_unfolds)),
        etac imageE, hyp_subst_tac ctxt, REPEAT_DETERM o eresolve_tac [allE, mp],
        rtac conjI, etac Collect_splitD_set_mp, atac, rtac (@{thm surjective_pairing} RS arg_cong)])
      (drop m set_map0s)))
    unfolds set_map0ss ks) 1
  end;

fun mk_rel_coinduct_tac in_rels in_Jrels helper_indss helper_coind1s helper_coind2s
  {context = ctxt, prems = CIHs} =
  let val n = length in_rels;
  in
    Method.insert_tac CIHs 1 THEN
    unfold_thms_tac ctxt (@{thm choice_iff} :: @{thm ex_simps(6)[symmetric]} :: in_rels) THEN
    REPEAT_DETERM (etac exE 1) THEN
    CONJ_WRAP' (fn (in_Jrel, (helper_inds, (helper_coind1, helper_coind2))) =>
      EVERY' [rtac @{thm predicate2I}, rtac (in_Jrel RS iffD2), rtac exI, rtac conjI,
        if null helper_inds then rtac UNIV_I
        else rtac CollectI THEN'
          CONJ_WRAP' (fn helper_ind =>
            EVERY' [rtac (helper_ind RS rev_mp), REPEAT_DETERM_N n o atac,
              REPEAT_DETERM_N n o etac thin_rl, rtac impI,
              REPEAT_DETERM o resolve_tac [subsetI, CollectI, @{thm iffD2[OF split_beta]}],
              dtac bspec, atac, REPEAT_DETERM o eresolve_tac [allE, mp, conjE],
              etac (refl RSN (2, conjI))])
          helper_inds,
        rtac conjI,
        rtac (helper_coind1 RS rev_mp), REPEAT_DETERM_N n o atac, REPEAT_DETERM_N n o etac thin_rl,
        rtac impI, etac mp, rtac exI, etac (refl RSN (2, conjI)),
        rtac (helper_coind2 RS rev_mp), REPEAT_DETERM_N n o atac, REPEAT_DETERM_N n o etac thin_rl,
        rtac impI, etac mp, rtac exI, etac (refl RSN (2, conjI))])
    (in_Jrels ~~ (helper_indss ~~ (helper_coind1s ~~ helper_coind2s))) 1
  end;

fun mk_unfold_transfer_tac m rel_coinduct map_transfers unfolds {context = ctxt, prems = _} =
  let
    val n = length map_transfers;
  in
    unfold_thms_tac ctxt
      @{thms fun_rel_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]} THEN
    unfold_thms_tac ctxt @{thms fun_rel_iff_geq_image2p} THEN
    HEADGOAL (EVERY'
      [REPEAT_DETERM o resolve_tac [allI, impI], rtac rel_coinduct,
      EVERY' (map (fn map_transfer => EVERY'
        [REPEAT_DETERM o resolve_tac [allI, impI], etac @{thm image2pE}, hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt unfolds),
        rtac (funpow (m + n + 1) (fn thm => thm RS @{thm fun_relD}) map_transfer),
        REPEAT_DETERM_N m o rtac @{thm id_transfer},
        REPEAT_DETERM_N n o rtac @{thm fun_rel_image2p},
        etac @{thm predicate2D}, etac @{thm image2pI}])
      map_transfers)])
  end;

end;
