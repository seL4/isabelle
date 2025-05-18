(*  Title:      HOL/Tools/BNF/bnf_gfp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for the codatatype construction.
*)

signature BNF_GFP_TACTICS =
sig
  val mk_bis_Gr_tac: Proof.context -> thm -> thm list -> thm list -> thm list -> thm list -> tactic
  val mk_bis_O_tac: Proof.context -> int -> thm -> thm list -> thm list -> tactic
  val mk_bis_Union_tac: Proof.context -> thm -> thm list -> tactic
  val mk_bis_converse_tac: Proof.context -> int -> thm -> thm list -> thm list -> tactic
  val mk_bis_rel_tac: Proof.context -> int -> thm -> thm list -> thm list -> thm list ->
    thm list list -> tactic
  val mk_coalgT_tac: Proof.context -> int -> thm list -> thm list -> thm list list -> tactic
  val mk_coalg_final_tac: Proof.context -> int -> thm -> thm list -> thm list -> thm list list ->
    thm list list -> tactic
  val mk_coalg_set_tac: Proof.context -> thm -> tactic
  val mk_coind_wit_tac: Proof.context -> thm -> thm list -> thm list -> thm list -> tactic
  val mk_col_bd_tac: Proof.context -> int -> int -> cterm option list -> thm list -> thm list ->
    thm -> thm -> thm list list -> tactic
  val mk_col_natural_tac: Proof.context -> cterm option list -> thm list -> thm list -> thm list ->
    thm list list -> tactic
  val mk_congruent_str_final_tac: Proof.context -> int -> thm -> thm -> thm -> thm list -> tactic
  val mk_corec_tac: Proof.context -> int -> thm list -> thm -> thm -> thm list -> tactic
  val mk_corec_unique_mor_tac: Proof.context -> thm list -> thm list -> thm -> tactic
  val mk_dtor_coinduct_tac: Proof.context -> int -> thm -> thm -> thm list -> tactic
  val mk_dtor_corec_transfer_tac: Proof.context -> int -> int -> thm list -> thm list -> thm list ->
    thm list -> tactic
  val mk_dtor_rel_tac: Proof.context -> thm list -> int -> thm -> thm -> thm -> thm -> thm list ->
    thm -> thm -> thm list -> thm list -> thm list list -> tactic
  val mk_dtor_o_ctor_tac: Proof.context -> thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_equiv_lsbis_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_Jset_minimal_tac: Proof.context -> int -> thm -> tactic
  val mk_col_minimal_tac: Proof.context -> int -> cterm option list -> thm list -> thm list ->
    tactic
  val mk_incl_lsbis_tac: Proof.context -> int -> int -> thm -> tactic
  val mk_length_Lev'_tac: Proof.context -> thm -> tactic
  val mk_length_Lev_tac: Proof.context -> cterm option list -> thm list -> thm list -> tactic
  val mk_map_comp0_tac: Proof.context -> thm list -> thm list -> thm -> tactic
  val mk_mcong_tac: Proof.context -> int -> (int -> tactic) -> thm list -> thm list -> thm list ->
    thm list list -> thm list list -> thm list list list -> thm list -> tactic
  val mk_map_id0_tac: Proof.context -> thm list -> thm -> thm -> tactic
  val mk_map_tac: Proof.context -> int -> int -> thm -> thm -> thm -> thm -> tactic
  val mk_dtor_map_unique_tac: Proof.context -> thm -> thm list -> tactic
  val mk_mor_Abs_tac: Proof.context -> thm list -> thm list -> tactic
  val mk_mor_Rep_tac: Proof.context -> thm list -> thm list -> thm list -> thm list list ->
    thm list -> thm list -> tactic
  val mk_mor_T_final_tac: Proof.context -> thm -> thm list -> thm list -> tactic
  val mk_mor_UNIV_tac: Proof.context -> thm list -> thm -> tactic
  val mk_mor_beh_tac: Proof.context -> int -> thm -> thm -> thm list -> thm list -> thm list ->
    thm list -> thm list list -> thm list list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list list -> thm list list list -> thm list list list ->
    thm list list -> thm list -> thm list -> tactic
  val mk_mor_comp_tac: Proof.context -> thm -> thm list -> thm list -> thm list -> tactic
  val mk_mor_elim_tac: Proof.context -> thm -> tactic
  val mk_mor_col_tac: Proof.context -> int -> int -> cterm option list -> int -> thm list ->
    thm list -> thm list -> thm list list -> thm list list -> tactic
  val mk_mor_incl_tac: Proof.context -> thm -> thm list -> tactic
  val mk_mor_str_tac: Proof.context -> 'a list -> thm -> tactic
  val mk_mor_unfold_tac: Proof.context -> int -> thm -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> tactic
  val mk_raw_coind_tac: Proof.context -> thm -> thm -> thm -> thm -> thm -> thm -> thm -> thm ->
    thm -> thm list -> thm list -> thm list -> thm -> thm list -> tactic
  val mk_rel_coinduct_tac: Proof.context -> thm list -> thm list -> thm list -> thm list list ->
    thm list -> thm list -> tactic
  val mk_rel_coinduct_coind_tac: Proof.context -> bool -> int -> thm -> int list -> thm list ->
    thm list -> thm list -> thm list list -> thm list -> thm list -> thm list -> tactic
  val mk_rel_coinduct_ind_tac: Proof.context -> int -> int list -> thm list -> thm list list ->
    int -> thm -> tactic
  val mk_rv_last_tac: Proof.context -> ctyp option list -> cterm option list -> thm list ->
    thm list -> tactic
  val mk_sbis_lsbis_tac: Proof.context -> thm list -> thm -> thm -> tactic
  val mk_set_Lev_tac: Proof.context -> cterm option list -> thm list -> thm list -> thm list ->
    thm list -> thm list list -> tactic
  val mk_set_bd_tac: Proof.context -> thm -> thm -> thm -> thm -> tactic
  val mk_set_Jset_incl_Jset_tac: Proof.context -> int -> thm -> int -> tactic
  val mk_set_image_Lev_tac: Proof.context -> cterm option list -> thm list -> thm list ->
    thm list -> thm list -> thm list list -> thm list list -> tactic
  val mk_set_incl_Jset_tac: Proof.context -> thm -> tactic
  val mk_set_ge_tac: Proof.context -> int  -> thm -> thm list -> tactic
  val mk_set_le_tac: Proof.context -> int -> thm -> thm list -> thm list list -> tactic
  val mk_set_map0_tac: Proof.context -> thm -> tactic
  val mk_unfold_unique_mor_tac: Proof.context -> thm list -> thm -> thm -> thm list -> tactic
  val mk_unfold_transfer_tac: Proof.context -> int -> thm -> thm list -> thm list -> tactic
  val mk_wit_tac: Proof.context -> int -> thm list -> thm list -> thm list -> thm list -> tactic
  val mk_le_rel_OO_tac: Proof.context -> thm -> thm list -> thm list -> tactic
end;

structure BNF_GFP_Tactics : BNF_GFP_TACTICS =
struct

open BNF_Tactics
open BNF_Util
open BNF_FP_Util
open BNF_GFP_Util

val fst_convol_fun_cong_sym = @{thm fst_convol[simplified convol_def]} RS fun_cong RS sym;
val list_inject_iffD1 = @{thm list.inject[THEN iffD1]};
val nat_induct = @{thm nat_induct};
val o_apply_trans_sym = o_apply RS trans RS sym;
val ord_eq_le_trans = @{thm ord_eq_le_trans};
val ordIso_ordLeq_trans = @{thm ordIso_ordLeq_trans};
val snd_convol_fun_cong_sym = @{thm snd_convol[simplified convol_def]} RS fun_cong RS sym;
val sum_case_cong_weak = @{thm sum.case_cong_weak};
val trans_fun_cong_image_id_id_apply = @{thm trans[OF fun_cong[OF image_id] id_apply]};
val Collect_splitD_set_mp = @{thm Collect_case_prodD[OF set_mp]};
val rev_bspec = Drule.rotate_prems 1 @{thm bspec};
val Un_cong = @{thm arg_cong2[of _ _ _ _ "(\<union>)"]};
val converse_shift = @{thm converse_subset_swap} RS iffD1;

fun mk_coalg_set_tac ctxt coalg_def =
  dtac ctxt (coalg_def RS iffD1) 1 THEN
  REPEAT_DETERM (etac ctxt conjE 1) THEN
  EVERY' [dtac ctxt rev_bspec, assume_tac ctxt] 1 THEN
  REPEAT_DETERM (eresolve_tac ctxt @{thms CollectE conjE} 1) THEN assume_tac ctxt 1;

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
    (EVERY' [rtac ctxt @{thm ballI}, rtac ctxt (thm RS trans), rtac ctxt sym, rtac ctxt (id_apply RS arg_cong)])) map_ids) 1;

fun mk_mor_comp_tac ctxt mor_def mor_images morEs map_comp_ids =
  let
    fun fbetw_tac image = EVERY' [rtac ctxt @{thm ballI}, rtac ctxt (o_apply RS @{thm ssubst_mem}), etac ctxt image,
      etac ctxt image, assume_tac ctxt];
    fun mor_tac ((mor_image, morE), map_comp_id) =
      EVERY' [rtac ctxt @{thm ballI}, stac ctxt o_apply, rtac ctxt trans, rtac ctxt (map_comp_id RS sym), rtac ctxt trans,
        etac ctxt (morE RS arg_cong), assume_tac ctxt, etac ctxt morE,
        etac ctxt mor_image, assume_tac ctxt];
  in
    (rtac ctxt (mor_def RS iffD2) THEN' rtac ctxt conjI THEN'
    CONJ_WRAP' fbetw_tac mor_images THEN'
    CONJ_WRAP' mor_tac ((mor_images ~~ morEs) ~~ map_comp_ids)) 1
  end;

fun mk_mor_UNIV_tac ctxt morEs mor_def =
  let
    val n = length morEs;
    fun mor_tac morE = EVERY' [rtac ctxt @{thm ext}, rtac ctxt trans, rtac ctxt o_apply, rtac ctxt trans, etac ctxt morE,
      rtac ctxt @{thm UNIV_I}, rtac ctxt sym, rtac ctxt o_apply];
  in
    EVERY' [rtac ctxt iffI, CONJ_WRAP' mor_tac morEs,
    rtac ctxt (mor_def RS iffD2), rtac ctxt conjI, CONJ_WRAP' (K (rtac ctxt @{thm ballI} THEN' rtac ctxt @{thm UNIV_I})) morEs,
    CONJ_WRAP' (fn i =>
      EVERY' [dtac ctxt (mk_conjunctN n i), rtac ctxt @{thm ballI}, etac ctxt @{thm comp_eq_dest}]) (1 upto n)] 1
  end;

fun mk_mor_str_tac ctxt ks mor_UNIV =
  (rtac ctxt (mor_UNIV RS iffD2) THEN' CONJ_WRAP' (K (rtac ctxt refl)) ks) 1;

fun mk_set_incl_Jset_tac ctxt rec_Suc =
  EVERY' (map (rtac ctxt) (@{thms SUP_upper2 UNIV_I ord_le_eq_trans Un_upper1 sym} @
    [rec_Suc])) 1;

fun mk_set_Jset_incl_Jset_tac ctxt n rec_Suc i =
  EVERY' (map (rtac ctxt) (@{thms UN_least subsetI UN_I UNIV_I set_mp equalityD2} @
    [rec_Suc, @{thm UnI2}, mk_UnIN n i]) @ [etac ctxt @{thm UN_I}, assume_tac ctxt]) 1;

fun mk_col_minimal_tac ctxt m cts rec_0s rec_Sucs =
  EVERY' [rtac ctxt (Thm.instantiate' [] cts nat_induct),
    REPEAT_DETERM o rtac ctxt allI,
    CONJ_WRAP' (fn thm => EVERY'
      [rtac ctxt ord_eq_le_trans, rtac ctxt thm, rtac ctxt @{thm empty_subsetI}]) rec_0s,
    REPEAT_DETERM o rtac ctxt allI,
    CONJ_WRAP' (fn rec_Suc => EVERY'
      [rtac ctxt ord_eq_le_trans, rtac ctxt rec_Suc,
        if m = 0 then K all_tac
        else (rtac ctxt @{thm Un_least} THEN' Goal.assume_rule_tac ctxt),
        CONJ_WRAP_GEN' (rtac ctxt (Thm.permute_prems 0 1 @{thm Un_least}))
          (K (EVERY' [rtac ctxt @{thm UN_least}, REPEAT_DETERM o eresolve_tac ctxt [allE, conjE],
            rtac ctxt @{thm subset_trans}, assume_tac ctxt, Goal.assume_rule_tac ctxt])) rec_0s])
      rec_Sucs] 1;

fun mk_Jset_minimal_tac ctxt n col_minimal =
  (CONJ_WRAP' (K (EVERY' [rtac ctxt @{thm UN_least}, rtac ctxt rev_mp, rtac ctxt col_minimal,
    EVERY' (replicate ((n + 1) * n) (Goal.assume_rule_tac ctxt)), rtac ctxt impI,
    REPEAT_DETERM o eresolve_tac ctxt [allE, conjE], assume_tac ctxt])) (1 upto n)) 1

fun mk_mor_col_tac ctxt m n cts j rec_0s rec_Sucs morEs set_map0ss coalg_setss =
  EVERY' [rtac ctxt (Thm.instantiate' [] cts nat_induct),
    REPEAT_DETERM o rtac ctxt allI,
    CONJ_WRAP' (fn thm => EVERY' (map (rtac ctxt) [impI, thm RS trans, thm RS sym])) rec_0s,
    REPEAT_DETERM o rtac ctxt allI,
    CONJ_WRAP'
      (fn (rec_Suc, (morE, ((passive_set_map0s, active_set_map0s), coalg_sets))) =>
        EVERY' [rtac ctxt impI, rtac ctxt (rec_Suc RS trans), rtac ctxt (rec_Suc RS trans RS sym),
          if m = 0 then K all_tac
          else EVERY' [rtac ctxt Un_cong, rtac ctxt @{thm box_equals},
            rtac ctxt (nth passive_set_map0s (j - 1) RS sym),
            rtac ctxt trans_fun_cong_image_id_id_apply, etac ctxt (morE RS arg_cong),
            assume_tac ctxt],
          CONJ_WRAP_GEN' (rtac ctxt (Thm.permute_prems 0 1 Un_cong))
            (fn (i, (set_map0, coalg_set)) =>
              EVERY' [rtac ctxt sym, rtac ctxt trans, rtac ctxt (refl RSN (2, @{thm SUP_cong})),
                etac ctxt (morE RS sym RS arg_cong RS trans), assume_tac ctxt, rtac ctxt set_map0,
                rtac ctxt (@{thm UN_simps(10)} RS trans), rtac ctxt (refl RS @{thm SUP_cong}),
                forward_tac ctxt [coalg_set], assume_tac ctxt, dtac ctxt set_mp, assume_tac ctxt,
                rtac ctxt mp, rtac ctxt (mk_conjunctN n i),
                REPEAT_DETERM o etac ctxt allE, assume_tac ctxt, assume_tac ctxt])
            (rev ((1 upto n) ~~ (active_set_map0s ~~ coalg_sets)))])
      (rec_Sucs ~~ (morEs ~~ (map (chop m) set_map0ss ~~ map (drop m) coalg_setss)))] 1;

fun mk_bis_rel_tac ctxt m bis_def in_rels map_comp0s map_cong0s set_map0ss =
  let
    val n = length in_rels;
    val thms = ((1 upto n) ~~ map_comp0s ~~ map_cong0s ~~ set_map0ss ~~ in_rels);

    fun mk_if_tac ((((i, map_comp0), map_cong0), set_map0s), in_rel) =
      EVERY' [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI, dtac ctxt (mk_conjunctN n i),
        etac ctxt allE, etac ctxt allE, etac ctxt impE, assume_tac ctxt, etac ctxt @{thm bexE},
        REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE},
        rtac ctxt (in_rel RS iffD2), rtac ctxt exI, rtac ctxt (Drule.rotate_prems 1 conjI),
        CONJ_WRAP' (fn thm => EVERY' [rtac ctxt trans, rtac ctxt trans, rtac ctxt map_comp0, rtac ctxt map_cong0,
          REPEAT_DETERM_N m o rtac ctxt thm, REPEAT_DETERM_N n o rtac ctxt (@{thm comp_id} RS fun_cong),
          assume_tac ctxt])
        @{thms fst_diag_id snd_diag_id},
        rtac ctxt @{thm CollectI},
        CONJ_WRAP' (fn (i, thm) =>
          if i <= m
          then EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt thm, rtac ctxt @{thm subset_trans},
            etac ctxt @{thm image_mono}, rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm CollectI},
            rtac ctxt @{thm case_prodI}, rtac ctxt refl]
          else EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt trans, rtac ctxt thm,
            rtac ctxt trans_fun_cong_image_id_id_apply, etac ctxt @{thm Collect_case_prod_in_rel_leI}])
        (1 upto (m + n) ~~ set_map0s)];

    fun mk_only_if_tac ((((i, map_comp0), map_cong0), set_map0s), in_rel) =
      EVERY' [dtac ctxt (mk_conjunctN n i), rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
        etac ctxt allE, etac ctxt allE, etac ctxt impE, assume_tac ctxt,
        dtac ctxt (in_rel RS @{thm iffD1}),
        REPEAT_DETERM o eresolve_tac ctxt
          @{thms CollectE conjE exE CollectE Collect_case_prod_in_rel_leE},
        rtac ctxt @{thm bexI}, rtac ctxt conjI, rtac ctxt trans, rtac ctxt map_comp0, rtac ctxt trans, rtac ctxt map_cong0,
        REPEAT_DETERM_N m o rtac ctxt (@{thm id_comp} RS fun_cong),
        REPEAT_DETERM_N n o rtac ctxt (@{thm comp_id} RS fun_cong),
        assume_tac ctxt, rtac ctxt trans, rtac ctxt map_comp0, rtac ctxt trans, rtac ctxt map_cong0,
        REPEAT_DETERM_N m o rtac ctxt (@{thm id_comp} RS fun_cong),
        REPEAT_DETERM_N n o rtac ctxt (@{thm comp_id} RS fun_cong),
        rtac ctxt trans, rtac ctxt map_cong0,
        REPEAT_DETERM_N m o EVERY' [rtac ctxt @{thm Collect_case_prodD}, etac ctxt set_mp, assume_tac ctxt],
        REPEAT_DETERM_N n o rtac ctxt refl,
        assume_tac ctxt, rtac ctxt @{thm CollectI},
        CONJ_WRAP' (fn (i, thm) =>
          if i <= m then rtac ctxt subset_UNIV
          else EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt trans, rtac ctxt thm,
            rtac ctxt trans_fun_cong_image_id_id_apply, assume_tac ctxt])
        (1 upto (m + n) ~~ set_map0s)];
  in
    EVERY' [rtac ctxt (bis_def RS trans),
      rtac ctxt iffI, etac ctxt conjE, etac ctxt conjI, CONJ_WRAP' mk_if_tac thms,
      etac ctxt conjE, etac ctxt conjI, CONJ_WRAP' mk_only_if_tac thms] 1
  end;

fun mk_bis_converse_tac ctxt m bis_rel rel_congs rel_converseps =
  EVERY' [rtac ctxt (bis_rel RS iffD2), dtac ctxt (bis_rel RS iffD1),
    REPEAT_DETERM o etac ctxt conjE, rtac ctxt conjI,
    CONJ_WRAP' (K (EVERY' [rtac ctxt converse_shift, etac ctxt @{thm subset_trans},
      rtac ctxt @{thm equalityD2}, rtac ctxt @{thm converse_Times}])) rel_congs,
    CONJ_WRAP' (fn (rel_cong, rel_conversep) =>
      EVERY' [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
        rtac ctxt (rel_cong RS @{thm eq_refl} RS @{thm predicate2D}),
        REPEAT_DETERM_N m o rtac ctxt @{thm conversep_eq},
        REPEAT_DETERM_N (length rel_congs) o rtac ctxt @{thm conversep_in_rel},
        rtac ctxt (rel_conversep RS sym RS @{thm eq_refl} RS @{thm predicate2D}),
        REPEAT_DETERM o etac ctxt allE,
        rtac ctxt @{thm conversepI}, etac ctxt mp, etac ctxt @{thm converseD}]) (rel_congs ~~ rel_converseps)] 1;

fun mk_bis_O_tac ctxt m bis_rel rel_congs le_rel_OOs =
  EVERY' [rtac ctxt (bis_rel RS iffD2), REPEAT_DETERM o dtac ctxt (bis_rel RS iffD1),
    REPEAT_DETERM o etac ctxt conjE, rtac ctxt conjI,
    CONJ_WRAP' (K (EVERY' [etac ctxt @{thm relcomp_subset_Sigma}, assume_tac ctxt])) rel_congs,
    CONJ_WRAP' (fn (rel_cong, le_rel_OO) =>
      EVERY' [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
        rtac ctxt (rel_cong RS @{thm eq_refl} RS @{thm predicate2D}),
        REPEAT_DETERM_N m o rtac ctxt @{thm eq_OO},
        REPEAT_DETERM_N (length rel_congs) o rtac ctxt @{thm relcompp_in_rel},
        rtac ctxt (le_rel_OO RS @{thm predicate2D}),
        etac ctxt @{thm relcompE},
        REPEAT_DETERM o dtac ctxt prod_injectD,
        etac ctxt conjE, hyp_subst_tac ctxt,
        REPEAT_DETERM o etac ctxt allE, rtac ctxt @{thm relcomppI},
        etac ctxt mp, assume_tac ctxt, etac ctxt mp, assume_tac ctxt]) (rel_congs ~~ le_rel_OOs)] 1;

fun mk_bis_Gr_tac ctxt bis_rel rel_Grps mor_images morEs coalg_ins =
  unfold_thms_tac ctxt (bis_rel :: @{thm eq_alt} :: @{thm in_rel_Gr} :: rel_Grps) THEN
  EVERY' [rtac ctxt conjI,
    CONJ_WRAP' (fn thm => rtac ctxt (@{thm Gr_incl} RS iffD2) THEN' etac ctxt thm) mor_images,
    CONJ_WRAP' (fn (coalg_in, morE) =>
      EVERY' [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI, rtac ctxt @{thm GrpI}, etac ctxt (morE RS trans),
        etac ctxt @{thm GrD1}, etac ctxt (@{thm GrD2} RS arg_cong), etac ctxt coalg_in, etac ctxt @{thm GrD1}])
    (coalg_ins ~~ morEs)] 1;

fun mk_bis_Union_tac ctxt bis_def in_monos =
  let
    val n = length in_monos;
    val ks = 1 upto n;
  in
    unfold_thms_tac ctxt [bis_def] THEN
    EVERY' [rtac ctxt conjI,
      CONJ_WRAP' (fn i =>
        EVERY' [rtac ctxt @{thm UN_least}, dtac ctxt @{thm bspec}, assume_tac ctxt,
          dtac ctxt conjunct1, etac ctxt (mk_conjunctN n i)]) ks,
      CONJ_WRAP' (fn (i, in_mono) =>
        EVERY' [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI, etac ctxt @{thm UN_E},
          dtac ctxt @{thm bspec}, assume_tac ctxt,
          dtac ctxt conjunct2, dtac ctxt (mk_conjunctN n i), etac ctxt allE, etac ctxt allE, dtac ctxt mp,
          assume_tac ctxt, etac ctxt @{thm bexE}, rtac ctxt @{thm bexI}, assume_tac ctxt, rtac ctxt in_mono,
          REPEAT_DETERM_N n o etac ctxt @{thm SUP_upper2[OF _ subset_refl]},
          assume_tac ctxt]) (ks ~~ in_monos)] 1
  end;

fun mk_sbis_lsbis_tac ctxt lsbis_defs bis_Union bis_cong =
  let
    val n = length lsbis_defs;
  in
    EVERY' [rtac ctxt (Thm.permute_prems 0 1 bis_cong), EVERY' (map (rtac ctxt) lsbis_defs),
      rtac ctxt bis_Union, rtac ctxt @{thm ballI}, REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE exE},
      hyp_subst_tac ctxt, etac ctxt bis_cong, EVERY' (map (rtac ctxt o mk_nth_conv n) (1 upto n))] 1
  end;

fun mk_incl_lsbis_tac ctxt n i lsbis_def =
  EVERY' [rtac ctxt @{thm xt1(3)}, rtac ctxt lsbis_def, rtac ctxt @{thm SUP_upper2}, rtac ctxt @{thm CollectI},
    REPEAT_DETERM_N n o rtac ctxt exI, rtac ctxt conjI, rtac ctxt refl, assume_tac ctxt,
    rtac ctxt @{thm equalityD2}, rtac ctxt (mk_nth_conv n i)] 1;

fun mk_equiv_lsbis_tac ctxt sbis_lsbis lsbis_incl incl_lsbis bis_Id_on bis_converse bis_O =
  EVERY' [rtac ctxt @{thm equivI},
    rtac ctxt lsbis_incl,

    rtac ctxt @{thm refl_onI},
    rtac ctxt set_mp,
    rtac ctxt incl_lsbis, rtac ctxt bis_Id_on, assume_tac ctxt, etac ctxt @{thm Id_onI},

    rtac ctxt @{thm symI},
    rtac ctxt set_mp,
    rtac ctxt incl_lsbis, rtac ctxt bis_converse, rtac ctxt sbis_lsbis, etac ctxt @{thm converseI},

    rtac ctxt @{thm transI},
    rtac ctxt set_mp,
    rtac ctxt incl_lsbis, rtac ctxt bis_O, rtac ctxt sbis_lsbis, rtac ctxt sbis_lsbis,
    etac ctxt @{thm relcompI}, assume_tac ctxt] 1;

fun mk_coalgT_tac ctxt m defs strT_defs set_map0ss =
  let
    val n = length strT_defs;
    val ks = 1 upto n;
    fun coalg_tac (i, (active_sets, def)) =
      EVERY' [rtac ctxt @{thm ballI}, REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE},
        hyp_subst_tac ctxt, rtac ctxt (def RS trans RS @{thm ssubst_mem}), etac ctxt (arg_cong RS trans),
        rtac ctxt (mk_sum_caseN n i), rtac ctxt @{thm CollectI},
        REPEAT_DETERM_N m o EVERY' [rtac ctxt conjI, rtac ctxt subset_UNIV],
        CONJ_WRAP' (fn (i, thm) => EVERY' [rtac ctxt (thm RS ord_eq_le_trans),
          rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm CollectI}, rtac ctxt exI, rtac ctxt exI, rtac ctxt conjI, rtac ctxt refl,
          rtac ctxt conjI,
          rtac ctxt conjI, etac ctxt @{thm empty_Shift}, dtac ctxt set_rev_mp,
            etac ctxt @{thm equalityD1}, etac ctxt @{thm CollectD},
          rtac ctxt @{thm ballI},
            CONJ_WRAP' (fn i => EVERY' [rtac ctxt @{thm ballI}, etac ctxt @{thm CollectE}, dtac ctxt @{thm ShiftD},
              dtac ctxt @{thm bspec}, etac ctxt thin_rl, assume_tac ctxt, dtac ctxt (mk_conjunctN n i),
              dtac ctxt @{thm bspec}, rtac ctxt @{thm CollectI}, etac ctxt @{thm set_mp[OF equalityD1[OF Succ_Shift]]},
              REPEAT_DETERM o eresolve_tac ctxt [exE, conjE], rtac ctxt exI,
              rtac ctxt conjI, rtac ctxt (@{thm shift_def} RS fun_cong RS trans),
              rtac ctxt (@{thm append_Cons} RS sym RS arg_cong RS trans), assume_tac ctxt,
              CONJ_WRAP' (K (EVERY' [etac ctxt trans, rtac ctxt @{thm Collect_cong},
                rtac ctxt @{thm eqset_imp_iff}, rtac ctxt sym, rtac ctxt trans, rtac ctxt @{thm Succ_Shift},
                rtac ctxt (@{thm append_Cons} RS sym RS arg_cong)])) ks]) ks,
          dtac ctxt @{thm bspec}, assume_tac ctxt, dtac ctxt (mk_conjunctN n i), dtac ctxt @{thm bspec},
          etac ctxt @{thm set_mp[OF equalityD1]}, assume_tac ctxt,
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE], rtac ctxt exI,
          rtac ctxt conjI, rtac ctxt (@{thm shift_def} RS fun_cong RS trans),
          etac ctxt (@{thm append_Nil} RS sym RS arg_cong RS trans),
          REPEAT_DETERM_N m o (rtac ctxt conjI THEN' assume_tac ctxt),
          CONJ_WRAP' (K (EVERY' [etac ctxt trans, rtac ctxt @{thm Collect_cong},
            rtac ctxt @{thm eqset_imp_iff}, rtac ctxt sym, rtac ctxt trans, rtac ctxt @{thm Succ_Shift},
            rtac ctxt (@{thm append_Nil} RS sym RS arg_cong)])) ks]) (ks ~~ active_sets)];
  in
    unfold_thms_tac ctxt defs THEN
    CONJ_WRAP' coalg_tac (ks ~~ (map (drop m) set_map0ss ~~ strT_defs)) 1
  end;

fun mk_length_Lev_tac ctxt cts Lev_0s Lev_Sucs =
  let
    val n = length Lev_0s;
    val ks = n downto 1;
  in
    EVERY' [rtac ctxt (Thm.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn Lev_0 =>
        EVERY' [rtac ctxt impI, dtac ctxt (Lev_0 RS @{thm equalityD1} RS set_mp),
          etac ctxt @{thm singletonE}, etac ctxt ssubst, rtac ctxt @{thm list.size(3)}]) Lev_0s,
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn Lev_Suc =>
        EVERY' [rtac ctxt impI, dtac ctxt (Lev_Suc RS @{thm equalityD1} RS set_mp),
          CONJ_WRAP_GEN' (etac ctxt (Thm.permute_prems 1 1 @{thm UnE}))
            (fn i =>
              EVERY' [REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE}, hyp_subst_tac ctxt,
                rtac ctxt trans, rtac ctxt @{thm length_Cons}, rtac ctxt @{thm arg_cong[of _ _ Suc]},
                REPEAT_DETERM o etac ctxt allE, dtac ctxt (mk_conjunctN n i),
                etac ctxt mp, assume_tac ctxt]) ks])
      Lev_Sucs] 1
  end;

fun mk_length_Lev'_tac ctxt length_Lev =
  EVERY' [forward_tac ctxt [length_Lev], etac ctxt ssubst, assume_tac ctxt] 1;

fun mk_rv_last_tac ctxt cTs cts rv_Nils rv_Conss =
  let
    val n = length rv_Nils;
    val ks = 1 upto n;
  in
    EVERY' [rtac ctxt (Thm.instantiate' cTs cts @{thm list.induct}),
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn rv_Cons =>
        CONJ_WRAP' (fn (i, rv_Nil) => (EVERY' [rtac ctxt exI,
          rtac ctxt (@{thm append_Nil} RS arg_cong RS trans),
          rtac ctxt (rv_Cons RS trans), rtac ctxt (mk_sum_caseN n i RS trans), rtac ctxt rv_Nil]))
        (ks ~~ rv_Nils))
      rv_Conss,
      REPEAT_DETERM o rtac ctxt allI, rtac ctxt (mk_sumEN n),
      EVERY' (map (fn i =>
        CONJ_WRAP' (fn rv_Cons => EVERY' [REPEAT_DETERM o etac ctxt allE, dtac ctxt (mk_conjunctN n i),
          CONJ_WRAP' (fn i' => EVERY' [dtac ctxt (mk_conjunctN n i'), etac ctxt exE, rtac ctxt exI,
            rtac ctxt (@{thm append_Cons} RS arg_cong RS trans), rtac ctxt (rv_Cons RS trans),
            if n = 1 then K all_tac else etac ctxt (sum_case_cong_weak RS trans),
            rtac ctxt (mk_sum_caseN n i RS trans), assume_tac ctxt])
          ks])
        rv_Conss)
      ks)] 1
  end;

fun mk_set_Lev_tac ctxt cts Lev_0s Lev_Sucs rv_Nils rv_Conss from_to_sbdss =
  let
    val n = length Lev_0s;
    val ks = 1 upto n;
  in
    EVERY' [rtac ctxt (Thm.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn ((i, (Lev_0, Lev_Suc)), rv_Nil) =>
        EVERY' [rtac ctxt impI, dtac ctxt (Lev_0 RS @{thm equalityD1} RS set_mp),
          etac ctxt @{thm singletonE}, hyp_subst_tac ctxt,
          CONJ_WRAP' (fn i' => rtac ctxt impI THEN' dtac ctxt (sym RS trans) THEN' rtac ctxt rv_Nil THEN'
            (if i = i'
            then EVERY' [dtac ctxt (mk_InN_inject n i), hyp_subst_tac ctxt,
              CONJ_WRAP' (fn (i'', Lev_0'') =>
                EVERY' [rtac ctxt impI, rtac ctxt @{thm ssubst_mem[OF append_Nil]},
                  rtac ctxt (Lev_Suc RS @{thm equalityD2} RS set_mp), rtac ctxt (mk_UnIN n i''),
                  rtac ctxt @{thm CollectI}, REPEAT_DETERM o rtac ctxt exI, rtac ctxt conjI, rtac ctxt refl,
                  etac ctxt conjI, rtac ctxt (Lev_0'' RS @{thm equalityD2} RS set_mp),
                  rtac ctxt @{thm singletonI}])
              (ks ~~ Lev_0s)]
            else etac ctxt (mk_InN_not_InM i' i RS notE)))
          ks])
      ((ks ~~ (Lev_0s ~~ Lev_Sucs)) ~~ rv_Nils),
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn ((Lev_Suc, rv_Cons), from_to_sbds) =>
        EVERY' [rtac ctxt impI, dtac ctxt (Lev_Suc RS @{thm equalityD1} RS set_mp),
          CONJ_WRAP_GEN' (etac ctxt (Thm.permute_prems 1 1 @{thm UnE}))
            (fn (i, from_to_sbd) =>
              EVERY' [REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE}, hyp_subst_tac ctxt,
                CONJ_WRAP' (fn i' => rtac ctxt impI THEN'
                  CONJ_WRAP' (fn i'' =>
                    EVERY' [rtac ctxt impI, rtac ctxt (Lev_Suc RS @{thm equalityD2} RS set_mp),
                      rtac ctxt @{thm ssubst_mem[OF append_Cons]}, rtac ctxt (mk_UnIN n i),
                      rtac ctxt @{thm CollectI}, REPEAT_DETERM o rtac ctxt exI, rtac ctxt conjI, rtac ctxt refl,
                      rtac ctxt conjI, assume_tac ctxt, dtac ctxt (sym RS trans RS sym),
                      rtac ctxt (rv_Cons RS trans), rtac ctxt (mk_sum_caseN n i RS trans),
                      etac ctxt (from_to_sbd RS arg_cong), REPEAT_DETERM o etac ctxt allE,
                      dtac ctxt (mk_conjunctN n i), dtac ctxt mp, assume_tac ctxt,
                      dtac ctxt (mk_conjunctN n i'), dtac ctxt mp, assume_tac ctxt,
                      dtac ctxt (mk_conjunctN n i''), etac ctxt mp, assume_tac ctxt])
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
    EVERY' [rtac ctxt (Thm.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn ((i, (Lev_0, Lev_Suc)), rv_Nil) =>
        EVERY' [rtac ctxt impI, dtac ctxt (Lev_0 RS @{thm equalityD1} RS set_mp),
          etac ctxt @{thm singletonE}, hyp_subst_tac ctxt,
          CONJ_WRAP' (fn i' => rtac ctxt impI THEN'
            CONJ_WRAP' (fn i'' => rtac ctxt impI  THEN' dtac ctxt (sym RS trans) THEN' rtac ctxt rv_Nil THEN'
              (if i = i''
              then EVERY' [dtac ctxt @{thm ssubst_mem[OF sym[OF append_Nil]]},
                dtac ctxt (Lev_Suc RS @{thm equalityD1} RS set_mp), dtac ctxt (mk_InN_inject n i),
                hyp_subst_tac ctxt,
                CONJ_WRAP_GEN' (etac ctxt (Thm.permute_prems 1 1 @{thm UnE}))
                  (fn k => REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE} THEN'
                    dtac ctxt list_inject_iffD1 THEN' etac ctxt conjE THEN'
                    (if k = i'
                    then EVERY' [dtac ctxt (mk_InN_inject n k), hyp_subst_tac ctxt, etac ctxt @{thm imageI}]
                    else etac ctxt (mk_InN_not_InM i' k RS notE)))
                (rev ks)]
              else etac ctxt (mk_InN_not_InM i'' i RS notE)))
            ks)
          ks])
      ((ks ~~ (Lev_0s ~~ Lev_Sucs)) ~~ rv_Nils),
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn ((Lev_Suc, rv_Cons), (from_to_sbds, to_sbd_injs)) =>
        EVERY' [rtac ctxt impI, dtac ctxt (Lev_Suc RS @{thm equalityD1} RS set_mp),
          CONJ_WRAP_GEN' (etac ctxt (Thm.permute_prems 1 1 @{thm UnE}))
            (fn (i, (from_to_sbd, to_sbd_inj)) =>
              REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE} THEN' hyp_subst_tac ctxt THEN'
              CONJ_WRAP' (fn i' => rtac ctxt impI THEN'
                dtac ctxt @{thm ssubst_mem[OF sym[OF append_Cons]]} THEN'
                dtac ctxt (Lev_Suc RS @{thm equalityD1} RS set_mp) THEN'
                CONJ_WRAP_GEN' (etac ctxt (Thm.permute_prems 1 1 @{thm UnE})) (fn k =>
                  REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE} THEN'
                  dtac ctxt list_inject_iffD1 THEN' etac ctxt conjE THEN'
                  (if k = i
                  then EVERY' [dtac ctxt (mk_InN_inject n i),
                    dtac ctxt (Thm.permute_prems 0 2 (to_sbd_inj RS iffD1)),
                    assume_tac ctxt, assume_tac ctxt, hyp_subst_tac ctxt] THEN'
                    CONJ_WRAP' (fn i'' =>
                      EVERY' [rtac ctxt impI, dtac ctxt (sym RS trans),
                        rtac ctxt (rv_Cons RS trans), rtac ctxt (mk_sum_caseN n i RS arg_cong RS trans),
                        etac ctxt (from_to_sbd RS arg_cong),
                        REPEAT_DETERM o etac ctxt allE,
                        dtac ctxt (mk_conjunctN n i), dtac ctxt mp, assume_tac ctxt,
                        dtac ctxt (mk_conjunctN n i'), dtac ctxt mp, assume_tac ctxt,
                        dtac ctxt (mk_conjunctN n i''), etac ctxt mp, etac ctxt sym])
                    ks
                  else etac ctxt (mk_InN_not_InM i k RS notE)))
                (rev ks))
              ks)
          (rev (ks ~~ (from_to_sbds ~~ to_sbd_injs)))])
      ((Lev_Sucs ~~ rv_Conss) ~~ (from_to_sbdss ~~ to_sbd_injss))] 1
  end;

fun mk_mor_beh_tac ctxt m mor_def mor_cong beh_defs carT_defs strT_defs isNode_defs to_sbd_injss
  from_to_sbdss Lev_0s Lev_Sucs rv_Nils rv_Conss length_Levs length_Lev's rv_lastss set_Levsss
  set_image_Levsss set_map0ss map_comp_ids map_cong0s =
  let
    val n = length beh_defs;
    val ks = 1 upto n;

    fun fbetw_tac (i, (carT_def, (isNode_def, (Lev_0, (rv_Nil, ((length_Lev, length_Lev'),
      (rv_lasts, (set_map0s, (set_Levss, set_image_Levss))))))))) =
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt (carT_def RS @{thm equalityD2} RS set_mp),
        rtac ctxt @{thm CollectI}, REPEAT_DETERM o rtac ctxt exI, rtac ctxt conjI, rtac ctxt refl, rtac ctxt conjI,
        rtac ctxt conjI,
          rtac ctxt @{thm UN_I}, rtac ctxt @{thm UNIV_I}, rtac ctxt (Lev_0 RS @{thm equalityD2} RS set_mp),
          rtac ctxt @{thm singletonI},
        (**)
          rtac ctxt @{thm ballI}, etac ctxt @{thm UN_E},
          CONJ_WRAP' (fn (i, (rv_last, (isNode_def, (set_map0s,
            (set_Levs, set_image_Levs))))) =>
            EVERY' [rtac ctxt @{thm ballI},
              REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE SuccE UN_E},
              rtac ctxt (rev_mp OF [rv_last, impI]), etac ctxt exE, rtac ctxt (isNode_def RS iffD2),
              rtac ctxt exI, rtac ctxt conjI,
              if n = 1 then rtac ctxt refl
              else etac ctxt (sum_case_cong_weak RS trans) THEN' rtac ctxt (mk_sum_caseN n i),
              CONJ_WRAP' (fn (set_map0, (set_Lev, set_image_Lev)) =>
                EVERY' [rtac ctxt (set_map0 RS trans), rtac ctxt @{thm equalityI}, rtac ctxt @{thm image_subsetI},
                  rtac ctxt @{thm CollectI}, rtac ctxt @{thm SuccI}, rtac ctxt @{thm UN_I}, rtac ctxt @{thm UNIV_I}, etac ctxt set_Lev,
                  if n = 1 then rtac ctxt refl else assume_tac ctxt, assume_tac ctxt, rtac ctxt @{thm subsetI},
                  REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE SuccE UN_E},
                  REPEAT_DETERM_N 4 o etac ctxt thin_rl,
                  rtac ctxt set_image_Lev,
                  assume_tac ctxt, dtac ctxt length_Lev, hyp_subst_tac ctxt, dtac ctxt length_Lev',
                  etac ctxt @{thm set_mp[OF equalityD1[OF arg_cong[OF length_append_singleton]]]},
                  if n = 1 then rtac ctxt refl else assume_tac ctxt])
              (drop m set_map0s ~~ (set_Levs ~~ set_image_Levs))])
          (ks ~~ (rv_lasts ~~ (isNode_defs ~~ (set_map0ss ~~
            (set_Levss ~~ set_image_Levss))))),
        (*root isNode*)
          rtac ctxt (isNode_def RS iffD2), rtac ctxt exI, rtac ctxt conjI,
          CONVERSION (Conv.top_conv
            (K (Conv.try_conv (Conv.rewr_conv (rv_Nil RS eq_reflection)))) ctxt),
          if n = 1 then rtac ctxt refl else rtac ctxt (mk_sum_caseN n i),
          CONJ_WRAP' (fn (set_map0, (set_Lev, set_image_Lev)) =>
            EVERY' [rtac ctxt (set_map0 RS trans), rtac ctxt @{thm equalityI}, rtac ctxt @{thm image_subsetI},
              rtac ctxt @{thm CollectI}, rtac ctxt @{thm SuccI}, rtac ctxt @{thm UN_I}, rtac ctxt @{thm UNIV_I}, rtac ctxt set_Lev,
              rtac ctxt (Lev_0 RS @{thm equalityD2} RS set_mp), rtac ctxt @{thm singletonI}, rtac ctxt rv_Nil,
              assume_tac ctxt, rtac ctxt @{thm subsetI},
              REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE SuccE UN_E},
              rtac ctxt set_image_Lev, rtac ctxt (Lev_0 RS @{thm equalityD2} RS set_mp),
              rtac ctxt @{thm singletonI}, dtac ctxt length_Lev',
              etac ctxt @{thm set_mp[OF equalityD1[OF arg_cong[OF
                trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]]},
              rtac ctxt rv_Nil])
          (drop m set_map0s ~~ (nth set_Levss (i - 1) ~~ nth set_image_Levss (i - 1)))];

    fun mor_tac (i, (strT_def, ((Lev_Suc, (rv_Nil, rv_Cons)),
      ((map_comp_id, map_cong0), (length_Lev', (from_to_sbds, to_sbd_injs)))))) =
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt sym, rtac ctxt trans, rtac ctxt strT_def,
        CONVERSION (Conv.top_conv
          (K (Conv.try_conv (Conv.rewr_conv (rv_Nil RS eq_reflection)))) ctxt),
        if n = 1 then K all_tac
        else (rtac ctxt (sum_case_cong_weak RS trans) THEN'
          rtac ctxt (mk_sum_caseN n i) THEN' rtac ctxt (mk_sum_caseN n i RS trans)),
        rtac ctxt (map_comp_id RS trans), rtac ctxt (map_cong0 OF replicate m refl),
        EVERY' (@{map 3} (fn i' => fn to_sbd_inj => fn from_to_sbd =>
          DETERM o EVERY' [rtac ctxt trans, rtac ctxt o_apply, rtac ctxt prod_injectI, rtac ctxt conjI,
            rtac ctxt trans, rtac ctxt @{thm Shift_def},
            rtac ctxt @{thm equalityI}, rtac ctxt @{thm subsetI}, etac ctxt thin_rl,
            REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE UN_E}, dtac ctxt length_Lev', dtac ctxt asm_rl,
            etac ctxt thin_rl, dtac ctxt @{thm set_rev_mp[OF _ equalityD1]},
            rtac ctxt (@{thm length_Cons} RS arg_cong RS trans), rtac ctxt Lev_Suc,
            CONJ_WRAP_GEN' (etac ctxt (Thm.permute_prems 1 1 @{thm UnE})) (fn i'' =>
              EVERY' [REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE},
                dtac ctxt list_inject_iffD1, etac ctxt conjE,
                if i' = i'' then EVERY' [dtac ctxt (mk_InN_inject n i'),
                  dtac ctxt (Thm.permute_prems 0 2 (to_sbd_inj RS iffD1)),
                  assume_tac ctxt, assume_tac ctxt, hyp_subst_tac ctxt, etac ctxt @{thm UN_I[OF UNIV_I]}]
                else etac ctxt (mk_InN_not_InM i' i'' RS notE)])
            (rev ks),
            rtac ctxt @{thm UN_least}, rtac ctxt @{thm subsetI}, rtac ctxt @{thm CollectI}, rtac ctxt @{thm UN_I[OF UNIV_I]},
            rtac ctxt (Lev_Suc RS @{thm equalityD2} RS set_mp), rtac ctxt (mk_UnIN n i'), rtac ctxt @{thm CollectI},
            REPEAT_DETERM o rtac ctxt exI, rtac ctxt conjI, rtac ctxt refl, etac ctxt conjI, assume_tac ctxt,
            rtac ctxt trans, rtac ctxt @{thm shift_def}, rtac ctxt iffD2, rtac ctxt @{thm fun_eq_iff}, rtac ctxt allI,
            CONVERSION (Conv.top_conv
              (K (Conv.try_conv (Conv.rewr_conv (rv_Cons RS eq_reflection)))) ctxt),
            if n = 1 then K all_tac
            else rtac ctxt sum_case_cong_weak THEN' rtac ctxt (mk_sum_caseN n i' RS trans),
            SELECT_GOAL (unfold_thms_tac ctxt [from_to_sbd]), rtac ctxt refl])
        ks to_sbd_injs from_to_sbds)];
  in
    (rtac ctxt mor_cong THEN'
    EVERY' (map (fn thm => rtac ctxt (thm RS @{thm ext})) beh_defs) THEN'
    rtac ctxt (mor_def RS iffD2) THEN' rtac ctxt conjI THEN'
    CONJ_WRAP' fbetw_tac
      (ks ~~ (carT_defs ~~ (isNode_defs ~~ (Lev_0s ~~ (rv_Nils ~~ ((length_Levs ~~ length_Lev's) ~~
        (rv_lastss ~~ (set_map0ss ~~ (set_Levsss ~~ set_image_Levsss))))))))) THEN'
    CONJ_WRAP' mor_tac
      (ks ~~ (strT_defs ~~ ((Lev_Sucs ~~ (rv_Nils ~~ rv_Conss)) ~~
        ((map_comp_ids ~~ map_cong0s) ~~
          (length_Lev's ~~ (from_to_sbdss ~~ to_sbd_injss))))))) 1
  end;

fun mk_congruent_str_final_tac ctxt m lsbisE map_comp_id map_cong0 equiv_LSBISs =
  EVERY' [rtac ctxt @{thm congruentI}, dtac ctxt lsbisE,
    REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE bexE}, rtac ctxt (o_apply RS trans),
    etac ctxt (sym RS arg_cong RS trans), rtac ctxt (map_comp_id RS trans),
    rtac ctxt (map_cong0 RS trans), REPEAT_DETERM_N m o rtac ctxt refl,
    EVERY' (map (fn equiv_LSBIS =>
      EVERY' [rtac ctxt @{thm equiv_proj}, rtac ctxt equiv_LSBIS, etac ctxt set_mp, assume_tac ctxt])
    equiv_LSBISs), rtac ctxt sym, rtac ctxt (o_apply RS trans),
    etac ctxt (sym RS arg_cong RS trans), rtac ctxt map_comp_id] 1;

fun mk_coalg_final_tac ctxt m coalg_def congruent_str_finals equiv_LSBISs set_map0ss coalgT_setss =
  EVERY' [rtac ctxt (coalg_def RS iffD2),
    CONJ_WRAP' (fn ((set_map0s, coalgT_sets), (equiv_LSBIS, congruent_str_final)) =>
      EVERY' [rtac ctxt @{thm univ_preserves}, rtac ctxt equiv_LSBIS, rtac ctxt congruent_str_final,
        rtac ctxt @{thm ballI}, rtac ctxt @{thm ssubst_mem}, rtac ctxt o_apply, rtac ctxt @{thm CollectI},
        REPEAT_DETERM_N m o EVERY' [rtac ctxt conjI, rtac ctxt subset_UNIV],
        CONJ_WRAP' (fn (equiv_LSBIS, (set_map0, coalgT_set)) =>
          EVERY' [rtac ctxt (set_map0 RS ord_eq_le_trans),
            rtac ctxt @{thm image_subsetI}, rtac ctxt iffD2, rtac ctxt @{thm proj_in_iff},
            rtac ctxt equiv_LSBIS, etac ctxt set_rev_mp, etac ctxt coalgT_set])
        (equiv_LSBISs ~~ (drop m set_map0s ~~ coalgT_sets))])
    ((set_map0ss ~~ coalgT_setss) ~~ (equiv_LSBISs ~~ congruent_str_finals))] 1;

fun mk_mor_T_final_tac ctxt mor_def congruent_str_finals equiv_LSBISs =
  EVERY' [rtac ctxt (mor_def RS iffD2), rtac ctxt conjI,
    CONJ_WRAP' (fn equiv_LSBIS =>
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt iffD2, rtac ctxt @{thm proj_in_iff},
        rtac ctxt equiv_LSBIS, assume_tac ctxt])
    equiv_LSBISs,
    CONJ_WRAP' (fn (equiv_LSBIS, congruent_str_final) =>
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt sym, rtac ctxt trans, rtac ctxt @{thm univ_commute}, rtac ctxt equiv_LSBIS,
        rtac ctxt congruent_str_final, assume_tac ctxt, rtac ctxt o_apply])
    (equiv_LSBISs ~~ congruent_str_finals)] 1;

fun mk_mor_Rep_tac ctxt defs Reps Abs_inverses coalg_final_setss map_comp_ids map_cong0Ls =
  unfold_thms_tac ctxt defs THEN
  EVERY' [rtac ctxt conjI,
    CONJ_WRAP' (fn thm => rtac ctxt @{thm ballI} THEN' rtac ctxt thm) Reps,
    CONJ_WRAP' (fn (Rep, ((map_comp_id, map_cong0L), coalg_final_sets)) =>
      EVERY' [rtac ctxt @{thm ballI}, rtac ctxt (map_comp_id RS trans), rtac ctxt map_cong0L,
        EVERY' (map2 (fn Abs_inverse => fn coalg_final_set =>
          EVERY' [rtac ctxt @{thm ballI}, rtac ctxt (o_apply RS trans), rtac ctxt Abs_inverse,
            etac ctxt set_rev_mp, rtac ctxt coalg_final_set, rtac ctxt Rep])
        Abs_inverses coalg_final_sets)])
    (Reps ~~ ((map_comp_ids ~~ map_cong0Ls) ~~ coalg_final_setss))] 1;

fun mk_mor_Abs_tac ctxt defs Abs_inverses =
  unfold_thms_tac ctxt defs THEN
  EVERY' [rtac ctxt conjI,
    CONJ_WRAP' (K (rtac ctxt @{thm ballI} THEN' rtac ctxt @{thm UNIV_I})) Abs_inverses,
    CONJ_WRAP' (fn thm => rtac ctxt @{thm ballI} THEN' etac ctxt (thm RS arg_cong RS sym)) Abs_inverses] 1;

fun mk_mor_unfold_tac ctxt m mor_UNIV dtor_defs unfold_defs Abs_inverses morEs map_comp_ids map_cong0s =
  EVERY' [rtac ctxt iffD2, rtac ctxt mor_UNIV,
    CONJ_WRAP' (fn ((Abs_inverse, morE), ((dtor_def, unfold_def), (map_comp_id, map_cong0))) =>
      EVERY' [rtac ctxt @{thm ext}, rtac ctxt (o_apply RS trans RS sym), rtac ctxt (dtor_def RS trans),
        rtac ctxt (unfold_def RS arg_cong RS trans), rtac ctxt (Abs_inverse RS arg_cong RS trans),
        rtac ctxt (morE RS arg_cong RS trans), rtac ctxt (map_comp_id RS trans),
        rtac ctxt (o_apply RS trans RS sym), rtac ctxt map_cong0,
        REPEAT_DETERM_N m o rtac ctxt refl,
        EVERY' (map (fn thm => rtac ctxt (thm RS trans) THEN' rtac ctxt (o_apply RS sym)) unfold_defs)])
    ((Abs_inverses ~~ morEs) ~~ ((dtor_defs ~~ unfold_defs) ~~ (map_comp_ids ~~ map_cong0s)))] 1;

fun mk_raw_coind_tac ctxt bis_def bis_cong bis_O bis_converse bis_Gr tcoalg coalgT mor_T_final
  sbis_lsbis lsbis_incls incl_lsbiss equiv_LSBISs mor_Rep Rep_injects =
  let
    val n = length Rep_injects;
  in
    EVERY' [rtac ctxt rev_mp, forward_tac ctxt [bis_def RS iffD1],
      REPEAT_DETERM o etac ctxt conjE, rtac ctxt bis_cong, rtac ctxt bis_O, rtac ctxt bis_converse,
      rtac ctxt bis_Gr, rtac ctxt tcoalg, rtac ctxt mor_Rep, rtac ctxt bis_O, assume_tac ctxt,
      rtac ctxt bis_Gr, rtac ctxt tcoalg,
      rtac ctxt mor_Rep, REPEAT_DETERM_N n o etac ctxt @{thm relImage_Gr},
      rtac ctxt impI, rtac ctxt rev_mp, rtac ctxt bis_cong, rtac ctxt bis_O, rtac ctxt bis_Gr, rtac ctxt coalgT,
      rtac ctxt mor_T_final, rtac ctxt bis_O, rtac ctxt sbis_lsbis, rtac ctxt bis_converse, rtac ctxt bis_Gr, rtac ctxt coalgT,
      rtac ctxt mor_T_final, EVERY' (map (fn thm => rtac ctxt (thm RS @{thm relInvImage_Gr})) lsbis_incls),
      rtac ctxt impI,
      CONJ_WRAP' (fn (Rep_inject, (equiv_LSBIS , (incl_lsbis, lsbis_incl))) =>
        EVERY' [rtac ctxt @{thm subset_trans}, rtac ctxt @{thm relInvImage_UNIV_relImage}, rtac ctxt @{thm subset_trans},
          rtac ctxt @{thm relInvImage_mono}, rtac ctxt @{thm subset_trans}, etac ctxt incl_lsbis,
          rtac ctxt ord_eq_le_trans, rtac ctxt @{thm sym[OF relImage_relInvImage]},
          rtac ctxt @{thm xt1(3)}, rtac ctxt @{thm Sigma_cong},
          rtac ctxt @{thm proj_image}, rtac ctxt @{thm proj_image}, rtac ctxt lsbis_incl,
          rtac ctxt @{thm subset_trans}, rtac ctxt @{thm relImage_mono}, rtac ctxt incl_lsbis, assume_tac ctxt,
          rtac ctxt @{thm relImage_proj}, rtac ctxt equiv_LSBIS, rtac ctxt @{thm relInvImage_Id_on},
          rtac ctxt Rep_inject])
      (Rep_injects ~~ (equiv_LSBISs ~~ (incl_lsbiss ~~ lsbis_incls)))] 1
  end;

fun mk_unfold_unique_mor_tac ctxt raw_coinds bis mor unfold_defs =
  CONJ_WRAP' (fn (raw_coind, unfold_def) =>
    EVERY' [rtac ctxt @{thm ext}, etac ctxt (bis RS raw_coind RS set_mp RS @{thm IdD}), rtac ctxt mor,
      rtac ctxt @{thm image2_eqI}, rtac ctxt refl, rtac ctxt (unfold_def RS arg_cong RS trans),
      rtac ctxt (o_apply RS sym), rtac ctxt @{thm UNIV_I}]) (raw_coinds ~~ unfold_defs) 1;

fun mk_dtor_o_ctor_tac ctxt ctor_def unfold map_comp_id map_cong0L unfold_o_dtors =
  unfold_thms_tac ctxt [ctor_def] THEN EVERY' [rtac ctxt @{thm ext}, rtac ctxt trans, rtac ctxt o_apply,
    rtac ctxt trans, rtac ctxt unfold, rtac ctxt trans, rtac ctxt map_comp_id, rtac ctxt trans, rtac ctxt map_cong0L,
    EVERY' (map (fn thm =>
      rtac ctxt @{thm ballI} THEN' rtac ctxt (trans OF [thm RS fun_cong, id_apply])) unfold_o_dtors),
    rtac ctxt sym, rtac ctxt id_apply] 1;

fun mk_corec_tac ctxt m corec_defs unfold map_cong0 corec_Inls =
  unfold_thms_tac ctxt corec_defs THEN EVERY' [rtac ctxt trans, rtac ctxt (o_apply RS arg_cong),
    rtac ctxt trans, rtac ctxt unfold, fo_rtac ctxt (@{thm sum.case(2)} RS arg_cong RS trans),
    rtac ctxt map_cong0, REPEAT_DETERM_N m o rtac ctxt refl,
    EVERY' (map (fn thm => rtac ctxt @{thm case_sum_expand_Inr} THEN' rtac ctxt thm) corec_Inls)] 1;

fun mk_corec_unique_mor_tac ctxt corec_defs corec_Inls unfold_unique_mor =
  unfold_thms_tac ctxt
    (corec_defs @ map (fn thm => thm RS @{thm case_sum_expand_Inr'}) corec_Inls) THEN
  etac ctxt unfold_unique_mor 1;

fun mk_dtor_coinduct_tac ctxt m raw_coind bis_rel rel_congs =
  EVERY' [rtac ctxt rev_mp, rtac ctxt raw_coind, rtac ctxt iffD2, rtac ctxt bis_rel, rtac ctxt conjI,
    CONJ_WRAP' (K (rtac ctxt @{thm ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]]}))
    rel_congs,
    CONJ_WRAP' (fn rel_cong => EVERY' [rtac ctxt allI, rtac ctxt allI, rtac ctxt impI,
      REPEAT_DETERM o etac ctxt allE, rtac ctxt (rel_cong RS @{thm eq_refl} RS @{thm predicate2D}),
      REPEAT_DETERM_N m o rtac ctxt refl,
      REPEAT_DETERM_N (length rel_congs) o rtac ctxt @{thm in_rel_Collect_case_prod_eq[symmetric]},
      etac ctxt mp, etac ctxt @{thm CollectE}, etac ctxt @{thm case_prodD}])
    rel_congs,
    rtac ctxt impI, REPEAT_DETERM o etac ctxt conjE,
    CONJ_WRAP' (K (EVERY' [rtac ctxt impI, rtac ctxt @{thm IdD}, etac ctxt set_mp,
      rtac ctxt @{thm CollectI}, etac ctxt @{thm case_prodI}])) rel_congs] 1;

fun mk_map_tac ctxt m n map_arg_cong unfold map_comp map_cong0 =
  EVERY' [rtac ctxt @{thm ext}, rtac ctxt (o_apply RS trans RS sym), rtac ctxt (o_apply RS trans RS sym),
    rtac ctxt (unfold RS trans), rtac ctxt (Thm.permute_prems 0 1 (map_comp RS @{thm box_equals})),
    rtac ctxt map_cong0,
    REPEAT_DETERM_N m o rtac ctxt (@{thm id_comp} RS fun_cong),
    REPEAT_DETERM_N n o rtac ctxt (@{thm comp_id} RS fun_cong),
    rtac ctxt map_arg_cong, rtac ctxt (o_apply RS sym)] 1;

fun mk_set_le_tac ctxt n Jset_minimal set_Jsets set_Jset_Jsetss =
  EVERY' [rtac ctxt Jset_minimal,
    REPEAT_DETERM_N n o rtac ctxt @{thm Un_upper1},
    REPEAT_DETERM_N n o
      EVERY' (@{map 3} (fn i => fn set_Jset => fn set_Jset_Jsets =>
        EVERY' [rtac ctxt @{thm subsetI}, rtac ctxt @{thm UnI2}, rtac ctxt (mk_UnIN n i), etac ctxt @{thm UN_I},
          etac ctxt @{thm UnE}, etac ctxt set_Jset, REPEAT_DETERM_N (n - 1) o etac ctxt @{thm UnE},
          EVERY' (map (fn thm => EVERY' [etac ctxt @{thm UN_E}, etac ctxt thm, assume_tac ctxt]) set_Jset_Jsets)])
      (1 upto n) set_Jsets set_Jset_Jsetss)] 1;

fun mk_set_ge_tac ctxt n set_incl_Jset set_Jset_incl_Jsets =
  EVERY' [rtac ctxt @{thm Un_least}, rtac ctxt set_incl_Jset,
    REPEAT_DETERM_N (n - 1) o rtac ctxt @{thm Un_least},
    EVERY' (map (fn thm => rtac ctxt @{thm UN_least} THEN' etac ctxt thm) set_Jset_incl_Jsets)] 1;

fun mk_map_id0_tac ctxt maps unfold_unique unfold_dtor =
  EVERY' [rtac ctxt (unfold_unique RS trans), EVERY' (map (rtac ctxt o mk_sym) maps),
    rtac ctxt unfold_dtor] 1;

fun mk_map_comp0_tac ctxt maps map_comp0s map_unique =
  EVERY' [rtac ctxt map_unique,
    EVERY' (map2 (fn map_thm => fn map_comp0 =>
      EVERY' (map (rtac ctxt)
        [@{thm comp_assoc[symmetric]} RS trans,
        @{thm arg_cong2[of _ _ _ _ "(\<circ>)"]} OF [map_thm, refl] RS trans,
        @{thm comp_assoc[symmetric]} RS sym RS trans, map_thm RS arg_cong RS trans,
        @{thm comp_assoc[symmetric]} RS trans,
        @{thm arg_cong2[of _ _ _ _ "(\<circ>)"]} OF [map_comp0 RS sym, refl]]))
    maps map_comp0s)] 1;

fun mk_mcong_tac ctxt m coinduct_tac map_comps dtor_maps map_cong0s set_map0ss set_Jsetss
  set_Jset_Jsetsss in_rels =
  let
    val n = length map_comps;
    val ks = 1 upto n;
  in
    EVERY' ([rtac ctxt rev_mp, coinduct_tac] @
      maps (fn ((((((map_comp_trans, dtor_maps_trans), map_cong0), set_map0s), set_Jsets),
        set_Jset_Jsetss), in_rel) =>
        [REPEAT_DETERM o resolve_tac ctxt [allI, impI, in_rel RS iffD2],
         REPEAT_DETERM o eresolve_tac ctxt [exE, conjE], hyp_subst_tac ctxt, rtac ctxt exI,
         rtac ctxt (Drule.rotate_prems 1 conjI),
         rtac ctxt conjI, rtac ctxt map_comp_trans, rtac ctxt sym, rtac ctxt dtor_maps_trans, rtac ctxt map_cong0,
         REPEAT_DETERM_N m o (rtac ctxt o_apply_trans_sym THEN' rtac ctxt @{thm fst_conv}),
         REPEAT_DETERM_N n o rtac ctxt fst_convol_fun_cong_sym,
         rtac ctxt map_comp_trans, rtac ctxt sym, rtac ctxt dtor_maps_trans, rtac ctxt map_cong0,
         EVERY' (maps (fn set_Jset =>
           [rtac ctxt o_apply_trans_sym, rtac ctxt (@{thm snd_conv} RS trans), etac ctxt @{thm CollectE},
           REPEAT_DETERM o etac ctxt conjE, etac ctxt @{thm bspec}, etac ctxt set_Jset]) set_Jsets),
         REPEAT_DETERM_N n o rtac ctxt snd_convol_fun_cong_sym,
         rtac ctxt @{thm CollectI},
         EVERY' (map (fn set_map0 => EVERY' [rtac ctxt conjI, rtac ctxt ord_eq_le_trans, rtac ctxt set_map0,
           rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm CollectI}, rtac ctxt @{thm case_prodI}, rtac ctxt refl])
        (take m set_map0s)),
         CONJ_WRAP' (fn (set_map0, set_Jset_Jsets) =>
           EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt set_map0,
             rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm CollectI}, rtac ctxt @{thm case_prodI}, rtac ctxt exI, rtac ctxt conjI,
             rtac ctxt @{thm CollectI}, etac ctxt @{thm CollectE},
             REPEAT_DETERM o etac ctxt conjE,
             CONJ_WRAP' (fn set_Jset_Jset =>
               EVERY' [rtac ctxt @{thm ballI}, etac ctxt @{thm bspec}, etac ctxt set_Jset_Jset, assume_tac ctxt]) set_Jset_Jsets,
             rtac ctxt (conjI OF [refl, refl])])
           (drop m set_map0s ~~ set_Jset_Jsetss)])
        (map (fn th => th RS trans) map_comps ~~ map (fn th => th RS trans) dtor_maps ~~
          map_cong0s ~~ set_map0ss ~~ set_Jsetss ~~ set_Jset_Jsetsss ~~ in_rels) @
      [rtac ctxt impI,
       CONJ_WRAP' (fn k =>
         EVERY' [rtac ctxt impI, dtac ctxt (mk_conjunctN n k), etac ctxt mp, rtac ctxt exI, rtac ctxt conjI, etac ctxt @{thm CollectI},
           rtac ctxt conjI, rtac ctxt refl, rtac ctxt refl]) ks]) 1
  end

fun mk_dtor_map_unique_tac ctxt unfold_unique sym_map_comps =
  rtac ctxt unfold_unique 1 THEN
  unfold_thms_tac ctxt (sym_map_comps @ @{thms comp_assoc[symmetric] id_comp comp_id}) THEN
  ALLGOALS (etac ctxt sym);

fun mk_col_natural_tac ctxt cts rec_0s rec_Sucs dtor_maps set_map0ss =
  let
    val n = length dtor_maps;
  in
    EVERY' [rtac ctxt (Thm.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac ctxt allI, SELECT_GOAL (unfold_thms_tac ctxt rec_0s),
      CONJ_WRAP' (K (rtac ctxt @{thm image_empty})) rec_0s,
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn (rec_Suc, (dtor_map, set_nats)) => EVERY'
        [SELECT_GOAL (unfold_thms_tac ctxt
          (rec_Suc :: dtor_map :: set_nats @ @{thms image_Un image_UN UN_simps(10)})),
        rtac ctxt Un_cong, rtac ctxt refl,
        CONJ_WRAP_GEN' (rtac ctxt (Thm.permute_prems 0 1 Un_cong))
          (fn i => EVERY' [rtac ctxt @{thm SUP_cong[OF refl]},
            REPEAT_DETERM o etac ctxt allE, etac ctxt (mk_conjunctN n i)]) (n downto 1)])
      (rec_Sucs ~~ (dtor_maps ~~ set_map0ss))] 1
  end;

fun mk_set_map0_tac ctxt col_natural =
  EVERY' (map (rtac ctxt) [@{thm ext}, o_apply RS trans, sym, o_apply RS trans,
    @{thm image_UN} RS trans, refl RS @{thm SUP_cong}, col_natural]) 1;

fun mk_col_bd_tac ctxt m j cts rec_0s rec_Sucs sbd_regularCard sbd_Cinfinite set_sbdss =
  let
    val n = length rec_0s;
  in
    EVERY' [rtac ctxt (Thm.instantiate' [] cts nat_induct),
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn rec_0 => EVERY' (map (rtac ctxt) [@{thm ordIso_ordLess_trans},
        @{thm card_of_ordIso_subst}, rec_0, @{thm Cinfinite_gt_empty}, sbd_Cinfinite])) rec_0s,
      REPEAT_DETERM o rtac ctxt allI,
      CONJ_WRAP' (fn (rec_Suc, set_sbds) => EVERY'
        [rtac ctxt @{thm ordIso_ordLess_trans}, rtac ctxt @{thm card_of_ordIso_subst},
        rtac ctxt rec_Suc, rtac ctxt (sbd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound_strict})),
        rtac ctxt (nth set_sbds (j - 1)),
        REPEAT_DETERM_N (n - 1) o rtac ctxt (sbd_Cinfinite RSN (3, @{thm Un_Cinfinite_bound_strict})),
        EVERY' (map2 (fn i => fn set_sbd => EVERY' [
          rtac ctxt (@{thm card_of_UNION_ordLess_infinite_Field_regularCard} OF [sbd_regularCard,
          sbd_Cinfinite]), rtac ctxt set_sbd, rtac ctxt @{thm ballI}, REPEAT_DETERM o etac ctxt allE,
          etac ctxt (mk_conjunctN n i)]) (1 upto n) (drop m set_sbds))])
      (rec_Sucs ~~ set_sbdss)] 1
  end;

fun mk_set_bd_tac ctxt sbd_Cinfinite sbd_regularCard natLeq_ordLess_bd col_bd =
  EVERY' (map (rtac ctxt) [@{thm card_of_UNION_ordLess_infinite_Field_regularCard} OF [
    sbd_regularCard, sbd_Cinfinite], @{thm ordIso_ordLess_trans}, @{thm card_of_nat},
    natLeq_ordLess_bd, @{thm ballI}, col_bd]) 1;

fun mk_le_rel_OO_tac ctxt coinduct rel_Jrels le_rel_OOs =
  EVERY' (rtac ctxt coinduct :: map2 (fn rel_Jrel => fn le_rel_OO =>
    let val Jrel_imp_rel = rel_Jrel RS iffD1;
    in
      EVERY' [rtac ctxt (le_rel_OO RS @{thm predicate2D}), etac ctxt @{thm relcomppE},
      rtac ctxt @{thm relcomppI}, etac ctxt Jrel_imp_rel, etac ctxt Jrel_imp_rel]
    end)
  rel_Jrels le_rel_OOs) 1;

fun mk_wit_tac ctxt n dtor_ctors dtor_set wit coind_wits =
  ALLGOALS (TRY o (eresolve_tac ctxt coind_wits THEN' rtac ctxt refl)) THEN
  REPEAT_DETERM (assume_tac ctxt 1 ORELSE
    EVERY' [dtac ctxt set_rev_mp, rtac ctxt @{thm equalityD1}, resolve_tac ctxt dtor_set,
    K (unfold_thms_tac ctxt dtor_ctors),
    REPEAT_DETERM_N n o etac ctxt @{thm UnE},
    REPEAT_DETERM o
      (TRY o REPEAT_DETERM o etac ctxt @{thm UnE} THEN' TRY o etac ctxt @{thm UN_E} THEN'
        (eresolve_tac ctxt wit ORELSE'
        (dresolve_tac ctxt wit THEN'
          (etac ctxt FalseE ORELSE'
          EVERY' [hyp_subst_tac ctxt, dtac ctxt set_rev_mp, rtac ctxt @{thm equalityD1}, resolve_tac ctxt dtor_set,
            K (unfold_thms_tac ctxt dtor_ctors), REPEAT_DETERM_N n o etac ctxt @{thm UnE}]))))] 1);

fun mk_coind_wit_tac ctxt induct unfolds set_nats wits =
  rtac ctxt induct 1 THEN ALLGOALS (TRY o rtac ctxt impI THEN' TRY o hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt (unfolds @ set_nats @ @{thms image_id id_apply}) THEN
  ALLGOALS (REPEAT_DETERM o etac ctxt @{thm imageE} THEN' TRY o hyp_subst_tac ctxt) THEN
  ALLGOALS (TRY o
    FIRST' [rtac ctxt TrueI, rtac ctxt refl, etac ctxt (refl RSN (2, mp)), dresolve_tac ctxt wits THEN' etac ctxt FalseE]);

fun mk_dtor_corec_transfer_tac ctxt n m dtor_corec_defs dtor_unfold_transfer pre_T_map_transfers
    dtor_rels =
  CONJ_WRAP (fn (dtor_corec_def, dtor_unfold_transfer) =>
      REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
      unfold_thms_tac ctxt [dtor_corec_def, o_apply] THEN
      HEADGOAL (rtac ctxt (mk_rel_funDN (n + 1) dtor_unfold_transfer) THEN'
        EVERY' (map2 (fn pre_T_map_transfer => fn dtor_rel =>
          etac ctxt (mk_rel_funDN_rotated 2 @{thm case_sum_transfer}) THEN'
          rtac ctxt (mk_rel_funDN 2 @{thm comp_transfer}) THEN'
          rtac ctxt (mk_rel_funDN (m + n) pre_T_map_transfer) THEN'
          REPEAT_DETERM_N m o rtac ctxt @{thm id_transfer} THEN'
          REPEAT_DETERM_N n o rtac ctxt @{thm Inl_transfer} THEN'
          rtac ctxt rel_funI THEN'
          etac ctxt (dtor_rel RS iffD1)) pre_T_map_transfers dtor_rels) THEN'
        etac ctxt (mk_rel_funDN 1 @{thm Inr_transfer})))
    (dtor_corec_defs ~~ dtor_unfold_transfer);

fun mk_dtor_rel_tac ctxt in_Jrels i in_rel map_comp0 map_cong0 dtor_map dtor_sets dtor_inject
    dtor_ctor set_map0s dtor_set_incls dtor_set_set_inclss =
  let
    val m = length dtor_set_incls;
    val n = length dtor_set_set_inclss;
    val (passive_set_map0s, active_set_map0s) = chop m set_map0s;
    val in_Jrel = nth in_Jrels (i - 1);
    val if_tac =
      EVERY' [dtac ctxt (in_Jrel RS iffD1), REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE CollectE},
        rtac ctxt (in_rel RS iffD2), rtac ctxt exI, rtac ctxt conjI, rtac ctxt @{thm CollectI},
        EVERY' (map2 (fn set_map0 => fn set_incl =>
          EVERY' [rtac ctxt conjI, rtac ctxt ord_eq_le_trans, rtac ctxt set_map0,
            rtac ctxt ord_eq_le_trans, rtac ctxt trans_fun_cong_image_id_id_apply,
            etac ctxt (set_incl RS @{thm subset_trans})])
        passive_set_map0s dtor_set_incls),
        CONJ_WRAP' (fn (in_Jrel, (set_map0, dtor_set_set_incls)) =>
          EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt set_map0, rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm CollectI},
            rtac ctxt @{thm case_prodI}, rtac ctxt (in_Jrel RS iffD2), rtac ctxt exI, rtac ctxt conjI, rtac ctxt @{thm CollectI},
            CONJ_WRAP' (fn thm => etac ctxt (thm RS @{thm subset_trans}) THEN' assume_tac ctxt) dtor_set_set_incls,
            rtac ctxt conjI, rtac ctxt refl, rtac ctxt refl])
        (in_Jrels ~~ (active_set_map0s ~~ dtor_set_set_inclss)),
        CONJ_WRAP' (fn conv =>
          EVERY' [rtac ctxt trans, rtac ctxt map_comp0, rtac ctxt trans, rtac ctxt map_cong0,
          REPEAT_DETERM_N m o rtac ctxt @{thm fun_cong[OF comp_id]},
          REPEAT_DETERM_N n o EVERY' (map (rtac ctxt) [trans, o_apply, conv]),
          rtac ctxt trans, rtac ctxt sym, rtac ctxt dtor_map, rtac ctxt (dtor_inject RS iffD2), assume_tac ctxt])
        @{thms fst_conv snd_conv}];
    val only_if_tac =
      EVERY' [dtac ctxt (in_rel RS iffD1), REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE CollectE},
        rtac ctxt (in_Jrel RS iffD2), rtac ctxt exI, rtac ctxt conjI, rtac ctxt @{thm CollectI},
        CONJ_WRAP' (fn (dtor_set, passive_set_map0) =>
          EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt dtor_set, rtac ctxt @{thm Un_least},
            rtac ctxt ord_eq_le_trans, rtac ctxt @{thm box_equals}, rtac ctxt passive_set_map0,
            rtac ctxt (dtor_ctor RS sym RS arg_cong), rtac ctxt trans_fun_cong_image_id_id_apply, assume_tac ctxt,
            CONJ_WRAP_GEN' (rtac ctxt (Thm.permute_prems 0 1 @{thm Un_least}))
              (fn (active_set_map0, in_Jrel) => EVERY' [rtac ctxt ord_eq_le_trans,
                rtac ctxt @{thm SUP_cong[OF _ refl]}, rtac ctxt @{thm box_equals[OF _ _ refl]},
                rtac ctxt active_set_map0, rtac ctxt (dtor_ctor RS sym RS arg_cong), rtac ctxt @{thm UN_least},
                dtac ctxt set_rev_mp, etac ctxt @{thm image_mono}, etac ctxt @{thm imageE},
                dtac ctxt @{thm ssubst_mem[OF prod.collapse]},
                REPEAT_DETERM o eresolve_tac ctxt
                  @{thms CollectE conjE case_prodE iffD1[OF prod.inject, elim_format]},
                hyp_subst_tac ctxt,
                dtac ctxt (in_Jrel RS iffD1),
                dtac ctxt @{thm someI_ex}, REPEAT_DETERM o etac ctxt conjE,
                REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, assume_tac ctxt])
            (rev (active_set_map0s ~~ in_Jrels))])
        (dtor_sets ~~ passive_set_map0s),
        rtac ctxt conjI,
        REPEAT_DETERM_N 2 o EVERY'[rtac ctxt (dtor_inject RS iffD1), rtac ctxt trans, rtac ctxt dtor_map,
          rtac ctxt @{thm box_equals}, rtac ctxt map_comp0, rtac ctxt (dtor_ctor RS sym RS arg_cong), rtac ctxt trans,
          rtac ctxt map_cong0, REPEAT_DETERM_N m o rtac ctxt @{thm fun_cong[OF comp_id]},
          EVERY' (map (fn in_Jrel => EVERY' [rtac ctxt trans, rtac ctxt o_apply, dtac ctxt set_rev_mp, assume_tac ctxt,
            dtac ctxt @{thm ssubst_mem[OF prod.collapse]},
            REPEAT_DETERM o eresolve_tac ctxt
              @{thms CollectE conjE case_prodE iffD1[OF prod.inject, elim_format]},
            hyp_subst_tac ctxt, dtac ctxt (in_Jrel RS iffD1),
            dtac ctxt @{thm someI_ex}, REPEAT_DETERM o etac ctxt conjE, assume_tac ctxt]) in_Jrels),
          assume_tac ctxt]]
  in
    EVERY' [rtac ctxt iffI, if_tac, only_if_tac] 1
  end;

fun mk_rel_coinduct_coind_tac ctxt fst m coinduct ks map_comp0s map_congs map_arg_congs set_map0ss
  dtor_unfolds dtor_maps in_rels =
  let
    val n = length ks;
    val fst_diag_nth = if fst then @{thm fst_diag_fst} else @{thm fst_diag_snd};
    val snd_diag_nth = if fst then @{thm snd_diag_fst} else @{thm snd_diag_snd};
  in
    EVERY' [rtac ctxt coinduct,
      EVERY' (@{map 8} (fn i => fn map_comp0 => fn map_cong => fn map_arg_cong => fn set_map0s =>
          fn dtor_unfold => fn dtor_map => fn in_rel =>
        EVERY' [REPEAT_DETERM o resolve_tac ctxt [allI, impI, in_rel RS iffD2],
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          select_prem_tac ctxt (length ks) (dtac ctxt @{thm spec2}) i, dtac ctxt mp, assume_tac ctxt,
          REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, hyp_subst_tac ctxt,
          rtac ctxt exI, rtac ctxt (Drule.rotate_prems 1 conjI), rtac ctxt conjI,
          rtac ctxt (map_comp0 RS trans), rtac ctxt (dtor_map RS trans RS sym),
          rtac ctxt (dtor_unfold RS map_arg_cong RS trans), rtac ctxt (trans OF [map_comp0, map_cong]),
          REPEAT_DETERM_N m o rtac ctxt (fst_diag_nth RS @{thm fun_cong[OF trans[OF o_id sym]]}),
          REPEAT_DETERM_N n o (rtac ctxt @{thm sym[OF trans[OF o_apply]]} THEN' rtac ctxt @{thm fst_conv}),
          rtac ctxt (map_comp0 RS trans), rtac ctxt (map_cong RS trans),
          REPEAT_DETERM_N m o rtac ctxt (snd_diag_nth RS fun_cong),
          REPEAT_DETERM_N n o (rtac ctxt @{thm trans[OF o_apply]} THEN' rtac ctxt @{thm snd_conv}),
          etac ctxt (@{thm prod.case} RS map_arg_cong RS trans),
          SELECT_GOAL (unfold_thms_tac ctxt @{thms prod.case o_def fst_conv snd_conv}),
          rtac ctxt @{thm CollectI},
          CONJ_WRAP' (fn set_map0 =>
            EVERY' [rtac ctxt (set_map0 RS ord_eq_le_trans),
              rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm CollectI}, rtac ctxt @{thm case_prodI},
              FIRST' [rtac ctxt refl, EVERY'[rtac ctxt exI, rtac ctxt conjI, etac ctxt Collect_splitD_set_mp,
                assume_tac ctxt, rtac ctxt (@{thm surjective_pairing} RS arg_cong)]]])
          set_map0s])
      ks map_comp0s map_congs map_arg_congs set_map0ss dtor_unfolds dtor_maps in_rels)] 1
  end;

val split_id_unfolds = @{thms prod.case image_id id_apply};

fun mk_rel_coinduct_ind_tac ctxt m ks unfolds set_map0ss j set_induct =
  let val n = length ks;
  in
    rtac ctxt set_induct 1 THEN
    EVERY' (@{map 3} (fn unfold => fn set_map0s => fn i =>
      EVERY' [REPEAT_DETERM o resolve_tac ctxt [allI, impI], etac ctxt conjE,
        select_prem_tac ctxt n (dtac ctxt @{thm spec2}) i, dtac ctxt mp, assume_tac ctxt,
        REPEAT_DETERM o eresolve_tac ctxt [@{thm CollectE}, @{thm conjE}, Collect_splitD_set_mp, set_rev_mp],
        hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt ([unfold, nth set_map0s (j - 1)] @ split_id_unfolds)),
        rtac ctxt @{thm subset_refl}])
    unfolds set_map0ss ks) 1 THEN
    EVERY' (@{map 3} (fn unfold => fn set_map0s => fn i =>
      EVERY' (map (fn set_map0 =>
        EVERY' [REPEAT_DETERM o resolve_tac ctxt [allI, impI], etac ctxt conjE,
        select_prem_tac ctxt n (dtac ctxt @{thm spec2}) i, dtac ctxt mp, assume_tac ctxt,
        REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt ([unfold, set_map0] @ split_id_unfolds)),
        etac ctxt @{thm imageE}, hyp_subst_tac ctxt, REPEAT_DETERM o eresolve_tac ctxt [allE, mp],
        rtac ctxt conjI, etac ctxt Collect_splitD_set_mp, assume_tac ctxt,
        rtac ctxt (@{thm surjective_pairing} RS arg_cong)])
      (drop m set_map0s)))
    unfolds set_map0ss ks) 1
  end;

fun mk_rel_coinduct_tac ctxt CIHs in_rels in_Jrels helper_indss helper_coind1s helper_coind2s =
  let val n = length in_rels;
  in
    Method.insert_tac ctxt CIHs 1 THEN
    unfold_thms_tac ctxt (@{thm choice_iff} :: @{thm ex_simps(6)[symmetric]} :: in_rels) THEN
    REPEAT_DETERM (etac ctxt exE 1) THEN
    CONJ_WRAP' (fn (in_Jrel, (helper_inds, (helper_coind1, helper_coind2))) =>
      EVERY' [rtac ctxt @{thm predicate2I}, rtac ctxt (in_Jrel RS iffD2), rtac ctxt exI, rtac ctxt conjI,
        if null helper_inds then rtac ctxt @{thm UNIV_I}
        else rtac ctxt @{thm CollectI} THEN'
          CONJ_WRAP' (fn helper_ind =>
            EVERY' [rtac ctxt (helper_ind RS rev_mp), REPEAT_DETERM_N n o assume_tac ctxt,
              REPEAT_DETERM_N n o etac ctxt thin_rl, rtac ctxt impI,
              REPEAT_DETERM o resolve_tac ctxt @{thms subsetI CollectI iffD2[OF split_beta]},
              dtac ctxt @{thm bspec}, assume_tac ctxt, REPEAT_DETERM o eresolve_tac ctxt [allE, mp, conjE],
              etac ctxt (refl RSN (2, conjI))])
          helper_inds,
        rtac ctxt conjI,
        rtac ctxt (helper_coind1 RS rev_mp), REPEAT_DETERM_N n o assume_tac ctxt,
        REPEAT_DETERM_N n o etac ctxt thin_rl,
        rtac ctxt impI, etac ctxt mp, rtac ctxt exI, etac ctxt (refl RSN (2, conjI)),
        rtac ctxt (helper_coind2 RS rev_mp), REPEAT_DETERM_N n o assume_tac ctxt,
        REPEAT_DETERM_N n o etac ctxt thin_rl,
        rtac ctxt impI, etac ctxt mp, rtac ctxt exI, etac ctxt (refl RSN (2, conjI))])
    (in_Jrels ~~ (helper_indss ~~ (helper_coind1s ~~ helper_coind2s))) 1
  end;

fun mk_unfold_transfer_tac ctxt m ctor_rel_coinduct map_transfers unfolds =
  let
    val n = length map_transfers;
  in
    unfold_thms_tac ctxt
      @{thms rel_fun_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]} THEN
    unfold_thms_tac ctxt @{thms rel_fun_iff_geq_image2p} THEN
    HEADGOAL (EVERY'
      [REPEAT_DETERM o resolve_tac ctxt [allI, impI], rtac ctxt ctor_rel_coinduct,
      EVERY' (map (fn map_transfer => EVERY'
        [REPEAT_DETERM o resolve_tac ctxt [allI, impI], etac ctxt @{thm image2pE}, hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac ctxt unfolds),
        rtac ctxt (funpow (m + n + 1) (fn thm => thm RS rel_funD) map_transfer),
        REPEAT_DETERM_N m o rtac ctxt @{thm id_transfer},
        REPEAT_DETERM_N n o rtac ctxt @{thm rel_fun_image2p},
        etac ctxt @{thm predicate2D}, etac ctxt @{thm image2pI}])
      map_transfers)])
  end;

end;
