(*  Title:      HOL/Tools/BNF/bnf_def_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Author:     Ondrej Kuncar, TU Muenchen
    Copyright   2012, 2013, 2014, 2015

Tactics for definition of bounded natural functors.
*)

signature BNF_DEF_TACTICS =
sig
  val mk_collect_set_map_tac: Proof.context -> thm list -> tactic
  val mk_in_mono_tac: Proof.context -> int -> tactic
  val mk_inj_map_strong_tac: Proof.context -> thm -> thm list -> thm -> tactic
  val mk_inj_map_tac: Proof.context -> int -> thm -> thm -> thm -> thm -> tactic
  val mk_map_id: thm -> thm
  val mk_map_ident: Proof.context -> thm -> thm
  val mk_map_comp: thm -> thm
  val mk_map_cong_tac: Proof.context -> thm -> tactic
  val mk_set_map: thm -> thm

  val mk_rel_Grp_tac: Proof.context -> thm list -> thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_rel_eq_tac: Proof.context -> int -> thm -> thm -> thm -> tactic
  val mk_rel_OO_le_tac: Proof.context -> thm list -> thm -> thm -> thm -> thm list -> tactic
  val mk_rel_conversep_tac: Proof.context -> thm -> thm -> tactic
  val mk_rel_conversep_le_tac: Proof.context -> thm list -> thm -> thm -> thm -> thm list -> tactic
  val mk_rel_map0_tac: Proof.context -> int -> thm -> thm -> thm -> thm -> tactic
  val mk_rel_mono_tac: Proof.context -> thm list -> thm -> tactic
  val mk_rel_mono_strong0_tac: Proof.context -> thm -> thm list -> tactic
  val mk_rel_cong_tac: Proof.context -> thm list * thm list -> thm -> tactic
  val mk_rel_eq_onp_tac: Proof.context -> thm -> thm -> thm -> tactic
  val mk_pred_mono_strong0_tac: Proof.context -> thm -> thm -> tactic
  val mk_pred_mono_tac: Proof.context -> thm -> thm -> tactic

  val mk_map_transfer_tac: Proof.context -> thm -> thm -> thm list -> thm -> thm -> tactic
  val mk_pred_transfer_tac: Proof.context -> int -> thm -> thm -> thm -> tactic
  val mk_rel_transfer_tac: Proof.context -> thm -> thm list -> thm -> tactic
  val mk_set_transfer_tac: Proof.context -> thm -> thm list -> tactic

  val mk_in_bd_tac: Proof.context -> int -> thm -> thm -> thm -> thm -> thm list -> thm list ->
    thm -> thm -> thm -> thm -> tactic

  val mk_trivial_wit_tac: Proof.context -> thm list -> thm list -> tactic
end;

structure BNF_Def_Tactics : BNF_DEF_TACTICS =
struct

open BNF_Util
open BNF_Tactics

val ord_eq_le_trans = @{thm ord_eq_le_trans};
val ord_le_eq_trans = @{thm ord_le_eq_trans};
val conversep_shift = @{thm conversep_le_swap} RS iffD1;

fun mk_map_id id = mk_trans (fun_cong OF [id]) @{thm id_apply};
fun mk_map_ident ctxt = unfold_thms ctxt @{thms id_def};
fun mk_map_comp comp = @{thm comp_eq_dest_lhs} OF [mk_sym comp];
fun mk_map_cong_tac ctxt cong0 =
  (hyp_subst_tac ctxt THEN' rtac ctxt cong0 THEN'
   REPEAT_DETERM o (dtac ctxt meta_spec THEN' etac ctxt meta_mp THEN' assume_tac ctxt)) 1;
fun mk_set_map set_map0 = set_map0 RS @{thm comp_eq_dest};

fun mk_in_mono_tac ctxt n =
  if n = 0 then rtac ctxt subset_UNIV 1
  else
   (rtac ctxt @{thm subsetI} THEN' rtac ctxt @{thm CollectI}) 1 THEN
   REPEAT_DETERM (eresolve_tac ctxt @{thms CollectE conjE} 1) THEN
   REPEAT_DETERM_N (n - 1)
     ((rtac ctxt conjI THEN' etac ctxt @{thm subset_trans} THEN' assume_tac ctxt) 1) THEN
   (etac ctxt @{thm subset_trans} THEN' assume_tac ctxt) 1;

fun mk_inj_map_tac ctxt n map_id map_comp map_cong0 map_cong =
  let
    val map_cong' = map_cong OF (asm_rl :: replicate n refl);
    val map_cong0' = map_cong0 OF (replicate n @{thm the_inv_f_o_f_id});
  in
    HEADGOAL (rtac ctxt @{thm injI} THEN' etac ctxt (map_cong' RS box_equals) THEN'
      REPEAT_DETERM_N 2 o (rtac ctxt (box_equals OF [map_cong0', map_comp RS sym, map_id]) THEN'
        REPEAT_DETERM_N n o assume_tac ctxt))
  end;

fun mk_inj_map_strong_tac ctxt rel_eq rel_maps rel_mono_strong =
  let
    val rel_eq' = rel_eq RS @{thm predicate2_eqD};
    val rel_maps' = map (fn thm => thm RS iffD1) rel_maps;
  in
    HEADGOAL (dtac ctxt (rel_eq' RS iffD2) THEN' rtac ctxt (rel_eq' RS iffD1)) THEN
    EVERY (map (HEADGOAL o dtac ctxt) rel_maps') THEN
    HEADGOAL (etac ctxt rel_mono_strong) THEN
    TRYALL (Goal.assume_rule_tac ctxt)
  end;

fun mk_collect_set_map_tac ctxt set_map0s =
  (rtac ctxt (@{thm collect_comp} RS trans) THEN' rtac ctxt @{thm arg_cong[of _ _ collect]} THEN'
  EVERY' (map (fn set_map0 =>
    rtac ctxt (mk_trans @{thm image_insert} @{thm arg_cong2[of _ _ _ _ insert]}) THEN'
    rtac ctxt set_map0) set_map0s) THEN'
  rtac ctxt @{thm image_empty}) 1;

fun mk_rel_Grp_tac ctxt rel_OO_Grps map_id0 map_cong0 map_id map_comp set_maps =
  let
    val n = length set_maps;
    val rel_OO_Grps_tac =
      if null rel_OO_Grps then K all_tac else rtac ctxt (hd rel_OO_Grps RS trans);
  in
    if null set_maps then
      unfold_thms_tac ctxt ((map_id0 RS @{thm Grp_UNIV_id}) :: rel_OO_Grps) THEN
      resolve_tac ctxt @{thms refl Grp_UNIV_idI[OF refl]} 1
    else
      EVERY' [rel_OO_Grps_tac, rtac ctxt @{thm antisym}, rtac ctxt @{thm predicate2I},
        REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE GrpE relcomppE conversepE},
        hyp_subst_tac ctxt, rtac ctxt @{thm GrpI}, rtac ctxt trans, rtac ctxt map_comp,
          rtac ctxt map_cong0,
        REPEAT_DETERM_N n o EVERY' [rtac ctxt @{thm Collect_case_prod_Grp_eqD},
          etac ctxt @{thm set_mp}, assume_tac ctxt],
        rtac ctxt @{thm CollectI},
        CONJ_WRAP' (fn thm => EVERY' [rtac ctxt (thm RS ord_eq_le_trans),
          rtac ctxt @{thm image_subsetI}, rtac ctxt @{thm Collect_case_prod_Grp_in},
          etac ctxt @{thm set_mp}, assume_tac ctxt])
        set_maps,
        rtac ctxt @{thm predicate2I}, REPEAT_DETERM o eresolve_tac ctxt [@{thm GrpE}, exE, conjE],
        hyp_subst_tac ctxt,
        rtac ctxt @{thm relcomppI}, rtac ctxt @{thm conversepI},
        EVERY' (map2 (fn convol => fn map_id0 =>
          EVERY' [rtac ctxt @{thm GrpI},
            rtac ctxt (@{thm box_equals} OF [map_cong0, map_comp RS sym, map_id0]),
            REPEAT_DETERM_N n o rtac ctxt (convol RS fun_cong),
            REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE},
            rtac ctxt @{thm CollectI},
            CONJ_WRAP' (fn thm =>
              EVERY' [rtac ctxt ord_eq_le_trans, rtac ctxt thm, rtac ctxt @{thm image_subsetI},
                rtac ctxt @{thm convol_mem_GrpI}, etac ctxt set_mp, assume_tac ctxt])
            set_maps])
          @{thms fst_convol snd_convol} [map_id, refl])] 1
  end;

fun mk_rel_eq_tac ctxt n rel_Grp rel_cong map_id0 =
  (EVERY' (rtac ctxt (rel_cong RS trans) :: replicate n (rtac ctxt @{thm eq_alt})) THEN'
  rtac ctxt (rel_Grp RSN (2, @{thm box_equals[OF _ sym sym[OF eq_alt]]})) THEN'
  (if n = 0 then SELECT_GOAL (unfold_thms_tac ctxt (no_refl [map_id0])) THEN' rtac ctxt refl
  else EVERY' [rtac ctxt @{thm arg_cong2[of _ _ _ _ "Grp"]},
    rtac ctxt @{thm equalityI}, rtac ctxt subset_UNIV,
    rtac ctxt @{thm subsetI}, rtac ctxt @{thm CollectI},
    CONJ_WRAP' (K (rtac ctxt subset_UNIV)) (1 upto n), rtac ctxt map_id0])) 1;

fun mk_rel_map0_tac ctxt live rel_compp rel_conversep rel_Grp map_id =
  if live = 0 then
    HEADGOAL (Goal.conjunction_tac) THEN
    unfold_thms_tac ctxt @{thms id_apply} THEN
    ALLGOALS (rtac ctxt refl)
  else
    let
      val ks = 1 upto live;
    in
      Goal.conjunction_tac 1 THEN
      unfold_thms_tac ctxt [rel_compp, rel_conversep, rel_Grp, @{thm vimage2p_Grp}] THEN
      TRYALL (EVERY' [rtac ctxt iffI, rtac ctxt @{thm relcomppI}, rtac ctxt @{thm GrpI},
        resolve_tac ctxt [map_id, refl], rtac ctxt @{thm CollectI},
        CONJ_WRAP' (K (rtac ctxt @{thm subset_UNIV})) ks, rtac ctxt @{thm relcomppI},
        assume_tac ctxt, rtac ctxt @{thm conversepI}, rtac ctxt @{thm GrpI},
        resolve_tac ctxt [map_id, refl], rtac ctxt @{thm CollectI},
        CONJ_WRAP' (K (rtac ctxt @{thm subset_UNIV})) ks,
        REPEAT_DETERM o eresolve_tac ctxt @{thms relcomppE conversepE GrpE},
        dtac ctxt (trans OF [sym, map_id]), hyp_subst_tac ctxt, assume_tac ctxt])
    end;

fun mk_rel_mono_tac ctxt rel_OO_Grps in_mono =
  let
    val rel_OO_Grps_tac = if null rel_OO_Grps then K all_tac
      else rtac ctxt (hd rel_OO_Grps RS ord_eq_le_trans) THEN'
        rtac ctxt (hd rel_OO_Grps RS sym RSN (2, ord_le_eq_trans));
  in
    EVERY' [rel_OO_Grps_tac, rtac ctxt @{thm relcompp_mono}, rtac ctxt @{thm iffD2[OF conversep_mono]},
      rtac ctxt @{thm Grp_mono}, rtac ctxt in_mono, REPEAT_DETERM o etac ctxt @{thm Collect_case_prod_mono},
      rtac ctxt @{thm Grp_mono}, rtac ctxt in_mono, REPEAT_DETERM o etac ctxt @{thm Collect_case_prod_mono}] 1
  end;

fun mk_rel_conversep_le_tac ctxt rel_OO_Grps rel_eq map_cong0 map_comp set_maps =
  let
    val n = length set_maps;
    val rel_OO_Grps_tac = if null rel_OO_Grps then K all_tac
      else rtac ctxt (hd rel_OO_Grps RS ord_eq_le_trans) THEN'
        rtac ctxt (hd rel_OO_Grps RS sym RS @{thm arg_cong[of _ _ conversep]} RSN (2, ord_le_eq_trans));
  in
    if null set_maps then rtac ctxt (rel_eq RS @{thm leq_conversepI}) 1
    else
      EVERY' [rel_OO_Grps_tac, rtac ctxt @{thm predicate2I},
        REPEAT_DETERM o
          eresolve_tac ctxt @{thms CollectE exE conjE GrpE relcomppE conversepE},
        hyp_subst_tac ctxt, rtac ctxt @{thm conversepI}, rtac ctxt @{thm relcomppI}, rtac ctxt @{thm conversepI},
        EVERY' (map (fn thm => EVERY' [rtac ctxt @{thm GrpI}, rtac ctxt sym, rtac ctxt trans,
          rtac ctxt map_cong0, REPEAT_DETERM_N n o rtac ctxt thm,
          rtac ctxt (map_comp RS sym), rtac ctxt @{thm CollectI},
          CONJ_WRAP' (fn thm => EVERY' [rtac ctxt (thm RS ord_eq_le_trans),
            etac ctxt @{thm flip_pred}]) set_maps]) [@{thm snd_fst_flip}, @{thm fst_snd_flip}])] 1
  end;

fun mk_rel_conversep_tac ctxt le_conversep rel_mono =
  EVERY' [rtac ctxt @{thm antisym}, rtac ctxt le_conversep, rtac ctxt @{thm xt1(6)}, rtac ctxt conversep_shift,
    rtac ctxt le_conversep, rtac ctxt @{thm iffD2[OF conversep_mono]}, rtac ctxt rel_mono,
    REPEAT_DETERM o rtac ctxt @{thm eq_refl[OF sym[OF conversep_conversep]]}] 1;

fun mk_rel_OO_le_tac ctxt rel_OO_Grps rel_eq map_cong0 map_comp set_maps =
  let
    val n = length set_maps;
    fun in_tac nthO_in = rtac ctxt @{thm CollectI} THEN'
        CONJ_WRAP' (fn thm => EVERY' [rtac ctxt (thm RS ord_eq_le_trans),
          rtac ctxt @{thm image_subsetI}, rtac ctxt nthO_in, etac ctxt set_mp, assume_tac ctxt]) set_maps;
    val rel_OO_Grps_tac = if null rel_OO_Grps then K all_tac
      else rtac ctxt (hd rel_OO_Grps RS ord_eq_le_trans) THEN'
        rtac ctxt (@{thm arg_cong2[of _ _ _ _ "(OO)"]} OF (replicate 2 (hd rel_OO_Grps RS sym)) RSN
          (2, ord_le_eq_trans));
  in
    if null set_maps then rtac ctxt (rel_eq RS @{thm leq_OOI}) 1
    else
      EVERY' [rel_OO_Grps_tac, rtac ctxt @{thm predicate2I},
        REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE exE conjE GrpE relcomppE conversepE},
        hyp_subst_tac ctxt,
        rtac ctxt @{thm relcomppI}, rtac ctxt @{thm relcomppI}, rtac ctxt @{thm conversepI}, rtac ctxt @{thm GrpI},
        rtac ctxt trans, rtac ctxt map_comp, rtac ctxt sym, rtac ctxt map_cong0,
        REPEAT_DETERM_N n o rtac ctxt @{thm fst_fstOp},
        in_tac @{thm fstOp_in},
        rtac ctxt @{thm GrpI}, rtac ctxt trans, rtac ctxt map_comp, rtac ctxt map_cong0,
        REPEAT_DETERM_N n o EVERY' [rtac ctxt trans, rtac ctxt o_apply,
          rtac ctxt @{thm ballE}, rtac ctxt subst,
          rtac ctxt @{thm csquare_def}, rtac ctxt @{thm csquare_fstOp_sndOp}, assume_tac ctxt,
          etac ctxt notE, etac ctxt set_mp, assume_tac ctxt],
        in_tac @{thm fstOp_in},
        rtac ctxt @{thm relcomppI}, rtac ctxt @{thm conversepI}, rtac ctxt @{thm GrpI},
        rtac ctxt trans, rtac ctxt map_comp, rtac ctxt map_cong0,
        REPEAT_DETERM_N n o rtac ctxt o_apply,
        in_tac @{thm sndOp_in},
        rtac ctxt @{thm GrpI}, rtac ctxt trans, rtac ctxt map_comp, rtac ctxt sym, rtac ctxt map_cong0,
        REPEAT_DETERM_N n o rtac ctxt @{thm snd_sndOp},
        in_tac @{thm sndOp_in}] 1
  end;

fun mk_rel_mono_strong0_tac ctxt in_rel set_maps =
  if null set_maps then assume_tac ctxt 1
  else
    unfold_tac ctxt [in_rel] THEN
    REPEAT_DETERM (eresolve_tac ctxt @{thms exE CollectE conjE} 1) THEN
    hyp_subst_tac ctxt 1 THEN
    EVERY' [rtac ctxt exI, rtac ctxt @{thm conjI[OF CollectI conjI[OF refl refl]]},
      CONJ_WRAP' (fn thm =>
        (etac ctxt (@{thm Collect_split_mono_strong} OF [thm, thm]) THEN' assume_tac ctxt))
      set_maps] 1;

fun mk_rel_transfer_tac ctxt in_rel rel_map rel_mono_strong =
  let
    fun last_tac iffD =
      HEADGOAL (etac ctxt rel_mono_strong) THEN
      REPEAT_DETERM (HEADGOAL (etac ctxt (@{thm predicate2_transferD} RS iffD) THEN'
        REPEAT_DETERM o assume_tac ctxt));
  in
    REPEAT_DETERM (HEADGOAL (rtac ctxt rel_funI)) THEN
    (HEADGOAL (hyp_subst_tac ctxt THEN' rtac ctxt refl) ORELSE
     REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt (Tactic.make_elim (in_rel RS iffD1) ::
       @{thms exE conjE CollectE}))) THEN
     HEADGOAL (hyp_subst_tac ctxt) THEN
     REPEAT_DETERM (HEADGOAL (resolve_tac ctxt (maps (fn thm =>
       [thm RS trans, thm RS @{thm trans[rotated, OF sym]}]) rel_map))) THEN
     HEADGOAL (rtac ctxt iffI) THEN
     last_tac iffD1 THEN last_tac iffD2)
  end;

fun mk_map_transfer_tac ctxt rel_mono in_rel set_maps map_cong0 map_comp =
  let
    val n = length set_maps;
    val in_tac =
      if n = 0 then rtac ctxt @{thm UNIV_I}
      else
        rtac ctxt @{thm CollectI} THEN' CONJ_WRAP' (fn thm =>
          etac ctxt (thm RS
            @{thm ord_eq_le_trans[OF _ subset_trans[OF image_mono convol_image_vimage2p]]}))
        set_maps;
  in
    REPEAT_DETERM_N n (HEADGOAL (rtac ctxt rel_funI)) THEN
    unfold_thms_tac ctxt @{thms rel_fun_iff_leq_vimage2p} THEN
    HEADGOAL (EVERY' [rtac ctxt @{thm order_trans}, rtac ctxt rel_mono,
      REPEAT_DETERM_N n o assume_tac ctxt,
      rtac ctxt @{thm predicate2I}, dtac ctxt (in_rel RS iffD1),
      REPEAT_DETERM o eresolve_tac ctxt @{thms exE CollectE conjE}, hyp_subst_tac ctxt,
      rtac ctxt @{thm vimage2pI}, rtac ctxt (in_rel RS iffD2), rtac ctxt exI, rtac ctxt conjI, in_tac,
      rtac ctxt conjI,
      EVERY' (map (fn convol =>
        rtac ctxt (@{thm box_equals} OF [map_cong0, map_comp RS sym, map_comp RS sym]) THEN'
        REPEAT_DETERM_N n o rtac ctxt (convol RS fun_cong)) @{thms fst_convol snd_convol})])
  end;

fun mk_in_bd_tac ctxt live surj_imp_ordLeq_inst map_comp map_id map_cong0 set_maps set_bds
  bd_card_order bd_Card_order bd_Cinfinite bd_Cnotzero =
  if live = 0 then
    rtac ctxt @{thm ordLeq_transitive[OF ordLeq_csum2[OF card_of_Card_order]
      ordLeq_cexp2[OF ordLeq_refl[OF Card_order_ctwo] Card_order_csum]]} 1
  else
    let
      val bd'_Cinfinite = bd_Cinfinite RS @{thm Cinfinite_csum1};
      val inserts =
        map (fn set_bd =>
          iffD2 OF [@{thm card_of_ordLeq}, @{thm ordLeq_ordIso_trans} OF
            [set_bd, bd_Card_order RS @{thm card_of_Field_ordIso} RS @{thm ordIso_symmetric}]])
        set_bds;
    in
      EVERY' [rtac ctxt (Drule.rotate_prems 1 ctrans), rtac ctxt @{thm cprod_cinfinite_bound},
        rtac ctxt (ctrans OF @{thms ordLeq_csum2 ordLeq_cexp2}), rtac ctxt @{thm card_of_Card_order},
        rtac ctxt @{thm ordLeq_csum2}, rtac ctxt @{thm Card_order_ctwo}, rtac ctxt @{thm Card_order_csum},
        rtac ctxt @{thm ordIso_ordLeq_trans}, rtac ctxt @{thm cexp_cong1},
        if live = 1 then rtac ctxt @{thm ordIso_refl[OF Card_order_csum]}
        else
          REPEAT_DETERM_N (live - 2) o rtac ctxt @{thm ordIso_transitive[OF csum_cong2]} THEN'
          REPEAT_DETERM_N (live - 1) o rtac ctxt @{thm csum_csum},
        rtac ctxt bd_Card_order, rtac ctxt (@{thm cexp_mono2_Cnotzero} RS ctrans), rtac ctxt @{thm ordLeq_csum1},
        rtac ctxt bd_Card_order, rtac ctxt @{thm Card_order_csum}, rtac ctxt bd_Cnotzero,
        rtac ctxt @{thm csum_Cfinite_cexp_Cinfinite},
        rtac ctxt (if live = 1 then @{thm card_of_Card_order} else @{thm Card_order_csum}),
        CONJ_WRAP_GEN' (rtac ctxt @{thm Cfinite_csum}) (K (rtac ctxt @{thm Cfinite_cone})) set_maps,
        rtac ctxt bd'_Cinfinite, rtac ctxt @{thm card_of_Card_order},
        rtac ctxt @{thm Card_order_cexp}, rtac ctxt @{thm Cinfinite_cexp}, rtac ctxt @{thm ordLeq_csum2},
        rtac ctxt @{thm Card_order_ctwo}, rtac ctxt bd'_Cinfinite,
        rtac ctxt (Drule.rotate_prems 1 (@{thm cprod_mono2} RSN (2, ctrans))),
        REPEAT_DETERM_N (live - 1) o
          (rtac ctxt (bd_Cinfinite RS @{thm cprod_cexp_csum_cexp_Cinfinite} RSN (2, ctrans)) THEN'
           rtac ctxt @{thm ordLeq_ordIso_trans[OF cprod_mono2 ordIso_symmetric[OF cprod_cexp]]}),
        rtac ctxt @{thm ordLeq_refl[OF Card_order_cexp]}] 1 THEN
      unfold_thms_tac ctxt [bd_card_order RS @{thm card_order_csum_cone_cexp_def}] THEN
      unfold_thms_tac ctxt @{thms cprod_def Field_card_of} THEN
      EVERY' [rtac ctxt (Drule.rotate_prems 1 ctrans), rtac ctxt surj_imp_ordLeq_inst,
        rtac ctxt @{thm subsetI},
        Method.insert_tac ctxt inserts, REPEAT_DETERM o dtac ctxt meta_spec,
        REPEAT_DETERM o eresolve_tac ctxt [exE, Tactic.make_elim conjunct1],
        etac ctxt @{thm CollectE},
        if live = 1 then K all_tac
        else REPEAT_DETERM_N (live - 2) o (etac ctxt conjE THEN' rotate_tac ~1) THEN' etac ctxt conjE,
        rtac ctxt (Drule.rotate_prems 1 @{thm image_eqI}), rtac ctxt @{thm SigmaI}, rtac ctxt @{thm UNIV_I},
        CONJ_WRAP_GEN' (rtac ctxt @{thm SigmaI})
          (K (etac ctxt @{thm If_the_inv_into_in_Func} THEN' assume_tac ctxt)) set_maps,
        rtac ctxt sym,
        rtac ctxt (Drule.rotate_prems 1
           ((@{thm box_equals} OF [map_cong0 OF replicate live @{thm If_the_inv_into_f_f},
             map_comp RS sym, map_id]) RSN (2, trans))),
        REPEAT_DETERM_N (2 * live) o assume_tac ctxt,
        REPEAT_DETERM_N live o rtac ctxt (@{thm prod.case} RS trans),
        rtac ctxt refl,
        rtac ctxt @{thm surj_imp_ordLeq},
        rtac ctxt @{thm subsetI},
        rtac ctxt (Drule.rotate_prems 1 @{thm image_eqI}),
        REPEAT_DETERM o eresolve_tac ctxt @{thms CollectE conjE}, rtac ctxt @{thm CollectI},
        CONJ_WRAP' (fn thm =>
          rtac ctxt (thm RS ord_eq_le_trans) THEN' etac ctxt @{thm subset_trans[OF image_mono Un_upper1]})
        set_maps,
        rtac ctxt sym,
        rtac ctxt (@{thm box_equals} OF [map_cong0 OF replicate live @{thm fun_cong[OF case_sum_o_inj(1)]},
           map_comp RS sym, map_id])] 1
  end;

fun mk_trivial_wit_tac ctxt wit_defs set_maps =
  unfold_thms_tac ctxt wit_defs THEN
  HEADGOAL (EVERY' (map (fn thm =>
    dtac ctxt (thm RS @{thm equalityD1} RS set_mp) THEN'
    etac ctxt @{thm imageE} THEN' assume_tac ctxt) set_maps)) THEN
  ALLGOALS (assume_tac ctxt);

fun mk_set_transfer_tac ctxt in_rel set_maps =
  Goal.conjunction_tac 1 THEN
  EVERY (map (fn set_map => HEADGOAL (rtac ctxt rel_funI) THEN
  REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt (Tactic.make_elim (in_rel RS iffD1) ::
    @{thms exE conjE CollectE}))) THEN
  HEADGOAL (hyp_subst_tac ctxt THEN' rtac ctxt (@{thm iffD2[OF arg_cong2]} OF [set_map, set_map]) THEN'
    rtac ctxt @{thm rel_setI}) THEN
  REPEAT (HEADGOAL (etac ctxt @{thm imageE} THEN' dtac ctxt @{thm set_mp} THEN' assume_tac ctxt THEN'
    REPEAT_DETERM o (eresolve_tac ctxt @{thms CollectE case_prodE}) THEN' hyp_subst_tac ctxt THEN'
    rtac ctxt @{thm bexI} THEN' etac ctxt @{thm subst_Pair[OF _ refl]} THEN' etac ctxt @{thm imageI})))
    set_maps);

fun mk_rel_cong_tac ctxt (eqs, prems) mono =
  let
    fun mk_tac thm = etac ctxt thm THEN_ALL_NEW assume_tac ctxt;
    fun mk_tacs iffD = etac ctxt mono ::
      map (fn thm => (unfold_thms ctxt @{thms simp_implies_def} thm RS iffD)
        |> Drule.rotate_prems ~1 |> mk_tac) prems;
  in
    unfold_thms_tac ctxt eqs THEN
    HEADGOAL (EVERY' (rtac ctxt iffI :: mk_tacs iffD1 @ mk_tacs iffD2))
  end;

fun subst_conv ctxt thm =
  (Conv.arg_conv o Conv.arg_conv)
   (Conv.top_sweep_rewrs_conv [safe_mk_meta_eq thm] ctxt);

fun mk_rel_eq_onp_tac ctxt pred_def map_id0 rel_Grp =
  HEADGOAL (EVERY'
   [SELECT_GOAL (unfold_thms_tac ctxt (pred_def :: @{thms UNIV_def eq_onp_Grp Ball_Collect})),
   CONVERSION (subst_conv ctxt (map_id0 RS sym)),
   rtac ctxt (unfold_thms ctxt @{thms UNIV_def} rel_Grp)]);

fun mk_pred_mono_strong0_tac ctxt pred_rel rel_mono_strong0 =
   unfold_thms_tac ctxt [pred_rel] THEN
   HEADGOAL (etac ctxt rel_mono_strong0 THEN_ALL_NEW etac ctxt @{thm eq_onp_mono0});

fun mk_pred_mono_tac ctxt rel_eq_onp rel_mono =
  unfold_thms_tac ctxt (map mk_sym [@{thm eq_onp_mono_iff}, rel_eq_onp]) THEN
  HEADGOAL (rtac ctxt rel_mono THEN_ALL_NEW assume_tac ctxt);

fun mk_pred_transfer_tac ctxt n in_rel pred_map pred_cong =
  HEADGOAL (EVERY' [REPEAT_DETERM_N (n + 1) o rtac ctxt rel_funI, dtac ctxt (in_rel RS iffD1),
    REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE CollectE}, hyp_subst_tac ctxt,
    rtac ctxt (box_equals OF [@{thm _}, pred_map RS sym, pred_map RS sym]),
    rtac ctxt (refl RS pred_cong), REPEAT_DETERM_N n o
      (etac ctxt @{thm rel_fun_Collect_case_prodD[where B="(=)"]} THEN_ALL_NEW assume_tac ctxt)]);

end;
