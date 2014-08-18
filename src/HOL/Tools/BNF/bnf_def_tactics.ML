(*  Title:      HOL/Tools/BNF/bnf_def_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2012, 2013, 2014

Tactics for definition of bounded natural functors.
*)

signature BNF_DEF_TACTICS =
sig
  val mk_collect_set_map_tac: thm list -> tactic
  val mk_in_mono_tac: int -> tactic
  val mk_inj_map_strong_tac: Proof.context -> thm -> thm list -> thm -> tactic
  val mk_inj_map_tac: int -> thm -> thm -> thm -> thm -> tactic
  val mk_map_id: thm -> thm
  val mk_map_ident: Proof.context -> thm -> thm
  val mk_map_comp: thm -> thm
  val mk_map_cong_tac: Proof.context -> thm -> tactic
  val mk_set_map: thm -> thm

  val mk_rel_Grp_tac: Proof.context -> thm list -> thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_rel_eq_tac: int -> thm -> thm -> thm -> tactic
  val mk_rel_OO_le_tac: Proof.context -> thm list -> thm -> thm -> thm -> thm list -> tactic
  val mk_rel_conversep_tac: thm -> thm -> tactic
  val mk_rel_conversep_le_tac: Proof.context -> thm list -> thm -> thm -> thm -> thm list -> tactic
  val mk_rel_map0_tac: Proof.context -> int -> thm -> thm -> thm -> thm -> tactic
  val mk_rel_mono_tac: thm list -> thm -> tactic
  val mk_rel_mono_strong0_tac: Proof.context -> thm -> thm list -> tactic

  val mk_map_transfer_tac: Proof.context -> thm -> thm -> thm list -> thm -> thm -> tactic

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
  (hyp_subst_tac ctxt THEN' rtac cong0 THEN'
   REPEAT_DETERM o (dtac meta_spec THEN' etac meta_mp THEN' atac)) 1;
fun mk_set_map set_map0 = set_map0 RS @{thm comp_eq_dest};
fun mk_in_mono_tac n = if n = 0 then rtac subset_UNIV 1
  else (rtac subsetI THEN'
  rtac CollectI) 1 THEN
  REPEAT_DETERM (eresolve_tac [CollectE, conjE] 1) THEN
  REPEAT_DETERM_N (n - 1)
    ((rtac conjI THEN' etac subset_trans THEN' atac) 1) THEN
  (etac subset_trans THEN' atac) 1;

fun mk_inj_map_tac n map_id map_comp map_cong0 map_cong =
  let
    val map_cong' = map_cong OF (asm_rl :: replicate n refl);
    val map_cong0' = map_cong0 OF (replicate n @{thm the_inv_f_o_f_id});
  in
    HEADGOAL (rtac @{thm injI} THEN' etac (map_cong' RS box_equals) THEN'
      REPEAT_DETERM_N 2 o (rtac (box_equals OF [map_cong0', map_comp RS sym, map_id]) THEN'
        REPEAT_DETERM_N n o atac))
  end;

fun mk_inj_map_strong_tac ctxt rel_eq rel_maps rel_mono_strong =
  let
    val rel_eq' = rel_eq RS @{thm predicate2_eqD};
    val rel_maps' = map (fn thm => thm RS iffD1) rel_maps;
  in
    HEADGOAL (dtac (rel_eq' RS iffD2) THEN' rtac (rel_eq' RS iffD1)) THEN
    EVERY (map (HEADGOAL o dtac) rel_maps') THEN
    HEADGOAL (etac rel_mono_strong) THEN
    TRYALL (Goal.assume_rule_tac ctxt)
  end;

fun mk_collect_set_map_tac set_map0s =
  (rtac (@{thm collect_comp} RS trans) THEN' rtac @{thm arg_cong[of _ _ collect]} THEN'
  EVERY' (map (fn set_map0 =>
    rtac (mk_trans @{thm image_insert} @{thm arg_cong2[of _ _ _ _ insert]}) THEN'
    rtac set_map0) set_map0s) THEN'
  rtac @{thm image_empty}) 1;

fun mk_rel_Grp_tac ctxt rel_OO_Grps map_id0 map_cong0 map_id map_comp set_maps =
  let
    val n = length set_maps;
    val rel_OO_Grps_tac = if null rel_OO_Grps then K all_tac else rtac (hd rel_OO_Grps RS trans);
  in
    if null set_maps then
      unfold_thms_tac ctxt ((map_id0 RS @{thm Grp_UNIV_id}) :: rel_OO_Grps) THEN
      rtac @{thm Grp_UNIV_idI[OF refl]} 1
    else
      EVERY' [rel_OO_Grps_tac, rtac @{thm antisym}, rtac @{thm predicate2I},
        REPEAT_DETERM o
          eresolve_tac [CollectE, exE, conjE, @{thm GrpE}, @{thm relcomppE}, @{thm conversepE}],
        hyp_subst_tac ctxt, rtac @{thm GrpI}, rtac trans, rtac map_comp, rtac map_cong0,
        REPEAT_DETERM_N n o EVERY' [rtac @{thm Collect_split_Grp_eqD}, etac @{thm set_mp}, atac],
        rtac CollectI,
        CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS ord_eq_le_trans),
          rtac @{thm image_subsetI}, rtac @{thm Collect_split_Grp_inD}, etac @{thm set_mp}, atac])
        set_maps,
        rtac @{thm predicate2I}, REPEAT_DETERM o eresolve_tac [@{thm GrpE}, exE, conjE],
        hyp_subst_tac ctxt,
        rtac @{thm relcomppI}, rtac @{thm conversepI},
        EVERY' (map2 (fn convol => fn map_id0 =>
          EVERY' [rtac @{thm GrpI},
            rtac (@{thm box_equals} OF [map_cong0, map_comp RS sym, map_id0]),
            REPEAT_DETERM_N n o rtac (convol RS fun_cong),
            REPEAT_DETERM o eresolve_tac [CollectE, conjE],
            rtac CollectI,
            CONJ_WRAP' (fn thm =>
              EVERY' [rtac ord_eq_le_trans, rtac thm, rtac @{thm image_subsetI},
                rtac @{thm convol_mem_GrpI}, etac set_mp, atac])
            set_maps])
          @{thms fst_convol snd_convol} [map_id, refl])] 1
  end;

fun mk_rel_eq_tac n rel_Grp rel_cong map_id0 =
  (EVERY' (rtac (rel_cong RS trans) :: replicate n (rtac @{thm eq_alt})) THEN'
  rtac (rel_Grp RSN (2, @{thm box_equals[OF _ sym sym[OF eq_alt]]})) THEN'
  (if n = 0 then rtac refl
  else EVERY' [rtac @{thm arg_cong2[of _ _ _ _ "Grp"]},
    rtac @{thm equalityI}, rtac subset_UNIV, rtac subsetI, rtac CollectI,
    CONJ_WRAP' (K (rtac subset_UNIV)) (1 upto n), rtac map_id0])) 1;

fun mk_rel_map0_tac ctxt live rel_compp rel_conversep rel_Grp map_id =
  if live = 0 then
    HEADGOAL (Goal.conjunction_tac) THEN
    unfold_thms_tac ctxt @{thms id_apply} THEN
    ALLGOALS (rtac refl)
  else
    let
      val ks = 1 upto live;
    in
      Goal.conjunction_tac 1 THEN
      unfold_thms_tac ctxt [rel_compp, rel_conversep, rel_Grp, @{thm vimage2p_Grp}] THEN
      TRYALL (EVERY' [rtac iffI, rtac @{thm relcomppI}, rtac @{thm GrpI},
        resolve_tac [map_id, refl], rtac CollectI,
        CONJ_WRAP' (K (rtac @{thm subset_UNIV})) ks, rtac @{thm relcomppI}, atac,
        rtac @{thm conversepI}, rtac @{thm GrpI}, resolve_tac [map_id, refl], rtac CollectI,
        CONJ_WRAP' (K (rtac @{thm subset_UNIV})) ks,
        REPEAT_DETERM o eresolve_tac @{thms relcomppE conversepE GrpE},
        dtac (trans OF [sym, map_id]), hyp_subst_tac ctxt, atac])
    end;

fun mk_rel_mono_tac rel_OO_Grps in_mono =
  let
    val rel_OO_Grps_tac = if null rel_OO_Grps then K all_tac
      else rtac (hd rel_OO_Grps RS ord_eq_le_trans) THEN'
        rtac (hd rel_OO_Grps RS sym RSN (2, ord_le_eq_trans));
  in
    EVERY' [rel_OO_Grps_tac, rtac @{thm relcompp_mono}, rtac @{thm iffD2[OF conversep_mono]},
      rtac @{thm Grp_mono}, rtac in_mono, REPEAT_DETERM o etac @{thm Collect_split_mono},
      rtac @{thm Grp_mono}, rtac in_mono, REPEAT_DETERM o etac @{thm Collect_split_mono}] 1
  end;

fun mk_rel_conversep_le_tac ctxt rel_OO_Grps rel_eq map_cong0 map_comp set_maps =
  let
    val n = length set_maps;
    val rel_OO_Grps_tac = if null rel_OO_Grps then K all_tac
      else rtac (hd rel_OO_Grps RS ord_eq_le_trans) THEN'
        rtac (hd rel_OO_Grps RS sym RS @{thm arg_cong[of _ _ conversep]} RSN (2, ord_le_eq_trans));
  in
    if null set_maps then rtac (rel_eq RS @{thm leq_conversepI}) 1
    else
      EVERY' [rel_OO_Grps_tac, rtac @{thm predicate2I},
        REPEAT_DETERM o
          eresolve_tac [CollectE, exE, conjE, @{thm GrpE}, @{thm relcomppE}, @{thm conversepE}],
        hyp_subst_tac ctxt, rtac @{thm conversepI}, rtac @{thm relcomppI}, rtac @{thm conversepI},
        EVERY' (map (fn thm => EVERY' [rtac @{thm GrpI}, rtac sym, rtac trans,
          rtac map_cong0, REPEAT_DETERM_N n o rtac thm,
          rtac (map_comp RS sym), rtac CollectI,
          CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS ord_eq_le_trans),
            etac @{thm flip_pred}]) set_maps]) [@{thm snd_fst_flip}, @{thm fst_snd_flip}])] 1
  end;

fun mk_rel_conversep_tac le_conversep rel_mono =
  EVERY' [rtac @{thm antisym}, rtac le_conversep, rtac @{thm xt1(6)}, rtac conversep_shift,
    rtac le_conversep, rtac @{thm iffD2[OF conversep_mono]}, rtac rel_mono,
    REPEAT_DETERM o rtac @{thm eq_refl[OF sym[OF conversep_conversep]]}] 1;

fun mk_rel_OO_le_tac ctxt rel_OO_Grps rel_eq map_cong0 map_comp set_maps =
  let
    val n = length set_maps;
    fun in_tac nthO_in = rtac CollectI THEN'
        CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS ord_eq_le_trans),
          rtac @{thm image_subsetI}, rtac nthO_in, etac set_mp, atac]) set_maps;
    val rel_OO_Grps_tac = if null rel_OO_Grps then K all_tac
      else rtac (hd rel_OO_Grps RS ord_eq_le_trans) THEN'
        rtac (@{thm arg_cong2[of _ _ _ _ "op OO"]} OF (replicate 2 (hd rel_OO_Grps RS sym)) RSN
          (2, ord_le_eq_trans));
  in
    if null set_maps then rtac (rel_eq RS @{thm leq_OOI}) 1
    else
      EVERY' [rel_OO_Grps_tac, rtac @{thm predicate2I},
        REPEAT_DETERM o
          eresolve_tac [CollectE, exE, conjE, @{thm GrpE}, @{thm relcomppE}, @{thm conversepE}],
        hyp_subst_tac ctxt,
        rtac @{thm relcomppI}, rtac @{thm relcomppI}, rtac @{thm conversepI}, rtac @{thm GrpI},
        rtac trans, rtac map_comp, rtac sym, rtac map_cong0,
        REPEAT_DETERM_N n o rtac @{thm fst_fstOp},
        in_tac @{thm fstOp_in},
        rtac @{thm GrpI}, rtac trans, rtac map_comp, rtac map_cong0,
        REPEAT_DETERM_N n o EVERY' [rtac trans, rtac o_apply,
          rtac ballE, rtac subst,
          rtac @{thm csquare_def}, rtac @{thm csquare_fstOp_sndOp}, atac, etac notE,
          etac set_mp, atac],
        in_tac @{thm fstOp_in},
        rtac @{thm relcomppI}, rtac @{thm conversepI}, rtac @{thm GrpI},
        rtac trans, rtac map_comp, rtac map_cong0,
        REPEAT_DETERM_N n o rtac o_apply,
        in_tac @{thm sndOp_in},
        rtac @{thm GrpI}, rtac trans, rtac map_comp, rtac sym, rtac map_cong0,
        REPEAT_DETERM_N n o rtac @{thm snd_sndOp},
        in_tac @{thm sndOp_in}] 1
  end;

fun mk_rel_mono_strong0_tac ctxt in_rel set_maps =
  if null set_maps then atac 1
  else
    unfold_tac ctxt [in_rel] THEN
    REPEAT_DETERM (eresolve_tac [exE, CollectE, conjE] 1) THEN
    hyp_subst_tac ctxt 1 THEN
    EVERY' [rtac exI, rtac @{thm conjI[OF CollectI conjI[OF refl refl]]},
      CONJ_WRAP' (fn thm =>
        (etac (@{thm Collect_split_mono_strong} OF [thm, thm]) THEN' atac))
      set_maps] 1;

fun mk_map_transfer_tac ctxt rel_mono in_rel set_maps map_cong0 map_comp =
  let
    val n = length set_maps;
    val in_tac = if n = 0 then rtac UNIV_I else
      rtac CollectI THEN' CONJ_WRAP' (fn thm =>
        etac (thm RS
          @{thm ord_eq_le_trans[OF _ subset_trans[OF image_mono convol_image_vimage2p]]}))
      set_maps;
  in
    REPEAT_DETERM_N n (HEADGOAL (rtac @{thm rel_funI})) THEN
    unfold_thms_tac ctxt @{thms rel_fun_iff_leq_vimage2p} THEN
    HEADGOAL (EVERY' [rtac @{thm order_trans}, rtac rel_mono, REPEAT_DETERM_N n o atac,
      rtac @{thm predicate2I}, dtac (in_rel RS iffD1),
      REPEAT_DETERM o eresolve_tac [exE, CollectE, conjE], hyp_subst_tac ctxt,
      rtac @{thm vimage2pI}, rtac (in_rel RS iffD2), rtac exI, rtac conjI, in_tac,
      rtac conjI,
      EVERY' (map (fn convol =>
        rtac (@{thm box_equals} OF [map_cong0, map_comp RS sym, map_comp RS sym]) THEN'
        REPEAT_DETERM_N n o rtac (convol RS fun_cong)) @{thms fst_convol snd_convol})])
  end;

fun mk_in_bd_tac ctxt live surj_imp_ordLeq_inst map_comp map_id map_cong0 set_maps set_bds
  bd_card_order bd_Card_order bd_Cinfinite bd_Cnotzero =
  if live = 0 then
    rtac @{thm ordLeq_transitive[OF ordLeq_csum2[OF card_of_Card_order]
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
      EVERY' [rtac (Drule.rotate_prems 1 ctrans), rtac @{thm cprod_cinfinite_bound},
        rtac (ctrans OF @{thms ordLeq_csum2 ordLeq_cexp2}), rtac @{thm card_of_Card_order},
        rtac @{thm ordLeq_csum2}, rtac @{thm Card_order_ctwo}, rtac @{thm Card_order_csum},
        rtac @{thm ordIso_ordLeq_trans}, rtac @{thm cexp_cong1},
        if live = 1 then rtac @{thm ordIso_refl[OF Card_order_csum]}
        else
          REPEAT_DETERM_N (live - 2) o rtac @{thm ordIso_transitive[OF csum_cong2]} THEN'
          REPEAT_DETERM_N (live - 1) o rtac @{thm csum_csum},
        rtac bd_Card_order, rtac (@{thm cexp_mono2_Cnotzero} RS ctrans), rtac @{thm ordLeq_csum1},
        rtac bd_Card_order, rtac @{thm Card_order_csum}, rtac bd_Cnotzero,
        rtac @{thm csum_Cfinite_cexp_Cinfinite},
        rtac (if live = 1 then @{thm card_of_Card_order} else @{thm Card_order_csum}),
        CONJ_WRAP_GEN' (rtac @{thm Cfinite_csum}) (K (rtac @{thm Cfinite_cone})) set_maps,
        rtac bd'_Cinfinite, rtac @{thm card_of_Card_order},
        rtac @{thm Card_order_cexp}, rtac @{thm Cinfinite_cexp}, rtac @{thm ordLeq_csum2},
        rtac @{thm Card_order_ctwo}, rtac bd'_Cinfinite,
        rtac (Drule.rotate_prems 1 (@{thm cprod_mono2} RSN (2, ctrans))),
        REPEAT_DETERM_N (live - 1) o
          (rtac (bd_Cinfinite RS @{thm cprod_cexp_csum_cexp_Cinfinite} RSN (2, ctrans)) THEN'
           rtac @{thm ordLeq_ordIso_trans[OF cprod_mono2 ordIso_symmetric[OF cprod_cexp]]}),
        rtac @{thm ordLeq_refl[OF Card_order_cexp]}] 1 THEN
      unfold_thms_tac ctxt [bd_card_order RS @{thm card_order_csum_cone_cexp_def}] THEN
      unfold_thms_tac ctxt @{thms cprod_def Field_card_of} THEN
      EVERY' [rtac (Drule.rotate_prems 1 ctrans), rtac surj_imp_ordLeq_inst, rtac subsetI,
        Method.insert_tac inserts, REPEAT_DETERM o dtac meta_spec,
        REPEAT_DETERM o eresolve_tac [exE, Tactic.make_elim conjunct1], etac CollectE,
        if live = 1 then K all_tac
        else REPEAT_DETERM_N (live - 2) o (etac conjE THEN' rotate_tac ~1) THEN' etac conjE,
        rtac (Drule.rotate_prems 1 @{thm image_eqI}), rtac @{thm SigmaI}, rtac @{thm UNIV_I},
        CONJ_WRAP_GEN' (rtac @{thm SigmaI})
          (K (etac @{thm If_the_inv_into_in_Func} THEN' atac)) set_maps,
        rtac sym,
        rtac (Drule.rotate_prems 1
           ((@{thm box_equals} OF [map_cong0 OF replicate live @{thm If_the_inv_into_f_f},
             map_comp RS sym, map_id]) RSN (2, trans))),
        REPEAT_DETERM_N (2 * live) o atac,
        REPEAT_DETERM_N live o rtac (@{thm prod.case} RS trans),
        rtac refl,
        rtac @{thm surj_imp_ordLeq}, rtac subsetI, rtac (Drule.rotate_prems 1 @{thm image_eqI}),
        REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac CollectI,
        CONJ_WRAP' (fn thm =>
          rtac (thm RS ord_eq_le_trans) THEN' etac @{thm subset_trans[OF image_mono Un_upper1]})
        set_maps,
        rtac sym,
        rtac (@{thm box_equals} OF [map_cong0 OF replicate live @{thm fun_cong[OF case_sum_o_inj(1)]},
           map_comp RS sym, map_id])] 1
  end;

fun mk_trivial_wit_tac ctxt wit_defs set_maps =
  unfold_thms_tac ctxt wit_defs THEN HEADGOAL (EVERY' (map (fn thm =>
    dtac (thm RS equalityD1 RS set_mp) THEN' etac imageE THEN' atac) set_maps)) THEN ALLGOALS atac;

end;
