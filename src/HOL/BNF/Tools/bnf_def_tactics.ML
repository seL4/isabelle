(*  Title:      HOL/BNF/Tools/bnf_def_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for definition of bounded natural functors.
*)

signature BNF_DEF_TACTICS =
sig
  val mk_collect_set_map_tac: thm list -> tactic
  val mk_map_id': thm -> thm
  val mk_map_comp': thm -> thm
  val mk_map_cong_tac: Proof.context -> thm -> tactic
  val mk_in_mono_tac: int -> tactic
  val mk_map_wppull_tac: thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_set_map': thm -> thm

  val mk_rel_Grp_tac: thm list -> thm -> thm -> thm -> thm -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_rel_eq_tac: int -> thm -> thm -> thm -> tactic
  val mk_rel_OO_tac: thm list -> thm -> thm -> thm -> thm -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_in_rel_tac: thm list -> {prems: 'b, context: Proof.context} -> tactic
  val mk_rel_conversep_tac: thm -> thm -> tactic
  val mk_rel_conversep_le_tac: thm list -> thm -> thm -> thm -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
  val mk_rel_mono_tac: thm list -> thm -> {prems: 'a, context: Proof.context} -> tactic
end;

structure BNF_Def_Tactics : BNF_DEF_TACTICS =
struct

open BNF_Util
open BNF_Tactics

fun mk_map_id' id = mk_trans (fun_cong OF [id]) @{thm id_apply};
fun mk_map_comp' comp = @{thm o_eq_dest_lhs} OF [mk_sym comp];
fun mk_map_cong_tac ctxt cong0 =
  (hyp_subst_tac ctxt THEN' rtac cong0 THEN'
   REPEAT_DETERM o (dtac meta_spec THEN' etac meta_mp THEN' atac)) 1;
fun mk_set_map' set_map = set_map RS @{thm pointfreeE};
fun mk_in_mono_tac n = if n = 0 then rtac subset_UNIV 1
  else (rtac subsetI THEN'
  rtac CollectI) 1 THEN
  REPEAT_DETERM (eresolve_tac [CollectE, conjE] 1) THEN
  REPEAT_DETERM_N (n - 1)
    ((rtac conjI THEN' etac subset_trans THEN' atac) 1) THEN
  (etac subset_trans THEN' atac) 1;

fun mk_collect_set_map_tac set_maps =
  (rtac (@{thm collect_o} RS trans) THEN' rtac @{thm arg_cong[of _ _ collect]} THEN'
  EVERY' (map (fn set_map =>
    rtac (mk_trans @{thm image_insert} @{thm arg_cong2[of _ _ _ _ insert]}) THEN'
    rtac set_map) set_maps) THEN'
  rtac @{thm image_empty}) 1;

fun mk_map_wppull_tac map_id map_cong0 map_wpull map_comp set_maps =
  if null set_maps then
    EVERY' [rtac @{thm wppull_id}, rtac map_wpull, rtac map_id, rtac map_id] 1
  else EVERY' [REPEAT_DETERM o etac conjE, REPEAT_DETERM o dtac @{thm wppull_thePull},
    REPEAT_DETERM o etac exE, rtac @{thm wpull_wppull}, rtac map_wpull,
    REPEAT_DETERM o rtac @{thm wpull_thePull}, rtac ballI,
    REPEAT_DETERM o eresolve_tac [CollectE, conjE], rtac conjI, rtac CollectI,
    CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
      rtac @{thm image_subsetI}, rtac conjunct1, etac bspec, etac set_mp, atac])
      set_maps,
    CONJ_WRAP' (fn thm => EVERY' [rtac (map_comp RS trans), rtac (map_comp RS trans),
      rtac (map_comp RS trans RS sym), rtac map_cong0,
      REPEAT_DETERM_N (length set_maps) o EVERY' [rtac (o_apply RS trans),
        rtac (o_apply RS trans RS sym), rtac (o_apply RS trans), rtac thm,
        rtac conjunct2, etac bspec, etac set_mp, atac]]) [conjunct1, conjunct2]] 1;

fun mk_rel_Grp_tac rel_OO_Grps map_id map_cong0 map_id' map_comp set_maps
  {context = ctxt, prems = _} =
  let
    val n = length set_maps;
  in
    if null set_maps then
      unfold_thms_tac ctxt ((map_id RS @{thm Grp_UNIV_id}) :: rel_OO_Grps) THEN
      rtac @{thm Grp_UNIV_idI[OF refl]} 1
    else unfold_thms_tac ctxt rel_OO_Grps THEN
      EVERY' [rtac @{thm antisym}, rtac @{thm predicate2I},
        REPEAT_DETERM o
          eresolve_tac [CollectE, exE, conjE, @{thm GrpE}, @{thm relcomppE}, @{thm conversepE}],
        hyp_subst_tac ctxt, rtac @{thm GrpI}, rtac trans, rtac map_comp, rtac map_cong0,
        REPEAT_DETERM_N n o EVERY' [rtac @{thm Collect_split_Grp_eqD}, etac @{thm set_mp}, atac],
        rtac CollectI,
        CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
          rtac @{thm image_subsetI}, rtac @{thm Collect_split_Grp_inD}, etac @{thm set_mp}, atac])
        set_maps,
        rtac @{thm predicate2I}, REPEAT_DETERM o eresolve_tac [@{thm GrpE}, exE, conjE],
        hyp_subst_tac ctxt,
        rtac @{thm relcomppI}, rtac @{thm conversepI},
        EVERY' (map2 (fn convol => fn map_id =>
          EVERY' [rtac @{thm GrpI}, rtac (box_equals OF [map_cong0, map_comp RS sym, map_id]),
            REPEAT_DETERM_N n o rtac (convol RS fun_cong),
            REPEAT_DETERM o eresolve_tac [CollectE, conjE],
            rtac CollectI,
            CONJ_WRAP' (fn thm =>
              EVERY' [rtac @{thm ord_eq_le_trans}, rtac thm, rtac @{thm image_subsetI},
                rtac @{thm convol_mem_GrpI[OF refl]}, etac set_mp, atac])
            set_maps])
          @{thms fst_convol snd_convol} [map_id', refl])] 1
  end;

fun mk_rel_eq_tac n rel_Grp rel_cong map_id =
  (EVERY' (rtac (rel_cong RS trans) :: replicate n (rtac @{thm eq_alt})) THEN'
  rtac (rel_Grp RSN (2, @{thm box_equals[OF _ sym sym[OF eq_alt]]})) THEN'
  (if n = 0 then rtac refl
  else EVERY' [rtac @{thm arg_cong2[of _ _ _ _ "Grp"]},
    rtac @{thm equalityI}, rtac subset_UNIV, rtac subsetI, rtac CollectI,
    CONJ_WRAP' (K (rtac subset_UNIV)) (1 upto n), rtac map_id])) 1;

fun mk_rel_mono_tac rel_OO_Grps in_mono {context = ctxt, prems = _} =
  unfold_thms_tac ctxt rel_OO_Grps THEN
    EVERY' [rtac @{thm relcompp_mono}, rtac @{thm iffD2[OF conversep_mono]},
      rtac @{thm Grp_mono}, rtac in_mono, REPEAT_DETERM o etac @{thm Collect_split_mono},
      rtac @{thm Grp_mono}, rtac in_mono, REPEAT_DETERM o etac @{thm Collect_split_mono}] 1;

fun mk_rel_conversep_le_tac rel_OO_Grps rel_eq map_cong0 map_comp set_maps
  {context = ctxt, prems = _} =
  let
    val n = length set_maps;
  in
    if null set_maps then rtac (rel_eq RS @{thm leq_conversepI}) 1
    else unfold_thms_tac ctxt (rel_OO_Grps) THEN
      EVERY' [rtac @{thm predicate2I},
        REPEAT_DETERM o
          eresolve_tac [CollectE, exE, conjE, @{thm GrpE}, @{thm relcomppE}, @{thm conversepE}],
        hyp_subst_tac ctxt, rtac @{thm conversepI}, rtac @{thm relcomppI}, rtac @{thm conversepI},
        EVERY' (map (fn thm => EVERY' [rtac @{thm GrpI}, rtac sym, rtac trans,
          rtac map_cong0, REPEAT_DETERM_N n o rtac thm,
          rtac (map_comp RS sym), rtac CollectI,
          CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
            etac @{thm flip_pred}]) set_maps]) [@{thm snd_fst_flip}, @{thm fst_snd_flip}])] 1
  end;

fun mk_rel_conversep_tac le_conversep rel_mono =
  EVERY' [rtac @{thm antisym}, rtac le_conversep, rtac @{thm xt1(6)}, rtac @{thm conversep_shift},
    rtac le_conversep, rtac @{thm iffD2[OF conversep_mono]}, rtac rel_mono,
    REPEAT_DETERM o rtac @{thm eq_refl[OF sym[OF conversep_conversep]]}] 1;

fun mk_rel_OO_tac rel_OO_Grs rel_eq map_cong0 map_wppull map_comp set_maps
  {context = ctxt, prems = _} =
  let
    val n = length set_maps;
    fun in_tac nthO_in = rtac CollectI THEN'
        CONJ_WRAP' (fn thm => EVERY' [rtac (thm RS @{thm ord_eq_le_trans}),
          rtac @{thm image_subsetI}, rtac nthO_in, etac set_mp, atac]) set_maps;
  in
    if null set_maps then rtac (rel_eq RS @{thm eq_OOI}) 1
    else unfold_thms_tac ctxt rel_OO_Grs THEN
      EVERY' [rtac @{thm antisym}, rtac @{thm predicate2I},
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
        in_tac @{thm sndOp_in},
        rtac @{thm predicate2I},
        REPEAT_DETERM o eresolve_tac [@{thm relcomppE}, @{thm conversepE}, @{thm GrpE}],
        hyp_subst_tac ctxt,
        rtac allE, rtac subst, rtac @{thm wppull_def}, rtac map_wppull,
        CONJ_WRAP' (K (rtac @{thm wppull_fstOp_sndOp})) set_maps,
        etac allE, etac impE, etac conjI, etac conjI, etac sym,
        REPEAT_DETERM o eresolve_tac [bexE, conjE],
        rtac @{thm relcomppI}, rtac @{thm conversepI},
        EVERY' (map (fn thm => EVERY' [rtac @{thm GrpI}, rtac trans,
          rtac trans, rtac map_cong0, REPEAT_DETERM_N n o rtac thm,
          rtac (map_comp RS sym), atac, atac]) [@{thm fst_fstOp}, @{thm snd_sndOp}])] 1
  end;

fun mk_in_rel_tac rel_OO_Grs {context = ctxt, prems = _} =
  unfold_thms_tac ctxt rel_OO_Grs THEN
  EVERY' [rtac iffI,
    REPEAT_DETERM o eresolve_tac [@{thm GrpE}, @{thm relcomppE}, @{thm conversepE}],
    hyp_subst_tac ctxt, rtac exI, rtac conjI, atac, rtac conjI, rtac refl, rtac refl,
    REPEAT_DETERM o eresolve_tac [exE, conjE], rtac @{thm relcomppI}, rtac @{thm conversepI},
    etac @{thm GrpI}, atac, etac @{thm GrpI}, atac] 1;

end;
