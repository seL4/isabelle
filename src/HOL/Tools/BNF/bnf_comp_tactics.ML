(*  Title:      HOL/Tools/BNF/bnf_comp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for composition of bounded natural functors.
*)

signature BNF_COMP_TACTICS =
sig
  val mk_comp_bd_card_order_tac: thm list -> thm -> tactic
  val mk_comp_bd_cinfinite_tac: thm -> thm -> tactic
  val mk_comp_in_alt_tac: Proof.context -> thm list -> tactic
  val mk_comp_map_comp0_tac: thm -> thm -> thm list -> tactic
  val mk_comp_map_cong0_tac: Proof.context -> thm list -> thm list -> thm -> thm list -> tactic
  val mk_comp_map_id0_tac: thm -> thm -> thm list -> tactic
  val mk_comp_set_alt_tac: Proof.context -> thm -> tactic
  val mk_comp_set_bd_tac: Proof.context -> thm -> thm option -> thm -> thm list -> tactic
  val mk_comp_set_map0_tac: Proof.context -> thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_comp_wit_tac: Proof.context -> thm list -> thm list -> thm -> thm list -> tactic

  val kill_in_alt_tac: tactic
  val mk_kill_map_cong0_tac: Proof.context -> int -> int -> thm -> tactic

  val empty_natural_tac: tactic
  val lift_in_alt_tac: tactic
  val mk_lift_set_bd_tac: thm -> tactic

  val mk_permute_in_alt_tac: ''a list -> ''a list -> tactic

  val mk_le_rel_OO_tac: thm -> thm -> thm list -> tactic
  val mk_simple_rel_OO_Grp_tac: thm -> thm -> tactic
  val mk_simple_wit_tac: thm list -> tactic
  val mk_simplified_set_tac: Proof.context -> thm -> tactic
  val bd_ordIso_natLeq_tac: tactic
end;

structure BNF_Comp_Tactics : BNF_COMP_TACTICS =
struct

open BNF_Util
open BNF_Tactics

val arg_cong_Union = @{thm arg_cong[of _ _ Union]};
val comp_eq_dest_lhs = @{thm comp_eq_dest_lhs};
val trans_image_cong_o_apply = @{thm trans[OF image_cong[OF o_apply refl]]};
val trans_o_apply = @{thm trans[OF o_apply]};


(* Composition *)

fun mk_comp_set_alt_tac ctxt collect_set_map =
  unfold_thms_tac ctxt @{thms comp_assoc} THEN
  unfold_thms_tac ctxt [collect_set_map RS sym] THEN
  rtac refl 1;

fun mk_comp_map_id0_tac Gmap_id0 Gmap_cong0 map_id0s =
  EVERY' ([rtac @{thm ext}, rtac (Gmap_cong0 RS trans)] @
    map (fn thm => rtac (thm RS fun_cong)) map_id0s @ [rtac (Gmap_id0 RS fun_cong)]) 1;

fun mk_comp_map_comp0_tac Gmap_comp0 Gmap_cong0 map_comp0s =
  EVERY' ([rtac @{thm ext}, rtac sym, rtac trans_o_apply,
    rtac (Gmap_comp0 RS sym RS comp_eq_dest_lhs RS trans), rtac Gmap_cong0] @
    map (fn thm => rtac (thm RS sym RS fun_cong)) map_comp0s) 1;

fun mk_comp_set_map0_tac ctxt set'_eq_set Gmap_comp0 Gmap_cong0 Gset_map0 set_map0s =
  unfold_thms_tac ctxt [set'_eq_set] THEN
  EVERY' ([rtac @{thm ext}] @
    replicate 3 (rtac trans_o_apply) @
    [rtac (arg_cong_Union RS trans),
     rtac (@{thm arg_cong2[of _ _ _ _ collect, OF refl]} RS trans),
     rtac (Gmap_comp0 RS sym RS comp_eq_dest_lhs RS trans),
     rtac Gmap_cong0] @
     map (fn thm => rtac (thm RS fun_cong)) set_map0s @
     [rtac (Gset_map0 RS comp_eq_dest_lhs), rtac sym, rtac trans_o_apply,
     rtac trans_image_cong_o_apply, rtac trans_image_cong_o_apply,
     rtac (@{thm image_cong} OF [Gset_map0 RS comp_eq_dest_lhs RS arg_cong_Union, refl] RS trans),
     rtac @{thm trans[OF comp_eq_dest[OF Union_natural[symmetric]]]}, rtac arg_cong_Union,
     rtac @{thm trans[OF comp_eq_dest_lhs[OF image_o_collect[symmetric]]]},
     rtac @{thm fun_cong[OF arg_cong[of _ _ collect]]}] @
     [REPEAT_DETERM_N (length set_map0s) o EVERY' [rtac @{thm trans[OF image_insert]},
        rtac @{thm arg_cong2[of _ _ _ _ insert]}, rtac @{thm ext}, rtac trans_o_apply,
        rtac trans_image_cong_o_apply, rtac @{thm trans[OF image_image]},
        rtac @{thm sym[OF trans[OF o_apply]]}, rtac @{thm image_cong[OF refl o_apply]}],
     rtac @{thm image_empty}]) 1;

fun mk_comp_map_cong0_tac ctxt set'_eq_sets comp_set_alts map_cong0 map_cong0s =
  let
     val n = length comp_set_alts;
  in
    unfold_thms_tac ctxt set'_eq_sets THEN
    (if n = 0 then rtac refl 1
    else rtac map_cong0 1 THEN
      EVERY' (map_index (fn (i, map_cong0) =>
        rtac map_cong0 THEN' EVERY' (map_index (fn (k, set_alt) =>
          EVERY' [select_prem_tac n (dtac @{thm meta_spec}) (k + 1), etac meta_mp,
            rtac (equalityD2 RS set_mp), rtac (set_alt RS fun_cong RS trans),
            rtac trans_o_apply, rtac (@{thm collect_def} RS arg_cong_Union),
            rtac @{thm UnionI}, rtac @{thm UN_I}, REPEAT_DETERM_N i o rtac @{thm insertI2},
            rtac @{thm insertI1}, rtac (o_apply RS equalityD2 RS set_mp),
            etac @{thm imageI}, atac])
          comp_set_alts))
      map_cong0s) 1)
  end;

fun mk_comp_bd_card_order_tac Fbd_card_orders Gbd_card_order =
  rtac @{thm natLeq_card_order} 1 ORELSE
  let
    val (card_orders, last_card_order) = split_last Fbd_card_orders;
    fun gen_before thm = rtac @{thm card_order_csum} THEN' rtac thm;
  in
    (rtac @{thm card_order_cprod} THEN'
    WRAP' gen_before (K (K all_tac)) card_orders (rtac last_card_order) THEN'
    rtac Gbd_card_order) 1
  end;

fun mk_comp_bd_cinfinite_tac Fbd_cinfinite Gbd_cinfinite =
  (rtac @{thm natLeq_cinfinite} ORELSE'
   rtac @{thm cinfinite_cprod} THEN'
   ((K (TRY ((rtac @{thm cinfinite_csum} THEN' rtac disjI1) 1)) THEN'
     ((rtac @{thm cinfinite_csum} THEN' rtac disjI1 THEN' rtac Fbd_cinfinite) ORELSE'
      rtac Fbd_cinfinite)) ORELSE'
    rtac Fbd_cinfinite) THEN'
   rtac Gbd_cinfinite) 1;

fun mk_comp_set_bd_tac ctxt set'_eq_set bd_ordIso_natLeq_opt comp_set_alt Gset_Fset_bds =
  let
    val (bds, last_bd) = split_last Gset_Fset_bds;
    fun gen_before bd =
      rtac ctrans THEN' rtac @{thm Un_csum} THEN'
      rtac ctrans THEN' rtac @{thm csum_mono} THEN'
      rtac bd;
    fun gen_after _ = rtac @{thm ordIso_imp_ordLeq} THEN' rtac @{thm cprod_csum_distrib1};
  in
    (case bd_ordIso_natLeq_opt of
      SOME thm => rtac (thm RSN (2, @{thm ordLeq_ordIso_trans})) 1
    | NONE => all_tac) THEN
    unfold_thms_tac ctxt [set'_eq_set, comp_set_alt] THEN
    rtac @{thm comp_set_bd_Union_o_collect} 1 THEN
    unfold_thms_tac ctxt @{thms Union_image_insert Union_image_empty Union_Un_distrib o_apply} THEN
    (rtac ctrans THEN'
     WRAP' gen_before gen_after bds (rtac last_bd) THEN'
     rtac @{thm ordIso_imp_ordLeq} THEN'
     rtac @{thm cprod_com}) 1
  end;

val comp_in_alt_thms = @{thms o_apply collect_def image_insert image_empty Union_insert UN_insert
  UN_empty Union_empty Un_empty_right Union_Un_distrib Un_subset_iff conj_subset_def UN_image_subset
  conj_assoc};

fun mk_comp_in_alt_tac ctxt comp_set_alts =
  unfold_thms_tac ctxt comp_set_alts THEN
  unfold_thms_tac ctxt comp_in_alt_thms THEN
  unfold_thms_tac ctxt @{thms set_eq_subset} THEN
  rtac conjI 1 THEN
  REPEAT_DETERM (
    rtac @{thm subsetI} 1 THEN
    unfold_thms_tac ctxt @{thms mem_Collect_eq Ball_def} THEN
    (REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
     REPEAT_DETERM (CHANGED ((
       (rtac conjI THEN' (atac ORELSE' rtac subset_UNIV)) ORELSE'
       atac ORELSE'
       (rtac subset_UNIV)) 1)) ORELSE rtac subset_UNIV 1));

val comp_wit_thms = @{thms Union_empty_conv o_apply collect_def UN_insert UN_empty Un_empty_right
  Union_image_insert Union_image_empty};

fun mk_comp_wit_tac ctxt set'_eq_sets Gwit_thms collect_set_map Fwit_thms =
  unfold_thms_tac ctxt set'_eq_sets THEN
  ALLGOALS (dtac @{thm in_Union_o_assoc}) THEN
  unfold_thms_tac ctxt [collect_set_map] THEN
  unfold_thms_tac ctxt comp_wit_thms THEN
  REPEAT_DETERM ((atac ORELSE'
    REPEAT_DETERM o eresolve_tac @{thms UnionE UnE} THEN'
    etac imageE THEN' TRY o dresolve_tac Gwit_thms THEN'
    (etac FalseE ORELSE'
    hyp_subst_tac ctxt THEN'
    dresolve_tac Fwit_thms THEN'
    (etac FalseE ORELSE' atac))) 1);


(* Kill operation *)

fun mk_kill_map_cong0_tac ctxt n m map_cong0 =
  (rtac map_cong0 THEN' EVERY' (replicate n (rtac refl)) THEN'
    EVERY' (replicate m (Goal.assume_rule_tac ctxt))) 1;

val kill_in_alt_tac =
  ((rtac @{thm Collect_cong} THEN' rtac iffI) 1 THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE'
    rtac conjI THEN' rtac subset_UNIV) 1)) THEN
  (rtac subset_UNIV ORELSE' atac) 1 THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE' atac) 1))) ORELSE
  ((rtac @{thm UNIV_eq_I} THEN' rtac CollectI) 1 THEN
    REPEAT_DETERM (TRY (rtac conjI 1) THEN rtac subset_UNIV 1));


(* Lift operation *)

val empty_natural_tac = rtac @{thm empty_natural} 1;

fun mk_lift_set_bd_tac bd_Card_order = (rtac @{thm Card_order_empty} THEN' rtac bd_Card_order) 1;

val lift_in_alt_tac =
  ((rtac @{thm Collect_cong} THEN' rtac iffI) 1 THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE' atac) 1)) THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE'
    rtac conjI THEN' rtac @{thm empty_subsetI}) 1)) THEN
  (rtac @{thm empty_subsetI} ORELSE' atac) 1) ORELSE
  ((rtac sym THEN' rtac @{thm UNIV_eq_I} THEN' rtac CollectI) 1 THEN
    REPEAT_DETERM (TRY (rtac conjI 1) THEN rtac @{thm empty_subsetI} 1));


(* Permute operation *)

fun mk_permute_in_alt_tac src dest =
  (rtac @{thm Collect_cong} THEN'
  mk_rotate_eq_tac (rtac refl) trans @{thm conj_assoc} @{thm conj_commute} @{thm conj_cong}
    dest src) 1;


(* Miscellaneous *)

fun mk_le_rel_OO_tac outer_le_rel_OO outer_rel_mono inner_le_rel_OOs =
  EVERY' (map rtac (@{thm order_trans} :: outer_le_rel_OO :: outer_rel_mono :: inner_le_rel_OOs)) 1;

fun mk_simple_rel_OO_Grp_tac rel_OO_Grp in_alt_thm =
  rtac (trans OF [rel_OO_Grp, in_alt_thm RS @{thm OO_Grp_cong} RS sym]) 1;

fun mk_simple_wit_tac wit_thms = ALLGOALS (atac ORELSE' eresolve_tac (@{thm emptyE} :: wit_thms));

val csum_thms =
  @{thms csum_cong1 csum_cong2 csum_cong  csum_dup[OF natLeq_cinfinite natLeq_Card_order]};
val cprod_thms =
  @{thms cprod_cong1 cprod_cong2 cprod_cong cprod_dup[OF natLeq_cinfinite natLeq_Card_order]};

val simplified_set_simps =
  @{thms collect_def[abs_def] UN_insert UN_empty Un_empty_right Un_empty_left
    o_def Union_Un_distrib Union_image_eq UN_empty2 UN_singleton id_bnf_def};

fun mk_simplified_set_tac ctxt collect_set_map =
  unfold_thms_tac ctxt (collect_set_map :: @{thms comp_assoc}) THEN
  unfold_thms_tac ctxt simplified_set_simps THEN rtac refl 1;

val bd_ordIso_natLeq_tac =
  HEADGOAL (REPEAT_DETERM o resolve_tac
    (@{thm ordIso_refl[OF natLeq_Card_order]} :: csum_thms @ cprod_thms));

end;
