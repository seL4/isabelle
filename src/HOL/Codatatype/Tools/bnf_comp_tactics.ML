(*  Title:      HOL/Codatatype/Tools/bnf_comp_tactics.ML
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
  val mk_comp_in_bd_tac: thm -> thm list -> thm -> thm list -> thm -> tactic
  val mk_comp_map_comp_tac: thm -> thm -> thm list -> tactic
  val mk_comp_map_cong_tac: thm list -> thm -> thm list -> tactic
  val mk_comp_set_alt_tac: Proof.context -> thm -> tactic
  val mk_comp_set_bd_tac: Proof.context -> thm -> thm list -> tactic
  val mk_comp_set_natural_tac: thm -> thm -> thm -> thm list -> tactic
  val mk_comp_wit_tac: Proof.context -> thm list -> thm -> thm list -> tactic

  val mk_killN_bd_card_order_tac: int -> thm -> tactic
  val mk_killN_bd_cinfinite_tac: thm -> tactic
  val killN_in_alt_tac: tactic
  val mk_killN_in_bd_tac: int -> bool -> thm -> thm -> thm -> thm -> thm -> tactic
  val mk_killN_map_cong_tac: Proof.context -> int -> int -> thm -> tactic
  val mk_killN_set_bd_tac: thm -> thm -> tactic

  val empty_natural_tac: tactic
  val liftN_in_alt_tac: tactic
  val mk_liftN_in_bd_tac: int -> thm -> thm -> thm -> tactic
  val mk_liftN_set_bd_tac: thm -> tactic

  val mk_permute_in_alt_tac: ''a list -> ''a list -> tactic
  val mk_permute_in_bd_tac: ''a list -> ''a list -> thm -> thm -> thm -> tactic

  val mk_map_wpull_tac: thm -> thm list -> thm -> tactic
  val mk_simple_wit_tac: thm list -> tactic
end;

structure BNF_Comp_Tactics : BNF_COMP_TACTICS =
struct

open BNF_Util
open BNF_Tactics

val arg_cong_Union = @{thm arg_cong[of _ _ Union]};
val o_eq_dest_lhs = @{thm o_eq_dest_lhs};
val set_mp = @{thm set_mp};
val trans_image_cong_o_apply = @{thm trans[OF image_cong[OF o_apply refl]]};
val trans_o_apply = @{thm trans[OF o_apply]};



(* Composition *)

fun mk_comp_set_alt_tac ctxt collect_set_natural =
  Local_Defs.unfold_tac ctxt @{thms sym[OF o_assoc]} THEN
  Local_Defs.unfold_tac ctxt [collect_set_natural RS sym] THEN
  rtac refl 1;

fun mk_comp_map_comp_tac Gmap_comp Gmap_cong map_comps =
  EVERY' ([rtac ext, rtac sym, rtac trans_o_apply,
    rtac (Gmap_comp RS sym RS o_eq_dest_lhs RS trans), rtac Gmap_cong] @
    map (fn thm => rtac (thm RS sym RS fun_cong)) map_comps) 1;

fun mk_comp_set_natural_tac Gmap_comp Gmap_cong Gset_natural set_naturals =
  EVERY' ([rtac ext] @
    replicate 3 (rtac trans_o_apply) @
    [rtac (arg_cong_Union RS trans),
     rtac (@{thm arg_cong2[of _ _ _ _ collect, OF refl]} RS trans),
     rtac (Gmap_comp RS sym RS o_eq_dest_lhs RS trans),
     rtac Gmap_cong] @
     map (fn thm => rtac (thm RS fun_cong)) set_naturals @
     [rtac (Gset_natural RS o_eq_dest_lhs), rtac sym, rtac trans_o_apply,
     rtac trans_image_cong_o_apply, rtac trans_image_cong_o_apply,
     rtac (@{thm image_cong} OF [Gset_natural RS o_eq_dest_lhs RS arg_cong_Union, refl] RS trans),
     rtac @{thm trans[OF pointfreeE[OF Union_natural[symmetric]]]}, rtac arg_cong_Union,
     rtac @{thm trans[OF o_eq_dest_lhs[OF image_o_collect[symmetric]]]},
     rtac @{thm fun_cong[OF arg_cong[of _ _ collect]]}] @
     [REPEAT_DETERM_N (length set_naturals) o EVERY' [rtac @{thm trans[OF image_insert]},
        rtac @{thm arg_cong2[of _ _ _ _ insert]}, rtac ext, rtac trans_o_apply,
        rtac @{thm trans[OF image_cong[OF o_apply refl]]}, rtac @{thm trans[OF image_image]},
        rtac @{thm sym[OF trans[OF o_apply]]}, rtac @{thm image_cong[OF refl o_apply]}],
     rtac @{thm image_empty}]) 1;

fun mk_comp_map_cong_tac comp_set_alts map_cong map_congs =
  let
     val n = length comp_set_alts;
  in
    (if n = 0 then rtac refl 1
    else rtac map_cong 1 THEN
      EVERY' (map_index (fn (i, map_cong) =>
        rtac map_cong THEN' EVERY' (map_index (fn (k, set_alt) =>
          EVERY' [select_prem_tac n (dtac @{thm meta_spec}) (k + 1), etac @{thm meta_mp},
            rtac (equalityD2 RS set_mp), rtac (set_alt RS fun_cong RS trans),
            rtac trans_o_apply, rtac (@{thm collect_def} RS arg_cong_Union),
            rtac @{thm UnionI}, rtac @{thm UN_I}, REPEAT_DETERM_N i o rtac @{thm insertI2},
            rtac @{thm insertI1}, rtac (o_apply RS equalityD2 RS set_mp),
            etac @{thm imageI}, atac])
          comp_set_alts))
      map_congs) 1)
  end;

fun mk_comp_bd_card_order_tac Fbd_card_orders Gbd_card_order =
  let
    val (card_orders, last_card_order) = split_last Fbd_card_orders;
    fun gen_before thm = rtac @{thm card_order_csum} THEN' rtac thm;
  in
    (rtac @{thm card_order_cprod} THEN'
    WRAP' gen_before (K (K all_tac)) card_orders (rtac last_card_order) THEN'
    rtac Gbd_card_order) 1
  end;

fun mk_comp_bd_cinfinite_tac Fbd_cinfinite Gbd_cinfinite =
  (rtac @{thm cinfinite_cprod} THEN'
   ((K (TRY ((rtac @{thm cinfinite_csum} THEN' rtac disjI1) 1)) THEN'
     ((rtac @{thm cinfinite_csum} THEN' rtac disjI1 THEN' rtac Fbd_cinfinite) ORELSE'
      rtac Fbd_cinfinite)) ORELSE'
    rtac Fbd_cinfinite) THEN'
   rtac Gbd_cinfinite) 1;

fun mk_comp_set_bd_tac ctxt comp_set_alt Gset_Fset_bds =
  let
    val (bds, last_bd) = split_last Gset_Fset_bds;
    fun gen_before bd =
      rtac ctrans THEN' rtac @{thm Un_csum} THEN'
      rtac ctrans THEN' rtac @{thm csum_mono} THEN'
      rtac bd;
    fun gen_after _ = rtac @{thm ordIso_imp_ordLeq} THEN' rtac @{thm cprod_csum_distrib1};
  in
    Local_Defs.unfold_tac ctxt [comp_set_alt] THEN
    rtac @{thm comp_set_bd_Union_o_collect} 1 THEN
    Local_Defs.unfold_tac ctxt @{thms Union_image_insert Union_image_empty Union_Un_distrib
      o_apply} THEN
    (rtac ctrans THEN'
     WRAP' gen_before gen_after bds (rtac last_bd) THEN'
     rtac @{thm ordIso_imp_ordLeq} THEN'
     rtac @{thm cprod_com}) 1
  end;

val comp_in_alt_thms = @{thms o_apply collect_def SUP_def image_insert image_empty Union_insert
  Union_empty Un_empty_right Union_Un_distrib Un_subset_iff conj_subset_def UN_image_subset
  conj_assoc};

fun mk_comp_in_alt_tac ctxt comp_set_alts =
  Local_Defs.unfold_tac ctxt (comp_set_alts @ comp_in_alt_thms) THEN
  Local_Defs.unfold_tac ctxt @{thms set_eq_subset} THEN
  rtac conjI 1 THEN
  REPEAT_DETERM (
    rtac @{thm subsetI} 1 THEN
    Local_Defs.unfold_tac ctxt @{thms mem_Collect_eq Ball_def} THEN
    (REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
     REPEAT_DETERM (CHANGED ((
       (rtac conjI THEN' (atac ORELSE' rtac @{thm subset_UNIV})) ORELSE'
       atac ORELSE'
       (rtac @{thm subset_UNIV})) 1)) ORELSE rtac @{thm subset_UNIV} 1));

fun mk_comp_in_bd_tac comp_in_alt Fin_bds Gin_bd Fbd_Cinfs Gbd_Card_order =
  let
    val (bds, last_bd) = split_last Fin_bds;
    val (Cinfs, _) = split_last Fbd_Cinfs;
    fun gen_before (bd, _) = rtac ctrans THEN' rtac @{thm csum_mono} THEN' rtac bd;
    fun gen_after (_, (bd_Cinf, next_bd_Cinf)) =
      TRY o (rtac @{thm csum_cexp} THEN'
        rtac bd_Cinf THEN'
        (TRY o (rtac @{thm Cinfinite_csum} THEN' rtac disjI1) THEN' rtac next_bd_Cinf ORELSE'
           rtac next_bd_Cinf) THEN'
        ((rtac @{thm Card_order_csum} THEN' rtac @{thm ordLeq_csum2}) ORELSE'
          (rtac @{thm Card_order_ctwo} THEN' rtac @{thm ordLeq_refl})) THEN'
        rtac @{thm Card_order_ctwo});
  in
    (rtac @{thm ordIso_ordLeq_trans} THEN'
     rtac @{thm card_of_ordIso_subst} THEN'
     rtac comp_in_alt THEN'
     rtac ctrans THEN'
     rtac Gin_bd THEN'
     rtac @{thm ordLeq_ordIso_trans} THEN'
     rtac @{thm cexp_mono1} THEN'
     rtac @{thm ordLeq_ordIso_trans} THEN'
     rtac @{thm csum_mono1} THEN'
     WRAP' gen_before gen_after (bds ~~ (Cinfs ~~ tl Fbd_Cinfs)) (rtac last_bd) THEN'
     rtac @{thm csum_absorb1} THEN'
     rtac @{thm Cinfinite_cexp} THEN'
     (rtac @{thm ordLeq_csum2} ORELSE' rtac @{thm ordLeq_refl}) THEN'
     rtac @{thm Card_order_ctwo} THEN'
     (TRY o (rtac @{thm Cinfinite_csum} THEN' rtac disjI1) THEN' rtac (hd Fbd_Cinfs) ORELSE'
       rtac (hd Fbd_Cinfs)) THEN'
     rtac @{thm ctwo_ordLeq_Cinfinite} THEN'
     rtac @{thm Cinfinite_cexp} THEN'
     (rtac @{thm ordLeq_csum2} ORELSE' rtac @{thm ordLeq_refl}) THEN'
     rtac @{thm Card_order_ctwo} THEN'
     (TRY o (rtac @{thm Cinfinite_csum} THEN' rtac disjI1) THEN' rtac (hd Fbd_Cinfs) ORELSE'
       rtac (hd Fbd_Cinfs)) THEN'
     rtac disjI1 THEN'
     TRY o rtac @{thm csum_Cnotzero2} THEN'
     rtac @{thm ctwo_Cnotzero} THEN'
     rtac Gbd_Card_order THEN'
     rtac @{thm cexp_cprod} THEN'
     TRY o rtac @{thm csum_Cnotzero2} THEN'
     rtac @{thm ctwo_Cnotzero}) 1
  end;

val comp_wit_thms = @{thms Union_empty_conv o_apply collect_def SUP_def
  Union_image_insert Union_image_empty};

fun mk_comp_wit_tac ctxt Gwit_thms collect_set_natural Fwit_thms =
  ALLGOALS (dtac @{thm in_Union_o_assoc}) THEN
  Local_Defs.unfold_tac ctxt (collect_set_natural :: comp_wit_thms) THEN
  REPEAT_DETERM (
    atac 1 ORELSE
    REPEAT_DETERM (eresolve_tac @{thms UnionE UnE imageE} 1) THEN
    (TRY o dresolve_tac Gwit_thms THEN'
    (etac FalseE ORELSE'
    hyp_subst_tac THEN'
    dresolve_tac Fwit_thms THEN'
    (etac FalseE ORELSE' atac))) 1);



(* Kill operation *)

fun mk_killN_map_cong_tac ctxt n m map_cong =
  (rtac map_cong THEN' EVERY' (replicate n (rtac refl)) THEN'
    EVERY' (replicate m (Goal.assume_rule_tac ctxt))) 1;

fun mk_killN_bd_card_order_tac n bd_card_order =
  (rtac @{thm card_order_cprod} THEN'
  K (REPEAT_DETERM_N (n - 1)
    ((rtac @{thm card_order_csum} THEN'
    rtac @{thm card_of_card_order_on}) 1)) THEN'
  rtac @{thm card_of_card_order_on} THEN'
  rtac bd_card_order) 1;

fun mk_killN_bd_cinfinite_tac bd_Cinfinite =
  (rtac @{thm cinfinite_cprod2} THEN'
  TRY o rtac @{thm csum_Cnotzero1} THEN'
  rtac @{thm Cnotzero_UNIV} THEN'
  rtac bd_Cinfinite) 1;

fun mk_killN_set_bd_tac bd_Card_order set_bd =
  (rtac ctrans THEN'
  rtac set_bd THEN'
  rtac @{thm ordLeq_cprod2} THEN'
  TRY o rtac @{thm csum_Cnotzero1} THEN'
  rtac @{thm Cnotzero_UNIV} THEN'
  rtac bd_Card_order) 1

val killN_in_alt_tac =
  ((rtac @{thm Collect_cong} THEN' rtac @{thm iffI}) 1 THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE'
    rtac conjI THEN' rtac @{thm subset_UNIV}) 1)) THEN
  (rtac @{thm subset_UNIV} ORELSE' atac) 1 THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE' atac) 1))) ORELSE
  ((rtac @{thm UNIV_eq_I} THEN' rtac CollectI) 1 THEN
    REPEAT_DETERM (TRY (rtac conjI 1) THEN rtac @{thm subset_UNIV} 1));

fun mk_killN_in_bd_tac n nontrivial_killN_in in_alt in_bd bd_Card_order bd_Cinfinite bd_Cnotzero =
  (rtac @{thm ordIso_ordLeq_trans} THEN'
  rtac @{thm card_of_ordIso_subst} THEN'
  rtac in_alt THEN'
  rtac ctrans THEN'
  rtac in_bd THEN'
  rtac @{thm ordIso_ordLeq_trans} THEN'
  rtac @{thm cexp_cong1}) 1 THEN
  (if nontrivial_killN_in then
    rtac @{thm ordIso_transitive} 1 THEN
    REPEAT_DETERM_N (n - 1)
      ((rtac @{thm csum_cong1} THEN'
      rtac @{thm ordIso_symmetric} THEN'
      rtac @{thm csum_assoc} THEN'
      rtac @{thm ordIso_transitive}) 1) THEN
    (rtac @{thm ordIso_refl} THEN'
    rtac @{thm Card_order_csum} THEN'
    rtac @{thm ordIso_transitive} THEN'
    rtac @{thm csum_assoc} THEN'
    rtac @{thm ordIso_transitive} THEN'
    rtac @{thm csum_cong1} THEN'
    K (mk_flatten_assoc_tac
      (rtac @{thm ordIso_refl} THEN'
        FIRST' [rtac @{thm card_of_Card_order}, rtac @{thm Card_order_csum}])
      @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_cong}) THEN'
    rtac @{thm ordIso_refl} THEN'
    (rtac @{thm card_of_Card_order} ORELSE' rtac @{thm Card_order_csum})) 1
  else all_tac) THEN
  (rtac @{thm csum_com} THEN'
  rtac bd_Card_order THEN'
  rtac disjI1 THEN'
  rtac @{thm csum_Cnotzero2} THEN'
  rtac @{thm ctwo_Cnotzero} THEN'
  rtac disjI1 THEN'
  rtac @{thm csum_Cnotzero2} THEN'
  TRY o rtac @{thm csum_Cnotzero1} THEN'
  rtac @{thm Cnotzero_UNIV} THEN'
  rtac @{thm ordLeq_ordIso_trans} THEN'
  rtac @{thm cexp_mono1} THEN'
  rtac ctrans THEN'
  rtac @{thm csum_mono2} THEN'
  rtac @{thm ordLeq_cprod1} THEN'
  (rtac @{thm card_of_Card_order} ORELSE' rtac @{thm Card_order_csum}) THEN'
  rtac bd_Cnotzero THEN'
  rtac @{thm csum_cexp'} THEN'
  rtac @{thm Cinfinite_cprod2} THEN'
  TRY o rtac @{thm csum_Cnotzero1} THEN'
  rtac @{thm Cnotzero_UNIV} THEN'
  rtac bd_Cinfinite THEN'
  ((rtac @{thm Card_order_ctwo} THEN' rtac @{thm ordLeq_refl}) ORELSE'
    (rtac @{thm Card_order_csum} THEN' rtac @{thm ordLeq_csum2})) THEN'
  rtac @{thm Card_order_ctwo} THEN'
  rtac disjI1 THEN'
  rtac @{thm csum_Cnotzero2} THEN'
  TRY o rtac @{thm csum_Cnotzero1} THEN'
  rtac @{thm Cnotzero_UNIV} THEN'
  rtac bd_Card_order THEN'
  rtac @{thm cexp_cprod_ordLeq} THEN'
  TRY o rtac @{thm csum_Cnotzero2} THEN'
  rtac @{thm ctwo_Cnotzero} THEN'
  rtac @{thm Cinfinite_cprod2} THEN'
  TRY o rtac @{thm csum_Cnotzero1} THEN'
  rtac @{thm Cnotzero_UNIV} THEN'
  rtac bd_Cinfinite THEN'
  rtac bd_Cnotzero THEN'
  rtac @{thm ordLeq_cprod2} THEN'
  TRY o rtac @{thm csum_Cnotzero1} THEN'
  rtac @{thm Cnotzero_UNIV} THEN'
  rtac bd_Card_order) 1;



(* Lift operation *)

val empty_natural_tac = rtac @{thm empty_natural} 1;

fun mk_liftN_set_bd_tac bd_Card_order = (rtac @{thm Card_order_empty} THEN' rtac bd_Card_order) 1;

val liftN_in_alt_tac =
  ((rtac @{thm Collect_cong} THEN' rtac @{thm iffI}) 1 THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE' atac) 1)) THEN
  REPEAT_DETERM (CHANGED (etac conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac conjI ORELSE'
    rtac conjI THEN' rtac @{thm empty_subsetI}) 1)) THEN
  (rtac @{thm empty_subsetI} ORELSE' atac) 1) ORELSE
  ((rtac sym THEN' rtac @{thm UNIV_eq_I} THEN' rtac CollectI) 1 THEN
    REPEAT_DETERM (TRY (rtac conjI 1) THEN rtac @{thm empty_subsetI} 1));

fun mk_liftN_in_bd_tac n in_alt in_bd bd_Card_order =
  (rtac @{thm ordIso_ordLeq_trans} THEN'
  rtac @{thm card_of_ordIso_subst} THEN'
  rtac in_alt THEN'
  rtac ctrans THEN'
  rtac in_bd THEN'
  rtac @{thm cexp_mono1}) 1 THEN
  ((rtac @{thm csum_mono1} 1 THEN
  REPEAT_DETERM_N (n - 1)
    ((rtac ctrans THEN'
    rtac @{thm ordLeq_csum2} THEN'
    (rtac @{thm Card_order_csum} ORELSE' rtac @{thm card_of_Card_order})) 1) THEN
  (rtac @{thm ordLeq_csum2} THEN'
  (rtac @{thm Card_order_csum} ORELSE' rtac @{thm card_of_Card_order})) 1) ORELSE
  (rtac @{thm ordLeq_csum2} THEN' rtac @{thm Card_order_ctwo}) 1) THEN
  (rtac disjI1 THEN' TRY o rtac @{thm csum_Cnotzero2} THEN' rtac @{thm ctwo_Cnotzero}
   THEN' rtac bd_Card_order) 1;



(* Permute operation *)

fun mk_permute_in_alt_tac src dest =
  (rtac @{thm Collect_cong} THEN'
  mk_rotate_eq_tac (rtac refl) trans @{thm conj_assoc} @{thm conj_commute} @{thm conj_cong}
    dest src) 1;

fun mk_permute_in_bd_tac src dest in_alt in_bd bd_Card_order =
  (rtac @{thm ordIso_ordLeq_trans} THEN'
  rtac @{thm card_of_ordIso_subst} THEN'
  rtac in_alt THEN'
  rtac @{thm ordLeq_ordIso_trans} THEN'
  rtac in_bd THEN'
  rtac @{thm cexp_cong1} THEN'
  rtac @{thm csum_cong1} THEN'
  mk_rotate_eq_tac
    (rtac @{thm ordIso_refl} THEN'
      FIRST' [rtac @{thm card_of_Card_order}, rtac @{thm Card_order_csum}])
    @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_com} @{thm csum_cong}
    src dest THEN'
  rtac bd_Card_order THEN'
  rtac disjI1 THEN'
  TRY o rtac @{thm csum_Cnotzero2} THEN'
  rtac @{thm ctwo_Cnotzero} THEN'
  rtac disjI1 THEN'
  TRY o rtac @{thm csum_Cnotzero2} THEN'
  rtac @{thm ctwo_Cnotzero}) 1;

fun mk_map_wpull_tac comp_in_alt inner_map_wpulls outer_map_wpull =
  (rtac (@{thm wpull_cong} OF (replicate 3 comp_in_alt)) THEN' rtac outer_map_wpull) 1 THEN
  WRAP (fn thm => rtac thm 1 THEN REPEAT_DETERM (atac 1)) (K all_tac) inner_map_wpulls all_tac THEN
  TRY (REPEAT_DETERM (atac 1 ORELSE rtac @{thm wpull_id} 1));

fun mk_simple_wit_tac wit_thms = ALLGOALS (atac ORELSE' eresolve_tac (@{thm emptyE} :: wit_thms));

end;
