(*  Title:      HOL/Tools/BNF/bnf_comp_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for composition of bounded natural functors.
*)

signature BNF_COMP_TACTICS =
sig
  val mk_comp_bd_card_order_tac: Proof.context -> thm list -> thm -> tactic
  val mk_comp_bd_cinfinite_tac: Proof.context -> thm -> thm -> tactic
  val mk_comp_bd_regularCard_tac: Proof.context -> thm list -> thm -> thm list -> thm -> tactic
  val mk_comp_in_alt_tac: Proof.context -> thm list -> tactic
  val mk_comp_map_comp0_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_comp_map_cong0_tac: Proof.context -> thm list -> thm list -> thm -> thm list -> tactic
  val mk_comp_map_id0_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_comp_set_alt_tac: Proof.context -> thm -> tactic
  val mk_comp_set_bd_tac: Proof.context -> thm -> thm option -> thm -> thm list -> thm list -> tactic
  val mk_comp_set_map0_tac: Proof.context -> thm -> thm -> thm -> thm -> thm list -> tactic
  val mk_comp_wit_tac: Proof.context -> thm list -> thm list -> thm -> thm list -> tactic

  val kill_in_alt_tac: Proof.context -> tactic
  val mk_kill_map_cong0_tac: Proof.context -> int -> int -> thm -> tactic

  val empty_natural_tac: Proof.context -> tactic
  val lift_in_alt_tac: Proof.context -> tactic
  val mk_lift_set_bd_tac: Proof.context -> thm -> tactic

  val mk_permute_in_alt_tac: Proof.context -> ''a list -> ''a list -> tactic

  val mk_le_rel_OO_tac: Proof.context -> thm -> thm -> thm list -> tactic
  val mk_simple_rel_OO_Grp_tac: Proof.context -> thm -> thm -> tactic
  val mk_simple_pred_set_tac: Proof.context -> thm -> thm -> tactic
  val mk_simple_wit_tac: Proof.context -> thm list -> tactic
  val mk_simplified_set_tac: Proof.context -> thm -> tactic
  val bd_ordIso_natLeq_tac: Proof.context -> tactic
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
  rtac ctxt refl 1;

fun mk_comp_map_id0_tac ctxt Gmap_id0 Gmap_cong0 map_id0s =
  EVERY' ([rtac ctxt @{thm ext}, rtac ctxt (Gmap_cong0 RS trans)] @
    map (fn thm => rtac ctxt (thm RS fun_cong)) map_id0s @ [rtac ctxt (Gmap_id0 RS fun_cong)]) 1;

fun mk_comp_map_comp0_tac ctxt Gmap_comp0 Gmap_cong0 map_comp0s =
  EVERY' ([rtac ctxt @{thm ext}, rtac ctxt sym, rtac ctxt trans_o_apply,
    rtac ctxt (Gmap_comp0 RS sym RS comp_eq_dest_lhs RS trans), rtac ctxt Gmap_cong0] @
    map (fn thm => rtac ctxt (thm RS sym RS fun_cong)) map_comp0s) 1;

fun mk_comp_set_map0_tac ctxt set'_eq_set Gmap_comp0 Gmap_cong0 Gset_map0 set_map0s =
  unfold_thms_tac ctxt [set'_eq_set] THEN
  EVERY' ([rtac ctxt @{thm ext}] @
    replicate 3 (rtac ctxt trans_o_apply) @
    [rtac ctxt (arg_cong_Union RS trans),
     rtac ctxt (@{thm arg_cong2[of _ _ _ _ collect, OF refl]} RS trans),
     rtac ctxt (Gmap_comp0 RS sym RS comp_eq_dest_lhs RS trans),
     rtac ctxt Gmap_cong0] @
     map (fn thm => rtac ctxt (thm RS fun_cong)) set_map0s @
     [rtac ctxt (Gset_map0 RS comp_eq_dest_lhs), rtac ctxt sym, rtac ctxt trans_o_apply,
     rtac ctxt trans_image_cong_o_apply, rtac ctxt trans_image_cong_o_apply,
     rtac ctxt (@{thm image_cong} OF [Gset_map0 RS comp_eq_dest_lhs RS arg_cong_Union, refl]
       RS trans),
     rtac ctxt @{thm trans[OF comp_eq_dest[OF Union_natural[symmetric]]]}, rtac ctxt arg_cong_Union,
     rtac ctxt @{thm trans[OF comp_eq_dest_lhs[OF image_o_collect[symmetric]]]},
     rtac ctxt @{thm fun_cong[OF arg_cong[of _ _ collect]]}] @
     [REPEAT_DETERM_N (length set_map0s) o EVERY' [rtac ctxt @{thm trans[OF image_insert]},
        rtac ctxt @{thm arg_cong2[of _ _ _ _ insert]}, rtac ctxt @{thm ext},
        rtac ctxt trans_o_apply, rtac ctxt trans_image_cong_o_apply,
        rtac ctxt @{thm trans[OF image_image]}, rtac ctxt @{thm sym[OF trans[OF o_apply]]},
        rtac ctxt @{thm image_cong[OF refl o_apply]}],
     rtac ctxt @{thm image_empty}]) 1;

fun mk_comp_map_cong0_tac ctxt set'_eq_sets comp_set_alts map_cong0 map_cong0s =
  let
     val n = length comp_set_alts;
  in
    unfold_thms_tac ctxt set'_eq_sets THEN
    (if n = 0 then rtac ctxt refl 1
    else rtac ctxt map_cong0 1 THEN
      EVERY' (map_index (fn (i, map_cong0) =>
        rtac ctxt map_cong0 THEN' EVERY' (map_index (fn (k, set_alt) =>
          EVERY' [select_prem_tac ctxt n (dtac ctxt @{thm meta_spec}) (k + 1), etac ctxt meta_mp,
            rtac ctxt (@{thm equalityD2} RS set_mp), rtac ctxt (set_alt RS fun_cong RS trans),
            rtac ctxt trans_o_apply, rtac ctxt (@{thm collect_def} RS arg_cong_Union),
            rtac ctxt @{thm UnionI}, rtac ctxt @{thm UN_I},
            REPEAT_DETERM_N i o rtac ctxt @{thm insertI2}, rtac ctxt @{thm insertI1},
            rtac ctxt (o_apply RS @{thm equalityD2} RS set_mp), etac ctxt @{thm imageI}, assume_tac ctxt])
          comp_set_alts))
      map_cong0s) 1)
  end;

fun mk_comp_bd_card_order_tac ctxt Fbd_card_orders Gbd_card_order =
  rtac ctxt @{thm natLeq_card_order} 1 ORELSE
  let
    val (card_orders, last_card_order) = split_last Fbd_card_orders;
    fun gen_before thm = rtac ctxt @{thm card_order_csum} THEN' rtac ctxt thm;
  in
    (rtac ctxt @{thm card_order_cprod} THEN'
    WRAP' gen_before (K (K all_tac)) card_orders (rtac ctxt last_card_order) THEN'
    rtac ctxt Gbd_card_order) 1
  end;

fun mk_comp_bd_cinfinite_tac ctxt Fbd_cinfinite Gbd_cinfinite =
  (rtac ctxt @{thm natLeq_cinfinite} ORELSE'
   rtac ctxt @{thm cinfinite_cprod} THEN'
   ((K (TRY ((rtac ctxt @{thm cinfinite_csum} THEN' rtac ctxt disjI1) 1)) THEN'
     ((rtac ctxt @{thm cinfinite_csum} THEN' rtac ctxt disjI1 THEN' rtac ctxt Fbd_cinfinite) ORELSE'
      rtac ctxt Fbd_cinfinite)) ORELSE'
    rtac ctxt Fbd_cinfinite) THEN'
   rtac ctxt Gbd_cinfinite) 1;

fun mk_comp_bd_regularCard_tac ctxt Fbd_regularCards Gbd_regularCard Fbd_Cinfinites Gbd_Cinfinite =
  rtac ctxt @{thm regularCard_natLeq} 1 ORELSE
  EVERY1 [
    rtac ctxt @{thm regularCard_cprod},
    resolve_tac ctxt (Fbd_Cinfinites) ORELSE'
    ((TRY o rtac ctxt @{thm Cinfinite_csum1}) THEN'
    resolve_tac ctxt (Fbd_Cinfinites)),
    rtac ctxt Gbd_Cinfinite,
    REPEAT_DETERM o EVERY' [
      rtac ctxt @{thm regularCard_csum},
      resolve_tac ctxt Fbd_Cinfinites,
      resolve_tac ctxt (Fbd_Cinfinites) ORELSE'
      ((TRY o rtac ctxt @{thm Cinfinite_csum1}) THEN'
      resolve_tac ctxt (Fbd_Cinfinites)),
      resolve_tac ctxt Fbd_regularCards
    ],
    resolve_tac ctxt Fbd_regularCards,
    rtac ctxt Gbd_regularCard
  ];

fun mk_comp_set_bd_tac ctxt set'_eq_set bd_ordIso_natLeq_opt comp_set_alt Gset_Fset_bds Gbd_Fbd_Cinfinites =
  let
    val (bds, last_bd) = split_last Gset_Fset_bds;
    fun gen_before bd = EVERY' [
      rtac ctxt @{thm ordLeq_ordLess_trans},
      rtac ctxt @{thm Un_csum},
      rtac ctxt @{thm csum_mono_strict},
      rtac ctxt @{thm card_of_Card_order},
      rtac ctxt @{thm card_of_Card_order},
      resolve_tac ctxt Gbd_Fbd_Cinfinites,
      defer_tac,
      rtac ctxt bd
    ];
  in
    (case bd_ordIso_natLeq_opt of
      SOME thm => rtac ctxt (thm RSN (2, @{thm ordLess_ordIso_trans})) 1
    | NONE => all_tac) THEN
    unfold_thms_tac ctxt [set'_eq_set, comp_set_alt] THEN
    rtac ctxt @{thm comp_set_bd_Union_o_collect_strict} 1 THEN
    unfold_thms_tac ctxt @{thms Union_image_insert Union_image_empty Union_Un_distrib o_apply} THEN
    EVERY1 [
      rtac ctxt @{thm ordLess_ordLeq_trans},
      WRAP' gen_before (K (K all_tac)) bds (rtac ctxt last_bd),
      rtac ctxt @{thm ordIso_imp_ordLeq},
      REPEAT_DETERM_N (length Gset_Fset_bds - 1) o EVERY' [
        rtac ctxt @{thm ordIso_transitive},
        REPEAT_DETERM o (rtac ctxt @{thm cprod_csum_distrib1} ORELSE' rtac ctxt @{thm csum_cong2})
      ],
      rtac ctxt @{thm cprod_com},
      REPEAT_DETERM o EVERY' [
        TRY o rtac ctxt @{thm Cinfinite_csum1},
        resolve_tac ctxt Gbd_Fbd_Cinfinites
      ]
    ]
  end;

val comp_in_alt_thms = @{thms o_apply collect_def image_insert image_empty Union_insert UN_insert
  UN_empty Union_empty Un_empty_right Union_Un_distrib Un_subset_iff conj_subset_def UN_image_subset
  conj_assoc};

fun mk_comp_in_alt_tac ctxt comp_set_alts =
  unfold_thms_tac ctxt comp_set_alts THEN
  unfold_thms_tac ctxt comp_in_alt_thms THEN
  unfold_thms_tac ctxt @{thms set_eq_subset} THEN
  rtac ctxt conjI 1 THEN
  REPEAT_DETERM (
    rtac ctxt @{thm subsetI} 1 THEN
    unfold_thms_tac ctxt @{thms mem_Collect_eq Ball_def} THEN
    (REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
     REPEAT_DETERM (CHANGED ((
       (rtac ctxt conjI THEN' (assume_tac ctxt ORELSE' rtac ctxt subset_UNIV)) ORELSE'
       assume_tac ctxt ORELSE'
       (rtac ctxt subset_UNIV)) 1)) ORELSE rtac ctxt subset_UNIV 1));

val comp_wit_thms = @{thms Union_empty_conv o_apply collect_def UN_insert UN_empty Un_empty_right
  Union_image_insert Union_image_empty};

fun mk_comp_wit_tac ctxt set'_eq_sets Gwit_thms collect_set_map Fwit_thms =
  unfold_thms_tac ctxt set'_eq_sets THEN
  ALLGOALS (dtac ctxt @{thm in_Union_o_assoc}) THEN
  unfold_thms_tac ctxt [collect_set_map] THEN
  unfold_thms_tac ctxt comp_wit_thms THEN
  REPEAT_DETERM ((assume_tac ctxt ORELSE'
    REPEAT_DETERM o eresolve_tac ctxt @{thms UnionE UnE} THEN'
    etac ctxt @{thm imageE} THEN' TRY o dresolve_tac ctxt Gwit_thms THEN'
    (etac ctxt FalseE ORELSE'
    hyp_subst_tac ctxt THEN'
    dresolve_tac ctxt Fwit_thms THEN'
    (etac ctxt FalseE ORELSE' assume_tac ctxt))) 1);


(* Kill operation *)

fun mk_kill_map_cong0_tac ctxt n m map_cong0 =
  (rtac ctxt map_cong0 THEN' EVERY' (replicate n (rtac ctxt refl)) THEN'
    EVERY' (replicate m (Goal.assume_rule_tac ctxt))) 1;

fun kill_in_alt_tac ctxt =
  ((rtac ctxt @{thm Collect_cong} THEN' rtac ctxt iffI) 1 THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE'
    rtac ctxt conjI THEN' rtac ctxt subset_UNIV) 1)) THEN
  (rtac ctxt subset_UNIV ORELSE' assume_tac ctxt) 1 THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE' assume_tac ctxt) 1))) ORELSE
  ((rtac ctxt @{thm UNIV_eq_I} THEN' rtac ctxt @{thm CollectI}) 1 THEN
    REPEAT_DETERM (TRY (rtac ctxt conjI 1) THEN rtac ctxt subset_UNIV 1));


(* Lift operation *)

fun empty_natural_tac ctxt = rtac ctxt @{thm empty_natural} 1;

fun mk_lift_set_bd_tac ctxt bd_Cinfinite =
  (rtac ctxt @{thm Cinfinite_gt_empty} THEN' rtac ctxt bd_Cinfinite) 1;

fun lift_in_alt_tac ctxt =
  ((rtac ctxt @{thm Collect_cong} THEN' rtac ctxt iffI) 1 THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE' assume_tac ctxt) 1)) THEN
  REPEAT_DETERM (CHANGED (etac ctxt conjE 1)) THEN
  REPEAT_DETERM (CHANGED ((etac ctxt conjI ORELSE'
    rtac ctxt conjI THEN' rtac ctxt @{thm empty_subsetI}) 1)) THEN
  (rtac ctxt @{thm empty_subsetI} ORELSE' assume_tac ctxt) 1) ORELSE
  ((rtac ctxt sym THEN' rtac ctxt @{thm UNIV_eq_I} THEN' rtac ctxt @{thm CollectI}) 1 THEN
    REPEAT_DETERM (TRY (rtac ctxt conjI 1) THEN rtac ctxt @{thm empty_subsetI} 1));


(* Permute operation *)

fun mk_permute_in_alt_tac ctxt src dest =
  (rtac ctxt @{thm Collect_cong} THEN'
  mk_rotate_eq_tac ctxt (rtac ctxt refl) trans @{thm conj_assoc} @{thm conj_commute}
    @{thm conj_cong} dest src) 1;


(* Miscellaneous *)

fun mk_le_rel_OO_tac ctxt outer_le_rel_OO outer_rel_mono inner_le_rel_OOs =
  HEADGOAL (EVERY' (map (rtac ctxt) (@{thm order_trans} :: outer_le_rel_OO :: outer_rel_mono ::
    inner_le_rel_OOs)));

fun mk_simple_rel_OO_Grp_tac ctxt rel_OO_Grp in_alt_thm =
  HEADGOAL (rtac ctxt (trans OF [rel_OO_Grp, in_alt_thm RS @{thm OO_Grp_cong} RS sym]));

fun mk_simple_pred_set_tac ctxt pred_set in_alt_thm =
  HEADGOAL (rtac ctxt (pred_set RS trans)) THEN
  unfold_thms_tac ctxt @{thms Ball_Collect UNIV_def} THEN
  HEADGOAL (rtac ctxt (unfold_thms ctxt @{thms UNIV_def} in_alt_thm RS @{thm Collect_inj} RS sym));

fun mk_simple_wit_tac ctxt wit_thms =
  ALLGOALS (assume_tac ctxt ORELSE' eresolve_tac ctxt (@{thm emptyE} :: wit_thms));

val csum_thms =
  @{thms csum_cong1 csum_cong2 csum_cong  csum_dup[OF natLeq_cinfinite natLeq_Card_order]};
val cprod_thms =
  @{thms cprod_cong1 cprod_cong2 cprod_cong cprod_dup[OF natLeq_cinfinite natLeq_Card_order]};

val simplified_set_simps =
  @{thms collect_def[abs_def] UN_insert UN_empty Un_empty_right Un_empty_left
    o_def Union_Un_distrib UN_empty2 UN_singleton id_bnf_def};

fun mk_simplified_set_tac ctxt collect_set_map =
  unfold_thms_tac ctxt (collect_set_map :: @{thms comp_assoc}) THEN
  unfold_thms_tac ctxt simplified_set_simps THEN rtac ctxt refl 1;

fun bd_ordIso_natLeq_tac ctxt =
  HEADGOAL (REPEAT_DETERM o resolve_tac ctxt
    (@{thm ordIso_refl[OF natLeq_Card_order]} :: csum_thms @ cprod_thms));

end;
