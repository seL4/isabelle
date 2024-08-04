(*  Title:      HOL/Tools/Transfer/transfer_bnf.ML
    Author:     Ondrej Kuncar, TU Muenchen

Setup for Transfer for types that are BNF.
*)

signature TRANSFER_BNF =
sig
  exception NO_PRED_DATA of unit

  val base_name_of_bnf: BNF_Def.bnf -> binding
  val type_name_of_bnf: BNF_Def.bnf -> string
  val lookup_defined_pred_data: Proof.context -> string -> Transfer.pred_data
  val bnf_only_type_ctr: (BNF_Def.bnf -> 'a -> 'a) -> BNF_Def.bnf -> 'a -> 'a
end

structure Transfer_BNF : TRANSFER_BNF =
struct

open BNF_Util
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar

exception NO_PRED_DATA of unit

(* util functions *)

fun base_name_of_bnf bnf = Binding.name (Binding.name_of (name_of_bnf bnf))

fun mk_Domainp P =
  let
    val PT = fastype_of P
    val argT = hd (binder_types PT)
  in
    Const (\<^const_name>\<open>Domainp\<close>, PT --> argT --> HOLogic.boolT) $ P
  end

fun type_name_of_bnf bnf = dest_Type_name (T_of_bnf bnf)

fun bnf_only_type_ctr f bnf = if is_Type (T_of_bnf bnf) then f bnf else I

fun bnf_of_fp_sugar (fp_sugar:fp_sugar) = nth (#bnfs (#fp_res fp_sugar)) (#fp_res_index fp_sugar)

fun fp_sugar_only_type_ctr f fp_sugars =
  (case filter (is_Type o T_of_bnf o bnf_of_fp_sugar) fp_sugars of
    [] => I
  | fp_sugars' => f fp_sugars')

(* relation constraints - bi_total & co. *)

fun mk_relation_constraint name arg =
  (Const (name, fastype_of arg --> HOLogic.boolT)) $ arg

fun side_constraint_tac bnf constr_defs ctxt =
  let
    val thms = constr_defs @ map mk_sym [rel_eq_of_bnf bnf, rel_conversep_of_bnf bnf,
      rel_OO_of_bnf bnf]
  in
    SELECT_GOAL (Local_Defs.unfold0_tac ctxt thms) THEN' rtac ctxt (rel_mono_of_bnf bnf)
      THEN_ALL_NEW assume_tac ctxt
  end

fun bi_constraint_tac constr_iff sided_constr_intros ctxt =
  SELECT_GOAL (Local_Defs.unfold0_tac ctxt [constr_iff]) THEN'
    CONJ_WRAP' (fn thm => rtac ctxt thm THEN_ALL_NEW
      (REPEAT_DETERM o etac ctxt conjE THEN' assume_tac ctxt)) sided_constr_intros

fun generate_relation_constraint_goal ctxt bnf constraint_def =
  let
    val constr_name =
      constraint_def |> Thm.prop_of |> HOLogic.dest_Trueprop |> fst o HOLogic.dest_eq
      |> head_of |> dest_Const_name
    val live = live_of_bnf bnf
    val (((As, Bs), Ds), ctxt') = ctxt
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees' (map Type.sort_of_atyp (deads_of_bnf bnf))

    val relator = mk_rel_of_bnf Ds As Bs bnf
    val relsT = map2 mk_pred2T As Bs
    val (args, ctxt'') = Ctr_Sugar_Util.mk_Frees "R" relsT ctxt'
    val concl = HOLogic.mk_Trueprop (mk_relation_constraint constr_name (list_comb (relator, args)))
    val assms = map (HOLogic.mk_Trueprop o (mk_relation_constraint constr_name)) args
    val goal = Logic.list_implies (assms, concl)
  in
    (goal, ctxt'')
  end

fun prove_relation_side_constraint ctxt bnf constraint_def =
  let
    val (goal, ctxt') = generate_relation_constraint_goal ctxt bnf constraint_def
  in
    Goal.prove_sorry ctxt' [] [] goal (fn {context = goal_ctxt, ...} =>
      side_constraint_tac bnf [constraint_def] goal_ctxt 1)
    |> Thm.close_derivation \<^here>
    |> singleton (Variable.export ctxt' ctxt)
    |> Drule.zero_var_indexes
  end

fun prove_relation_bi_constraint ctxt bnf constraint_def side_constraints =
  let
    val (goal, ctxt') = generate_relation_constraint_goal ctxt bnf constraint_def
  in
    Goal.prove_sorry ctxt' [] [] goal (fn {context = goal_ctxt, ...} =>
      bi_constraint_tac constraint_def side_constraints goal_ctxt 1)
    |> Thm.close_derivation \<^here>
    |> singleton (Variable.export ctxt' ctxt)
    |> Drule.zero_var_indexes
  end

val defs =
 [("left_total_rel", @{thm left_total_alt_def}), ("right_total_rel", @{thm right_total_alt_def}),
  ("left_unique_rel", @{thm left_unique_alt_def}), ("right_unique_rel", @{thm right_unique_alt_def})]

fun prove_relation_constraints bnf ctxt =
  let
    val transfer_attr = @{attributes [transfer_rule]}
    val Tname = base_name_of_bnf bnf

    val defs = map (apsnd (prove_relation_side_constraint ctxt bnf)) defs
    val bi_total = prove_relation_bi_constraint ctxt bnf @{thm bi_total_alt_def}
      [snd (nth defs 0), snd (nth defs 1)]
    val bi_unique = prove_relation_bi_constraint ctxt bnf @{thm bi_unique_alt_def}
      [snd (nth defs 2), snd (nth defs 3)]
    val defs = ("bi_total_rel", bi_total) :: ("bi_unique_rel", bi_unique) :: defs
  in
    maps (fn (a, thm) => [((Binding.qualify_name true Tname a, []), [([thm], transfer_attr)])]) defs
  end

(* relator_eq *)

fun relator_eq bnf =
  [(Binding.empty_atts, [([rel_eq_of_bnf bnf], @{attributes [relator_eq]})])]

(* transfer rules *)

fun bnf_transfer_rules bnf =
  let
    val transfer_rules = map_transfer_of_bnf bnf :: pred_transfer_of_bnf bnf
      :: rel_transfer_of_bnf bnf :: set_transfer_of_bnf bnf
    val transfer_attr = @{attributes [transfer_rule]}
  in
    map (fn thm => (Binding.empty_atts, [([thm],transfer_attr)])) transfer_rules
  end

(* Domainp theorem for predicator *)

fun Domainp_tac bnf pred_def ctxt =
  let
    val n = live_of_bnf bnf
    val set_map's = set_map_of_bnf bnf
  in
    EVERY' [rtac ctxt ext, SELECT_GOAL (Local_Defs.unfold0_tac ctxt [@{thm Domainp.simps},
        in_rel_of_bnf bnf, pred_def]), rtac ctxt iffI,
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE, CollectE], hyp_subst_tac ctxt,
        CONJ_WRAP' (fn set_map => EVERY' [rtac ctxt ballI, dtac ctxt (set_map RS equalityD1 RS set_mp),
          etac ctxt imageE, dtac ctxt set_rev_mp, assume_tac ctxt,
          REPEAT_DETERM o eresolve_tac ctxt [CollectE, @{thm case_prodE}],
          hyp_subst_tac ctxt, rtac ctxt @{thm iffD2[OF arg_cong2[of _ _ _ _ Domainp, OF refl fst_conv]]},
          etac ctxt @{thm DomainPI}]) set_map's,
        REPEAT_DETERM o etac ctxt conjE,
        REPEAT_DETERM o resolve_tac ctxt [exI, (refl RS conjI), rotate_prems 1 conjI],
        rtac ctxt refl, rtac ctxt (box_equals OF [map_cong0_of_bnf bnf, map_comp_of_bnf bnf RS sym,
          map_id_of_bnf bnf]),
        REPEAT_DETERM_N n o (EVERY' [rtac ctxt @{thm box_equals[OF _ sym[OF o_apply] sym[OF id_apply]]},
          rtac ctxt @{thm fst_conv}]), rtac ctxt CollectI,
        CONJ_WRAP' (fn set_map => EVERY' [rtac ctxt (set_map RS @{thm ord_eq_le_trans}),
          REPEAT_DETERM o resolve_tac ctxt [@{thm image_subsetI}, CollectI, @{thm case_prodI}],
          dtac ctxt (rotate_prems 1 bspec), assume_tac ctxt,
          etac ctxt @{thm DomainpE}, etac ctxt @{thm someI}]) set_map's
      ]
  end

fun prove_Domainp_rel ctxt bnf pred_def =
  let
    val live = live_of_bnf bnf
    val (((As, Bs), Ds), ctxt') = ctxt
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees' (map Type.sort_of_atyp (deads_of_bnf bnf))

    val relator = mk_rel_of_bnf Ds As Bs bnf
    val relsT = map2 mk_pred2T As Bs
    val (args, ctxt'') = Ctr_Sugar_Util.mk_Frees "R" relsT ctxt'
    val lhs = mk_Domainp (list_comb (relator, args))
    val rhs = Term.list_comb (mk_pred_of_bnf Ds As bnf, map mk_Domainp args)
    val goal = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop
  in
    Goal.prove_sorry ctxt'' [] [] goal (fn {context = goal_ctxt, ...} =>
      Domainp_tac bnf pred_def goal_ctxt 1)
    |> Thm.close_derivation \<^here>
    |> singleton (Variable.export ctxt'' ctxt)
    |> Drule.zero_var_indexes
  end

fun predicator bnf lthy =
  let
    val pred_def = pred_set_of_bnf bnf
    val Domainp_rel = prove_Domainp_rel lthy bnf pred_def
    val rel_eq_onp = rel_eq_onp_of_bnf bnf
    val Domainp_rel_thm_name = Binding.qualify_name true (base_name_of_bnf bnf) "Domainp_rel"
    val pred_data = Transfer.mk_pred_data pred_def rel_eq_onp []
    val type_name = type_name_of_bnf bnf
    val relator_domain_attr = @{attributes [relator_domain]}
    val notes = [((Domainp_rel_thm_name, []), [([Domainp_rel], relator_domain_attr)])]
  in
    lthy
    |> Local_Theory.notes notes
    |> snd
    |> Local_Theory.declaration {syntax = false, pervasive = true, pos = \<^here>}
      (fn phi => Transfer.update_pred_data type_name (Transfer.morph_pred_data phi pred_data))
  end

(* BNF interpretation *)

fun transfer_bnf_interpretation bnf lthy =
  let
    val dead = dead_of_bnf bnf
    val constr_notes = if dead > 0 then [] else prove_relation_constraints bnf lthy
    val relator_eq_notes = if dead > 0 then [] else relator_eq bnf
    val transfer_rule_notes = if dead > 0 then [] else bnf_transfer_rules bnf
  in
    lthy
    |> Local_Theory.notes (constr_notes @ relator_eq_notes @ transfer_rule_notes)
    |> snd
    |> predicator bnf
  end

val _ =
  Theory.setup
    (bnf_interpretation transfer_plugin (bnf_only_type_ctr transfer_bnf_interpretation))

(* simplification rules for the predicator *)

fun lookup_defined_pred_data ctxt name =
  case Transfer.lookup_pred_data ctxt name of
    SOME data => data
  | NONE => raise NO_PRED_DATA ()


(* fp_sugar interpretation *)

fun fp_sugar_transfer_rules (fp_sugar:fp_sugar) =
  let
    val fp_ctr_sugar = #fp_ctr_sugar fp_sugar
    val transfer_rules = #ctr_transfers fp_ctr_sugar @ #case_transfers fp_ctr_sugar
      @ #disc_transfers fp_ctr_sugar @ #sel_transfers fp_ctr_sugar
      @ these (Option.map #co_rec_transfers (#fp_co_induct_sugar fp_sugar))
    val transfer_attr = @{attributes [transfer_rule]}
  in
    map (fn thm => (Binding.empty_atts, [([thm], transfer_attr)])) transfer_rules
  end

fun register_pred_injects fp_sugar lthy =
  let
    val pred_injects = #pred_injects (#fp_bnf_sugar fp_sugar)
    val type_name = type_name_of_bnf (#fp_bnf fp_sugar)
    val pred_data = lookup_defined_pred_data lthy type_name
      |> Transfer.update_pred_simps pred_injects
  in
    lthy
    |> Local_Theory.declaration {syntax = false, pervasive = true, pos = \<^here>}
      (fn phi => Transfer.update_pred_data type_name (Transfer.morph_pred_data phi pred_data))
  end

fun transfer_fp_sugars_interpretation fp_sugar lthy =
  let
    val lthy = register_pred_injects fp_sugar lthy
    val transfer_rules_notes = fp_sugar_transfer_rules fp_sugar
  in
    lthy
    |> Local_Theory.notes transfer_rules_notes
    |> snd
  end

val _ =
  Theory.setup (fp_sugars_interpretation transfer_plugin
    (fp_sugar_only_type_ctr (fold transfer_fp_sugars_interpretation)))

end
