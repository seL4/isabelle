(*  Title:      HOL/Tools/Transfer/transfer_bnf.ML
    Author:     Ondrej Kuncar, TU Muenchen

Setup for Transfer for types that are BNF.
*)

signature TRANSFER_BNF =
sig
  val base_name_of_bnf: BNF_Def.bnf -> binding
  val type_name_of_bnf: BNF_Def.bnf -> string
  val lookup_defined_pred_data: Proof.context -> string -> Transfer.pred_data
  val map_local_theory: (local_theory -> local_theory) -> theory -> theory
  val bnf_only_type_ctr: (BNF_Def.bnf -> 'a -> 'a) -> BNF_Def.bnf -> 'a -> 'a
end

structure Transfer_BNF : TRANSFER_BNF =
struct

open BNF_Util
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar

(* util functions *)

fun base_name_of_bnf bnf = Binding.name (Binding.name_of (name_of_bnf bnf))
fun mk_Frees_free x Ts ctxt = Variable.variant_frees ctxt [] (mk_names (length Ts) x ~~ Ts) |> map Free

fun mk_Domainp P =
  let
    val PT = fastype_of P
    val argT = hd (binder_types PT)
  in
    Const (@{const_name Domainp}, PT --> argT --> HOLogic.boolT) $ P
  end

fun mk_pred pred_def args T =
  let
    val pred_name = pred_def |> prop_of |> HOLogic.dest_Trueprop |> fst o HOLogic.dest_eq 
      |> head_of |> fst o dest_Const
    val argsT = map fastype_of args
  in
    list_comb (Const (pred_name, argsT ---> (T --> HOLogic.boolT)), args)
  end

fun mk_eq_onp arg = 
  let
    val argT = domain_type (fastype_of arg)
  in
    Const (@{const_name eq_onp}, (argT --> HOLogic.boolT) --> argT --> argT --> HOLogic.boolT)
      $ arg
  end

fun subst_conv thm =
  Conv.top_sweep_conv (K (Conv.rewr_conv (safe_mk_meta_eq thm))) @{context}

fun type_name_of_bnf bnf = T_of_bnf bnf |> dest_Type |> fst

fun is_Type (Type _) = true
  | is_Type _ = false

fun map_local_theory f = Named_Target.theory_init #> f #> Local_Theory.exit_global

fun bnf_only_type_ctr f bnf = if is_Type (T_of_bnf bnf) then f bnf else I

fun bnf_of_fp_sugar (fp_sugar:fp_sugar) = nth (#bnfs (#fp_res fp_sugar)) (#fp_res_index fp_sugar)

fun fp_sugar_only_type_ctr f fp_sugars =
  (case filter (is_Type o T_of_bnf o bnf_of_fp_sugar) fp_sugars of
    [] => I
  | fp_sugars' => f fp_sugars')

(* relation constraints - bi_total & co. *)

fun mk_relation_constraint name arg =
  (Const (name, fastype_of arg --> HOLogic.boolT)) $ arg

fun side_constraint_tac bnf constr_defs ctxt i = 
  let
    val thms = constr_defs @ map mk_sym [rel_eq_of_bnf bnf, rel_conversep_of_bnf bnf,
      rel_OO_of_bnf bnf]
  in                
    (SELECT_GOAL (Local_Defs.unfold_tac ctxt thms) THEN' rtac (rel_mono_of_bnf bnf)
      THEN_ALL_NEW atac) i
  end

fun bi_constraint_tac constr_iff sided_constr_intros ctxt i = 
  (SELECT_GOAL (Local_Defs.unfold_tac ctxt [constr_iff]) THEN' 
    CONJ_WRAP' (fn thm => rtac thm THEN_ALL_NEW (REPEAT_DETERM o etac conjE THEN' atac)) sided_constr_intros) i

fun generate_relation_constraint_goal ctxt bnf constraint_def =
  let
    val constr_name = constraint_def |> prop_of |> HOLogic.dest_Trueprop |> fst o HOLogic.dest_eq
      |> head_of |> fst o dest_Const
    val live = live_of_bnf bnf
    val (((As, Bs), Ds), ctxt) = ctxt
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees (dead_of_bnf bnf)
      
    val relator = mk_rel_of_bnf Ds As Bs bnf
    val relsT = map2 mk_pred2T As Bs
    val (args, ctxt) = Ctr_Sugar_Util.mk_Frees "R" relsT ctxt
    val concl = HOLogic.mk_Trueprop (mk_relation_constraint constr_name (list_comb (relator, args)))
    val assms = map (HOLogic.mk_Trueprop o (mk_relation_constraint constr_name)) args
    val goal = Logic.list_implies (assms, concl)
  in
    (goal, ctxt)
  end

fun prove_relation_side_constraint ctxt bnf constraint_def =
  let
    val old_ctxt = ctxt
    val (goal, ctxt) = generate_relation_constraint_goal ctxt bnf constraint_def
    val thm = Goal.prove ctxt [] [] goal 
      (fn {context = ctxt, prems = _} => side_constraint_tac bnf [constraint_def] ctxt 1)
  in
    Drule.zero_var_indexes (singleton (Variable.export ctxt old_ctxt) thm)
  end

fun prove_relation_bi_constraint ctxt bnf constraint_def side_constraints =
  let
    val old_ctxt = ctxt
    val (goal, ctxt) = generate_relation_constraint_goal ctxt bnf constraint_def
    val thm = Goal.prove ctxt [] [] goal 
      (fn {context = ctxt, prems = _} => bi_constraint_tac constraint_def side_constraints ctxt 1)
  in
    Drule.zero_var_indexes (singleton (Variable.export ctxt old_ctxt) thm)
  end

val defs = [("left_total_rel", @{thm left_total_alt_def}), ("right_total_rel", @{thm right_total_alt_def}),
  ("left_unique_rel", @{thm left_unique_alt_def}), ("right_unique_rel", @{thm right_unique_alt_def})]

fun prove_relation_constraints bnf lthy =
  let
    val transfer_attr = @{attributes [transfer_rule]}
    val Tname = base_name_of_bnf bnf
    fun qualify suffix = Binding.qualified true suffix Tname
    
    val defs = map (apsnd (prove_relation_side_constraint lthy bnf)) defs
    val bi_total = prove_relation_bi_constraint lthy bnf @{thm bi_total_alt_def} 
      [snd (nth defs 0), snd (nth defs 1)]
    val bi_unique = prove_relation_bi_constraint lthy bnf @{thm bi_unique_alt_def} 
      [snd (nth defs 2), snd (nth defs 3)]
    val defs = ("bi_total_rel", bi_total) :: ("bi_unique_rel", bi_unique) :: defs
    val notes = maps (fn (name, thm) => [((qualify name, []), [([thm], transfer_attr)])]) defs
  in
    notes
  end

(* relator_eq *)

fun relator_eq bnf =
  [((Binding.empty, []), [([rel_eq_of_bnf bnf], @{attributes [relator_eq]})])]

(* predicator definition and Domainp and eq_onp theorem *)

fun define_pred bnf lthy =
  let
    fun mk_pred_name c = Binding.prefix_name "pred_" c
    val live = live_of_bnf bnf
    val Tname = base_name_of_bnf bnf
    val ((As, Ds), lthy) = lthy
      |> mk_TFrees live
      ||>> mk_TFrees (dead_of_bnf bnf)
    val T = mk_T_of_bnf Ds As bnf
    val sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf
    val argTs = map mk_pred1T As
    val args = mk_Frees_free "P" argTs lthy
    val conjs = map (fn (set, arg) => mk_Ball (set $ Bound 0) arg) (sets ~~ args)
    val rhs = Abs ("x", T, foldr1 HOLogic.mk_conj conjs)
    val pred_name = mk_pred_name Tname
    val headT = argTs ---> (T --> HOLogic.boolT)
    val head = Free (Binding.name_of pred_name, headT)
    val lhs = list_comb (head, args)
    val def = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
    val ((_, (_, pred_def)), lthy) = Specification.definition ((SOME (pred_name, SOME headT, NoSyn)), 
      ((Binding.empty, []), def)) lthy
  in
    (pred_def, lthy)
  end

fun Domainp_tac bnf pred_def ctxt i =
  let
    val n = live_of_bnf bnf
    val set_map's = set_map_of_bnf bnf
  in
    EVERY' [rtac ext, SELECT_GOAL (Local_Defs.unfold_tac ctxt [@{thm Domainp.simps}, 
        in_rel_of_bnf bnf, pred_def]), rtac iffI,
        REPEAT_DETERM o eresolve_tac [exE, conjE, CollectE], hyp_subst_tac ctxt,
        CONJ_WRAP' (fn set_map => EVERY' [rtac ballI, dtac (set_map RS equalityD1 RS set_mp),
          etac imageE, dtac set_rev_mp, atac, REPEAT_DETERM o eresolve_tac [CollectE, @{thm case_prodE}],
          hyp_subst_tac ctxt, rtac @{thm iffD2[OF arg_cong2[of _ _ _ _ Domainp, OF refl fst_conv]]},
          etac @{thm DomainPI}]) set_map's, 
        REPEAT_DETERM o etac conjE, REPEAT_DETERM o resolve_tac [exI, (refl RS conjI), rotate_prems 1 conjI], 
        rtac refl, rtac (box_equals OF [map_cong0_of_bnf bnf, map_comp_of_bnf bnf RS sym,
          map_id_of_bnf bnf]),
        REPEAT_DETERM_N n o (EVERY' [rtac @{thm box_equals[OF _ sym[OF o_apply] sym[OF id_apply]]},
          rtac @{thm fst_conv}]), rtac CollectI,
        CONJ_WRAP' (fn set_map => EVERY' [rtac (set_map RS @{thm ord_eq_le_trans}), 
          REPEAT_DETERM o resolve_tac [@{thm image_subsetI}, CollectI, @{thm case_prodI}],
          dtac (rotate_prems 1 bspec), atac, etac @{thm DomainpE}, etac @{thm someI}]) set_map's
      ] i
  end

fun prove_Domainp_rel ctxt bnf pred_def =
  let
    val live = live_of_bnf bnf
    val old_ctxt = ctxt
    val (((As, Bs), Ds), ctxt) = ctxt
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees (dead_of_bnf bnf)

    val relator = mk_rel_of_bnf Ds As Bs bnf
    val relsT = map2 mk_pred2T As Bs
    val T = mk_T_of_bnf Ds As bnf
    val (args, ctxt) = Ctr_Sugar_Util.mk_Frees "R" relsT ctxt
    val lhs = mk_Domainp (list_comb (relator, args))
    val rhs = mk_pred pred_def (map mk_Domainp args) T
    val goal = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop
    val thm = Goal.prove ctxt [] [] goal 
      (fn {context = ctxt, prems = _} => Domainp_tac bnf pred_def ctxt 1)
  in
    Drule.zero_var_indexes (singleton (Variable.export ctxt old_ctxt) thm)
  end

fun pred_eq_onp_tac bnf pred_def ctxt i =
  (SELECT_GOAL (Local_Defs.unfold_tac ctxt [@{thm eq_onp_Grp}, 
    @{thm Ball_Collect}, pred_def]) THEN' CONVERSION (subst_conv (map_id0_of_bnf bnf RS sym))
  THEN' rtac (rel_Grp_of_bnf bnf)) i

fun prove_rel_eq_onp ctxt bnf pred_def =
  let
    val live = live_of_bnf bnf
    val old_ctxt = ctxt
    val ((As, Ds), ctxt) = ctxt
      |> mk_TFrees live
      ||>> mk_TFrees (dead_of_bnf bnf)
    val T = mk_T_of_bnf Ds As bnf
    val argTs = map mk_pred1T As
    val (args, ctxt) = mk_Frees "P" argTs ctxt
    val relator = mk_rel_of_bnf Ds As As bnf
    val lhs = list_comb (relator, map mk_eq_onp args)
    val rhs = mk_eq_onp (mk_pred pred_def args T)
    val goal = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop
    val thm = Goal.prove ctxt [] [] goal 
      (fn {context = ctxt, prems = _} => pred_eq_onp_tac bnf pred_def ctxt 1)
  in
    Drule.zero_var_indexes (singleton (Variable.export ctxt old_ctxt) thm)
  end

fun predicator bnf lthy =
  let
    val (pred_def, lthy) = define_pred bnf lthy
    val pred_def = Morphism.thm (Local_Theory.target_morphism lthy) pred_def
    val Domainp_rel = prove_Domainp_rel lthy bnf pred_def
    val rel_eq_onp = prove_rel_eq_onp lthy bnf pred_def
    fun qualify defname suffix = Binding.qualified true suffix defname
    val Domainp_rel_thm_name = qualify (base_name_of_bnf bnf) "Domainp_rel"
    val rel_eq_onp_thm_name = qualify (base_name_of_bnf bnf) "rel_eq_onp"
    val pred_data = {rel_eq_onp = rel_eq_onp}
    val type_name = type_name_of_bnf bnf
    val relator_domain_attr = @{attributes [relator_domain]}
    val notes = [((Domainp_rel_thm_name, []), [([Domainp_rel], relator_domain_attr)]),
      ((rel_eq_onp_thm_name, []), [([rel_eq_onp], [])])]
    val lthy = Local_Theory.declaration {syntax = false, pervasive = true}
      (fn phi => Transfer.update_pred_data type_name (Transfer.morph_pred_data phi pred_data)) lthy
  in
    (notes, lthy)
  end

(* BNF interpretation *)

fun transfer_bnf_interpretation bnf lthy =
  let
    val constr_notes = if dead_of_bnf bnf > 0 then []
      else prove_relation_constraints bnf lthy
    val relator_eq_notes = if dead_of_bnf bnf > 0 then [] 
      else relator_eq bnf
    val (pred_notes, lthy) = predicator bnf lthy
  in
    snd (Local_Theory.notes (constr_notes @ relator_eq_notes @ pred_notes) lthy)
  end

val _ = Context.>> (Context.map_theory (bnf_interpretation
  (bnf_only_type_ctr (fn bnf => map_local_theory (transfer_bnf_interpretation bnf)))))

(* simplification rules for the predicator *)

fun lookup_defined_pred_data lthy name =
  case (Transfer.lookup_pred_data lthy name) of
    SOME data => data
    | NONE => (error "lookup_pred_data: something went utterly wrong")

fun prove_pred_inject lthy (fp_sugar:fp_sugar) =
  let
    val involved_types = distinct op= (
        map type_name_of_bnf (#nested_bnfs fp_sugar) 
      @ map type_name_of_bnf (#nesting_bnfs fp_sugar)
      @ map type_name_of_bnf (#bnfs (#fp_res fp_sugar)))
    val eq_onps = map (Transfer.rel_eq_onp o lookup_defined_pred_data lthy) involved_types
    val live = live_of_bnf (bnf_of_fp_sugar fp_sugar)
    val old_lthy = lthy
    val (As, lthy) = mk_TFrees live lthy
    val predTs = map mk_pred1T As
    val (preds, lthy) = mk_Frees "P" predTs lthy
    val args = map mk_eq_onp preds
    val cTs = map (SOME o certifyT lthy) (maps (replicate 2) As)
    val cts = map (SOME o certify lthy) args
    fun get_rhs thm = thm |> concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
    fun is_eqn thm = can get_rhs thm
    val dead_step = @{lemma "x = y \<Longrightarrow> ((a = a) \<and> x) = y" by blast}
    val live_step = @{lemma "x = y \<Longrightarrow> (eq_onp P a a \<and> x) = (P a \<and> y)" by (simp only: eq_onp_same_args)}
    fun rel2pred_massage thm =
      let
        fun pred_eq_onp_conj conjs = List.foldr (fn (conj, thm) => 
          if can HOLogic.dest_eq conj then thm RS dead_step else thm RS live_step) @{thm refl[of True]} conjs
        val conjuncts = if is_eqn thm then thm |> get_rhs |> HOLogic.dest_conj else []
        val kill_True = Local_Defs.unfold lthy [@{thm HOL.simp_thms(21)}]
      in
        thm
        |> Drule.instantiate' cTs cts
        |> Local_Defs.unfold lthy eq_onps
        |> (fn thm => if conjuncts <> [] then @{thm box_equals} 
              OF [thm, @{thm eq_onp_same_args}, pred_eq_onp_conj conjuncts |> kill_True]
            else thm RS (@{thm eq_onp_same_args} RS iffD1))
      end
    val rel_injects = #rel_injects fp_sugar
  in
    rel_injects
    |> map (Local_Defs.unfold lthy [@{thm conj_assoc}])
    |> map rel2pred_massage
    |> Variable.export lthy old_lthy
    |> map Drule.zero_var_indexes
  end

(* fp_sugar interpretation *)

fun transfer_fp_sugar_interpretation fp_sugar lthy =
  let
    val pred_injects = prove_pred_inject lthy fp_sugar
    fun qualify defname suffix = Binding.qualified true suffix defname
    val pred_inject_thm_name = qualify (base_name_of_bnf (bnf_of_fp_sugar fp_sugar)) "pred_inject"
    val simp_attrs = @{attributes [simp]}
  in
    snd (Local_Theory.note ((pred_inject_thm_name, simp_attrs), pred_injects) lthy)
  end

val _ = Context.>> (Context.map_theory (fp_sugar_interpretation (fp_sugar_only_type_ctr
  (fn fp_sugars => map_local_theory (fold transfer_fp_sugar_interpretation fp_sugars)))))

end
