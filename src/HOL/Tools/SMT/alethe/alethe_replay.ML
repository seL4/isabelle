(*  Title:      HOL/Tools/SMT/alethe/alethe_replay.ML
    Author:     Mathias Fleury, JKU, University of Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof parsing and replay for alethe.
*)

signature ALETHE_REPLAY =
sig
  val replay: string -> (string -> Proof.context -> thm list -> term list -> term list -> term -> tactic_args option -> thm) ->
     Proof.context -> SMT_Translate.replay_data -> string list -> thm
end;

structure Alethe_Replay: ALETHE_REPLAY =
struct

open SMT_Config

fun debug_msg ctxt = alethe_debug_msg ctxt "alethe_replay"
fun debug_cond_msg ctxt cond verbosity msg = (if cond then debug_msg ctxt verbosity msg else ())

(** Util **)

fun subst_only_free pairs =
  let
     fun substf u =
        (case Termtab.lookup pairs u of
          SOME u' => u'
        | NONE =>
          (case u of
            (Abs(a,T,t)) => Abs(a, T, substf t)
          | (t$u') => substf t $ substf u'
          | u => u))
  in (not (Termtab.is_empty pairs)) ? substf end;

fun subst_free_if_nonempty concl_transformation =
  (not (null concl_transformation)) ? Term.subst_free concl_transformation

fun add_box_symbols ctxt t ct =
  let
    fun add_alethe_Box_after_all_negations_conv ctxt ct =
          (case Thm.term_of ct of
            @{term Not} $ _ =>
              Conv.try_conv (Conv.arg_conv (add_alethe_Box_after_all_negations_conv ctxt) )
          | _ =>
              Conv.try_conv (Conv.top_conv (K (Conv.rewr_conv @{thm SMT.alethe_Box})) ctxt)) ct

    fun add_box_symbols @{term True} ct =
          (case Thm.term_of ct of
            @{term Not} $ _ =>
              Conv.try_conv (Conv.arg_conv (add_alethe_Box_after_all_negations_conv ctxt))
          | _ =>
              Conv.try_conv (Conv.top_conv (K (Conv.rewr_conv @{thm SMT.alethe_Box})) ctxt)) ct
      | add_box_symbols (u $ v) ct =
          (Conv.fun_conv (add_box_symbols u)
           then_conv Conv.arg_conv (add_box_symbols v)) ct

      | add_box_symbols _ ct = Conv.all_conv ct

  in
    (* Some terms coming from veriT are not beta-reduced. *)
    ct
    |> (Thm.beta_conversion true then_conv HOLogic.Trueprop_conv (add_box_symbols (HOLogic.dest_Trueprop t)))
  end

(** Replaying **)

fun apply_replay_method f unchanged_prems (prems, prems_as_thms_with_context_assms) step_args
    context_assignments ((prop_skeleton, concl), ctxt) tactic_args keep_proposition_structure =
  let
    val prems1 = unchanged_prems @ map (SMT_Replay.varify ctxt) prems
    val prems2 = prems_as_thms_with_context_assms
      |> (if keep_proposition_structure
         then map (fn (t, thm) => Conv.fconv_rule (add_box_symbols ctxt t) thm)
         else map snd)

    val concl =
      if keep_proposition_structure
      then
        (add_box_symbols ctxt prop_skeleton (Thm.cterm_of ctxt concl)
        |> Thm.prop_of
        |> (fn _ $ s => s))
      else concl
    val _ = debug_msg ctxt high (fn () => \<^print> ("Apply a replay method to solve ((prems1,prems2),concl)", ((prems1,prems2),concl)))
  in (f ctxt (prems1 @ prems2) step_args context_assignments concl tactic_args) end

fun replay_thm solver method_for rewrite_rules ll_defs ctxt assumed unchanged_prems prems prems_as_thms_with_context_assms
    concl_transformation global_transformation step_args context_assignments args
    (Alethe_Node.Alethe_Replay_Node {id, rule, concl, prop_skeleton, ...}) =
  if rule = Alethe_Proof.input_rule then
      (case Symtab.lookup assumed id of
        SOME (_, thm) => thm
      | _ => raise Fail ("assumption " ^ @{make_string} id ^ " not found"))
  else
  let
    val rewrite = let val thy = Proof_Context.theory_of (Simplifier.empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs andalso Alethe_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
      end

    val concl_rewriter = (if Alethe_Proof.keep_app_symbols rule then
          filter (curry Term.could_unify (Thm.concl_of @{thm SMT.fun_app_def}) o Thm.concl_of) rewrite_rules
        else rewrite_rules)

    val post = let val thy = Proof_Context.theory_of (Simplifier.empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy concl_rewriter []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end

    val concl = concl
      |> subst_free_if_nonempty concl_transformation
      |> subst_only_free global_transformation
      |> post

    val _ = debug_msg ctxt high (fn () => \<^print> ("Rewritten atomized conclusion with lambda lifting definitions (ll_defs) and rewrite_rules", concl))

    val args = if rule = Alethe_Proof.refl_rule orelse rule = Alethe_Proof.cong_rule orelse rule = Alethe_Proof.normalized_input_rule
               then SOME (Solver_Name solver)
               else args

    (* The Alethe proof format distinguishes between the propositional structure (cl ...) and the
       disjunction purely from the theory solver. Using that structure reduces the size of the terms
       on some big cvc5 proof, improving performance. *)
    val needs_boxes = Alethe_Proof.keep_proposition_structure rule andalso
      SMT_Config.alethe_use_prop_skeleton ctxt

  in

      apply_replay_method (method_for rule) unchanged_prems
        (prems, prems_as_thms_with_context_assms)
        (map rewrite step_args)
        (map rewrite context_assignments)
        ((prop_skeleton, concl), ctxt)
        args
        needs_boxes
      |> Simplifier.simplify (Simplifier.add_simps (@{thm SMT.alethe_Box_def2} :: rewrite_rules)
          (Simplifier.empty_simpset ctxt))
  end
 | replay_thm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = raise Fail "unreachable code to silence the compiler"



fun replay_theorem_step solver method_for rewrite_rules all_assms ll_defs assumed (inputs : thm list) (all_local_assumptions : thm list)
  (step as Alethe_Node.Alethe_Replay_Node {id, rule, prems = non_skolem_prems, step_args, context_assignments,
     subproof = (fixes, assms, input, subproof), concl, args, prop_skeleton, ...})
  (globally_known_facts, stats, ctxt, concl_transformation, global_transformation) =
  let
    val _ = debug_msg ctxt low (fn () => \<^print> ("Replaying theorem step", id))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("(conclusion, propositional skeleton)", (concl, prop_skeleton)))

    (* Add symbol names from the step's conclusion to context *)
    val ctxt = Variable.variant_fixes [] ctxt
      |> (fn (_, ctxt) => fold Variable.declare_term [SMTLIB_Isar.unskolemize_names ctxt concl] ctxt)

    val (names, sub_ctxt) = Variable.variant_fixes (map fst fixes) ctxt
       ||> fold Variable.declare_term (map Free fixes)
    val _ = debug_cond_msg ctxt (fixes <> []) middle (fn () => \<^print> ("Obtained new variables from the subproof and added their names to a subcontext",(fixes,names)))

    val export_vars = concl_transformation @
       (ListPair.zip (map Free fixes, map Free (ListPair.zip (names, map snd fixes))))
    val _ = debug_cond_msg ctxt (export_vars <> []) high (fn () => \<^print> ("Current mapping from variable names to the possibly new names that Isabelle chose",export_vars))

    (* Rewriting and transforming util *)
    val remove_lambdas =
      let val thy = Proof_Context.theory_of (Simplifier.empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy (if (Alethe_Proof.keep_raw_lifting rule) andalso not (null rewrite_rules) then tl rewrite_rules else rewrite_rules) []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs orelse Alethe_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
    val term_rewriter2 = subst_only_free global_transformation o subst_free_if_nonempty export_vars o remove_lambdas
    val term_rewriter = SMTLIB_Isar.unskolemize_names ctxt o term_rewriter2

    fun is_refl thm = Thm.concl_of thm |> (fn (_ $ t) => t | _ => raise TERM ("",[])) |> HOLogic.dest_eq |> (op =) handle TERM _=> false
    fun mk_thms sctxt t = (Assumption.add_assumes (map (Thm.cterm_of sctxt) t) sctxt |>> filter_out is_refl)

    fun is_mapping (\<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _ )) = true |
        is_mapping _ = false
    val remove_non_mappings = List.filter is_mapping

    (* Rewrite and transform components *)
    val rewritten_assms = map term_rewriter assms
    val rewritten_input = map term_rewriter input
    val rewritten_context_assignments = context_assignments |> remove_non_mappings |> map term_rewriter2
    val rewritten_step_args = map term_rewriter step_args
    val _ = debug_cond_msg ctxt (not (null step_args)) high (fn () => \<^print> ("Transformed step arguments (before,after)",(step_args,rewritten_step_args)))

    (* Build up new sub-context sub_ctxt2 using (context) assumptions *)
    val (assms_as_thm, sub_ctxt2) = mk_thms sub_ctxt rewritten_assms
    val (input_as_thm, sub_ctxt2) = mk_thms sub_ctxt2 rewritten_input
    val (context_assignments_as_thm, sub_ctxt2) = mk_thms sub_ctxt2 rewritten_context_assignments
    val updated_local_assumptions = all_local_assumptions @ assms_as_thm @ context_assignments_as_thm
    val _ = debug_cond_msg ctxt (not (null rewritten_assms)) high (fn () => \<^print> ("Transformed assumptions, i.e. top-level assumes (before,after)",(assms,assms_as_thm)))
    val _ = debug_cond_msg ctxt (not (null rewritten_input)) high (fn () => \<^print> ("Transformed input, i.e. assumes in subproofs (before,after)",(input,input_as_thm)))
    val _ = debug_cond_msg ctxt (not (null rewritten_context_assignments)) high (fn () => \<^print> ("Transformed context assignments (before,after)",(context_assignments,context_assignments_as_thm)))
    val _ = debug_cond_msg ctxt (not (null updated_local_assumptions)) low (fn () => \<^print> ("All assumptions holding after the current step", updated_local_assumptions))

    (* Processing subproof *)
    val _ = debug_cond_msg ctxt (not (null subproof)) low (fn () => \<^print> ("Interrupting the replay of the current step " ^ id ^ " to replay its subproof"))
    val replay = replay_theorem_step solver method_for rewrite_rules all_assms ll_defs assumed (input_as_thm @ inputs) updated_local_assumptions
    val (locally_known_facts, stats, _, _, sub_global_rew) =
       fold replay subproof (globally_known_facts, stats, sub_ctxt2, export_vars, global_transformation)
    val _ = debug_cond_msg ctxt (not (null subproof)) high (fn () => \<^print> ("Filled table with mapping from names (id or for skolems var_def) to " ^
      "theorems with all steps the current step can access",Symtab.keys locally_known_facts ))
    val _ = debug_cond_msg ctxt (not (null subproof)) low (fn () => \<^print> ("Finished processing the subproof, returning the original step",id))

    (* Processing components with new context *)
    val export_thm = singleton (Proof_Context.export sub_ctxt2 ctxt)
    val subst_transform = (Raw_Simplifier.rewrite_term (Proof_Context.theory_of (Simplifier.empty_simpset ctxt)) ((if (Alethe_Proof.keep_raw_lifting rule) andalso not (null rewrite_rules) then tl rewrite_rules else rewrite_rules)) []
         o (not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs) o subst_free_if_nonempty concl_transformation o subst_only_free global_transformation)
    val id_to_thm = (Symtab.lookup (if (null subproof) then globally_known_facts else locally_known_facts))
    (*the name of the used skolem definitions is not in the premises, but in
    the args*)
    val prems_skolem_def =
      (case args of
        SOME (Alethe_Node.Sko_Def_Prems (a, b)) => a @ b
      | _ => [])

    val prems_as_thms_with_context_assms =
      non_skolem_prems
      |> map_filter id_to_thm
      |> map (apsnd export_thm)
    val skolem_rule_prems_as_thms_with_context_assms =
      (if Alethe_Proof.is_skolemization rule (* Choice terms only appear in sko_forall and exists *)
       then prems_skolem_def |> map_filter (Symtab.lookup globally_known_facts) (* Skolem definitions are always in the outermost context *)
       else [])
    val step_args = map subst_transform step_args
    val args =
      (case args of
        SOME (Alethe_Node.Insts tab) => SOME (Alethe_Node.Insts (Symtab.map (K subst_transform) tab))
      | _ => args)
    val context_assignments = map subst_transform context_assignments
    val _ = debug_cond_msg ctxt (length non_skolem_prems <> length prems_as_thms_with_context_assms) low (fn () =>
      \<^print> ("Warning, there were premises that are not accessible to the current step (i.e., that are not in the context). This should not happen. These were ignored."))
    val _ = debug_cond_msg ctxt (not (null non_skolem_prems)) middle (fn () =>
      \<^print> ("Export premises that are not skolem definitions, to the current context." ^
        "This will automatically add context assertions and assumes to the goal.",(non_skolem_prems,prems_as_thms_with_context_assms)))
    val _ = debug_cond_msg ctxt (not (null step_args)) middle (fn () => \<^print> ("Processed step_args",step_args))
    val _ = debug_cond_msg ctxt (not (null context_assignments)) middle (fn () => \<^print> ("Processed context_assignments", context_assignments))

    val missing_assumptions =
       if SMT_Config.alethe_no_provided_assms ctxt andalso
         (rule = Alethe_Proof.local_input_rule orelse rule = Alethe_Proof.normalized_input_rule orelse rule = Alethe_Proof.input_rule)
       then all_assms (* For external problems we don't know which assumptions are used since the assertions might not have names, add all *)
       else []
    val all_local_assumptions =
       if Alethe_Replay_Methods.requires_subproof_assms non_skolem_prems rule then updated_local_assumptions else []
    val local_inputs =
       if Alethe_Replay_Methods.requires_local_input non_skolem_prems rule then input_as_thm @ inputs else []
    val _ = debug_cond_msg ctxt (not (null missing_assumptions)) low (fn () => \<^print> ("Assumptions could not be mapped to the current input rule by name" ^
      "(possibly because you are checking an external proof), so all assumptions were added",missing_assumptions))
    val _ = debug_cond_msg ctxt (not (null all_local_assumptions)) middle (fn () => \<^print> ("Added mapping from context_assignment as premises to steps (refl,sko_forall,sko_ex,cong)",all_local_assumptions))
    val _ = debug_cond_msg ctxt (not (null local_inputs)) middle (fn () => \<^print> ("Added the assumptions of the current subproof rule as premises",local_inputs))

    val _ = debug_msg ctxt low (fn () => \<^print> ("Calling reconstruction method for rule",id))
    val replay = (Timing.timing (replay_thm solver method_for rewrite_rules ll_defs
       ctxt assumed [] (missing_assumptions @ all_local_assumptions @ local_inputs)
       (prems_as_thms_with_context_assms @ skolem_rule_prems_as_thms_with_context_assms) concl_transformation
       global_transformation step_args context_assignments args))

    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt (rule ^ "," ^ id) SMT_Config.reconstruction_step_timeout replay step
      handle ERROR exn => Exn.reraise (ERROR (" in step " ^ id ^ " " ^ exn))

    val _ = (SMT_Config.verbose_msg ctxt (K ("Successfully checked step " ^ id)) ())

    val name =
      (case rule of
        "rare_rewrite" => "rare_rewrite" ^ "_" ^ HOLogic.dest_string (hd step_args)
      | _ => rule)
    val stats' = Symtab.cons_list (name, Time.toNanoseconds elapsed) stats
    val globally_known_facts = Symtab.update (id, (prop_skeleton, thm)) globally_known_facts
    val _ = debug_msg ctxt low (fn () => \<^print> ("Add resulting theorem to globally known facts", (id,(prop_skeleton,thm))))

  in (globally_known_facts, stats', ctxt, concl_transformation, sub_global_rew) end
 | replay_theorem_step _ _ _ _ _ _ _ _ _ _ = raise Fail "unreachable code to silence the compiler"


fun replay_definition_step rewrite_rules ll_defs
  (Alethe_Node.Alethe_Definition_Node {id, skolem_name, skolem_term, ...}) state =
  let
    val (proofs, stats, ctxt, concl_transformation, global_transformation) = state

    val global_transformer = subst_only_free global_transformation
    val rewrite = let val thy = Proof_Context.theory_of ctxt in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val start0 = Timing.start ()
    val declaration = (rewrite o global_transformer) skolem_term
    val (name, ctxt) = yield_singleton Variable.variant_fixes skolem_name ctxt
      ||> Variable.declare_term (Free (skolem_name, fastype_of declaration))
    val old_names = Free (skolem_name, fastype_of declaration)
    val new_names = Free (name, fastype_of declaration)
    fun update_mapping (a, b) tab =
      if a <> b andalso Termtab.lookup tab a = NONE
      then Termtab.update_new (a, b) tab else tab
    val global_transformation = global_transformation
      |> update_mapping (old_names, new_names)
    val global_transformer = subst_only_free global_transformation

    val generate_definition =
      (fn (name, term) => (HOLogic.mk_Trueprop
        (Const(\<^const_name>\<open>HOL.eq\<close>, fastype_of term --> fastype_of term --> @{typ bool}) $
            Free (name, fastype_of term) $ term)))
      #> global_transformer
      #> Thm.cterm_of ctxt
    val decls = generate_definition (skolem_name, declaration)
    val (def, ctxt) = yield_singleton Assumption.add_assumes decls ctxt
    val proofs = Symtab.update (id, (declaration, @{thm sym} OF [def])) proofs
    val total = Time.toNanoseconds (#elapsed (Timing.result start0))
    val stats = Symtab.cons_list ("choice", total) stats
  in (proofs, stats, ctxt, concl_transformation, global_transformation) end
 | replay_definition_step _ _ _ _ = raise Fail "unreachable code to silence the compiler"


fun prove_ll_def_from_assms assms ll_defs rewrite_rules stats ctxt term =
  let
    val rewrite = let val thy = Proof_Context.theory_of (Simplifier.empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs (* Unfold lambda defs *)
      end
    val replay = Timing.timing (SMT_Replay_Methods.prove ctxt (rewrite term))
    val replay_ll_assumption_tac = 
      Method.insert_tac ctxt assms THEN' K (unfold_tac ctxt @{thms SMT.alethe_id_def}) 
      THEN' (assume_tac ctxt
         ORELSE' (Alethe_Replay_Methods.REPEAT' (resolve_tac ctxt @{thms allI})
           THEN' Alethe_Replay_Methods.REPEAT' (resolve_tac ctxt @{thms refl})))
    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt "assumption" SMT_Config.reconstruction_step_timeout replay
         (fn _ => replay_ll_assumption_tac)
    val stats' = Symtab.cons_list (Alethe_Proof.input_rule, Time.toNanoseconds elapsed) stats
  in
    (thm, stats')
  end

fun replay_step solver method_for rewrite_rules all_assms ll_defs assumed inputs all_local_assumptions
    (step as Alethe_Node.Alethe_Replay_Node {...}) state =
     replay_theorem_step solver method_for rewrite_rules all_assms ll_defs assumed inputs all_local_assumptions step state
  | replay_step _ _ rewrite_rules _ ll_defs _ _ _
    (step as Alethe_Node.Alethe_Definition_Node {...}) state =
     replay_definition_step rewrite_rules ll_defs step state


fun replay solver method_for outer_ctxt
    ({ctxt = ctxt, typs, terms, rewrite_rules, assms, ll_defs, ...} : SMT_Translate.replay_data)
     raw_proof_steps =
  let
    val _ = if solver = "cvc5_prover" andalso not (SMT_Config.use_alethe_proof_from_cvc ctxt)
       then (raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("reconstruction with CVC is experimental.\n" ^
         "You must activate it with [[smt_cvc_alethe = true]] and use cvc5 (not included as component) .")))
       else ()
    val _ = debug_msg ctxt low (fn () => \<^print> ("Replaying proof"))

    (* Rewriting util *)
    val rewrite_rules =
      filter_out (fn thm => Term.could_unify (Thm.prop_of @{thm alethe_eq_true_simplify},
          Thm.prop_of thm))
        rewrite_rules
    val num_ll_defs = length ll_defs
    val index_of_id = Integer.add (~ num_ll_defs)

    (* Parse proof *)
    val start0 = Timing.start ()
    val (parsed_proof_steps, ctxt_after_parsing) =
      Alethe_Proof.parse_replay typs terms raw_proof_steps ctxt
    val parsing_time = Time.toNanoseconds (#elapsed (Timing.result start0))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("Finished parsing proof steps"))

    (* Prepare for replay *)
    val start = Timing.start ()

    (* Find used and non lambda lifting definition assumptions *)
    fun add_used_asserts_in_step (Alethe_Node.Alethe_Replay_Node {prems,
      subproof = (_, _, _, subproof), ...}) =
      union (op =) (map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) prems @
     flat (map (fn x => add_used_asserts_in_step x []) subproof)) |
    add_used_asserts_in_step (Alethe_Node.Alethe_Definition_Node _) = (fn x => x)

    val used_assert_ids = fold add_used_asserts_in_step parsed_proof_steps []
    val real_assms =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 andalso i < length assms then
            let val concl = Thm.prop_of (snd (nth assms i))
              |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of
               (Simplifier.add_simps rewrite_rules (Simplifier.empty_simpset ctxt))) rewrite_rules []
            in SOME (SMTLIB_Interface.assert_name_of_role_and_index SMT_Util.Axiom id,
              Alethe_Proof.input_rule, concl, @{term "Trueprop True"}) end
          else NONE end) used_assert_ids
    val _ = debug_msg ctxt high (fn () => \<^print> ("These are genuine assumptions of the proof",real_assms))

    (* Process lambda lifting definitions *)
    fun normalize_tac ctxt = let val thy = Proof_Context.theory_of (Simplifier.empty_simpset ctxt) in
      Raw_Simplifier.rewrite_term thy rewrite_rules [] end
    val used_lldefs =
      map_filter (fn id => let val i = index_of_id id in if i < 0 andalso not (ll_defs = [])
          then SOME (id, normalize_tac ctxt (nth ll_defs id)) else NONE end)
        used_assert_ids
    val _ = debug_msg ctxt high (fn () => \<^print> ("These assumptions were lambda lifting definitions that were actually used: ",used_lldefs))

    (* Add assumptions to context *)
    val add_assert = SMT_Replay.add_asserted Symtab.update Symtab.empty (fn x => x)
      (fn r => r = Alethe_Proof.input_rule)
    val ((_, _), (ctxt_with_asserts, assumed)) =
      add_assert outer_ctxt rewrite_rules (map (apfst fst) assms)
        real_assms ctxt_after_parsing
    val ctxt_with_asserts = ctxt_with_asserts
      |> put_simpset (SMT_Replay.make_simpset ctxt_with_asserts []) (* Note: we had this commented out for a while, if something breaks this could be a good candidate to comment out again *)
      |> Config.put SAT.solver (Config.get ctxt_after_parsing SMT_Config.sat_solver)

    (* Note: this proves and then adds the used lambda lifting definitions to the set of assumptions and could theoretically
       also update existing assumptions. It is not clear if the latter is needed, but erring on the side
       of caution we leave this code intact. *)
    val (assumed, stats) = fold (fn (ll_def_id, ll_def_term) => fn (assumed, stats) =>
      let
        val (thm, stats) = prove_ll_def_from_assms (map snd assms) ll_defs rewrite_rules stats ctxt ll_def_term
        val name = SMTLIB_Interface.assert_name_of_role_and_index SMT_Util.Axiom ll_def_id
      in
        (Symtab.update (name, (@{term "Trueprop True"}, thm)) assumed, stats)
      end)
      used_lldefs (assumed, Symtab.cons_list ("parsing", parsing_time) Symtab.empty)
    val _ = debug_msg ctxt middle (fn () => \<^print> ("Finished replaying the assumptions"))

    (* Linearize step ids *)
    val len = Alethe_Proof.number_of_steps parsed_proof_steps
    fun steps_with_depth _ [] = []
      | steps_with_depth i (p :: ps) =
        let val i' = i + Alethe_Proof.number_of_steps [p] in (i', p) :: steps_with_depth i' ps end
    val actual_steps = steps_with_depth 0 parsed_proof_steps

    (* Set-up statistics *)
    val print_runtime_statistics = SMT_Replay.intermediate_statistics ctxt_with_asserts start len
    fun blockwise f (i, x) (next, y) =
      (if i > next then print_runtime_statistics i else ();
       (if i > next then i + 10 else next, f x y))

    (* Replay steps *)
    val global_transformation : term Termtab.table = Termtab.empty
    val (_, (proofs, stats, ctxt5, _, _)) =
      fold (blockwise (replay_step solver method_for rewrite_rules (map snd assms) ll_defs assumed [] [])) actual_steps
        (1, (assumed, stats, ctxt_with_asserts, [], global_transformation))
    val id =
      (case split_last actual_steps of
        (_, (_, Alethe_Node.Alethe_Replay_Node {id, ...})) => id
      | _ => raise Fail "last proof step is not a replay node")
    val thm_with_defs =
      Symtab.lookup proofs id |> the |> snd
      |> singleton (Proof_Context.export ctxt5 outer_ctxt)
    val total = Time.toMilliseconds (#elapsed (Timing.result start))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("Last step (id " ^ id ^ ")", thm_with_defs))

    val _ = if solver = "cvc5_prover" then
              SMT_Replay.spying (SMT_Config.spy_cvc ctxt) ctxt
                (fn () => SMT_Replay.print_stats (Symtab.dest stats)) "$ISABELLE_SMT_CVC_SPY"
           else (* Everything that is not cvc5 is veriT *)
              SMT_Replay.spying (SMT_Config.spy_verit ctxt) ctxt
                                (fn () => SMT_Replay.print_stats (Symtab.dest stats)) "$ISABELLE_SMT_VERIT_SPY"
    (* Statistics *)
    val _ = print_runtime_statistics len
    val _ = SMT_Config.statistics_msg ctxt5
      (Pretty.string_of o SMT_Replay.pretty_statistics "cvc" total) stats

  in
    if SMT_Config.check_smt_is_slicing ctxt
    then thm_with_defs
    else CVC5_Replay_Methods.discharge ctxt [thm_with_defs] @{term False}
  end

end
