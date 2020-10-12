(*  Title:      HOL/Tools/SMT/verit_replay.ML
    Author:     Mathias Fleury, MPII

VeriT proof parsing and replay.
*)

signature VERIT_REPLAY =
sig
  val replay: Proof.context -> SMT_Translate.replay_data -> string list -> thm
end;

structure Verit_Replay: VERIT_REPLAY =
struct

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
  in substf end;


fun under_fixes f unchanged_prems (prems, nthms) names args insts decls (concl, ctxt) =
  let
    val thms1 = unchanged_prems @ map (SMT_Replay.varify ctxt) prems
    val _ =  SMT_Config.verit_msg ctxt (fn () => \<^print>  ("names =", names))
    val thms2 = map snd nthms
    val _ = SMT_Config.verit_msg ctxt (fn () => \<^print> ("prems=", prems))
    val _ = SMT_Config.verit_msg ctxt (fn () => \<^print> ("nthms=", nthms))
    val _ = SMT_Config.verit_msg ctxt (fn () => \<^print> ("thms1=", thms1))
    val _ = SMT_Config.verit_msg ctxt (fn () => \<^print> ("thms2=", thms2))
  in (f ctxt (thms1 @ thms2) args insts decls concl) end


(** Replaying **)

fun replay_thm method_for rewrite_rules ll_defs ctxt assumed unchanged_prems prems nthms
    concl_transformation global_transformation args insts
    (Verit_Proof.VeriT_Replay_Node {id, rule, concl, bounds, declarations = decls, ...}) =
  let
    val _ = SMT_Config.verit_msg ctxt (fn () => \<^print> id)
    val rewrite = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs andalso Verit_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val rewrite_concl = if Verit_Proof.keep_app_symbols rule then
          filter (curry Term.could_unify (Thm.concl_of @{thm SMT.fun_app_def}) o Thm.concl_of) rewrite_rules
        else rewrite_rules
    val post = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_concl []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
    val concl = concl
      |> Term.subst_free concl_transformation
      |> subst_only_free global_transformation
      |> post
  in
    if rule = Verit_Proof.input_rule then
      (case Symtab.lookup assumed id of
        SOME (_, thm) => thm
      | _ => raise Fail ("assumption " ^ @{make_string} id ^ " not found"))
    else
      under_fixes (method_for rule) unchanged_prems
        (prems, nthms) (map fst bounds)
        (map rewrite args)
        (Symtab.map (K rewrite) insts)
        decls
        (concl, ctxt)
      |> Simplifier.simplify (empty_simpset ctxt addsimps rewrite_rules)
  end

fun add_used_asserts_in_step (Verit_Proof.VeriT_Replay_Node {prems,
    subproof = (_, _, _, subproof), ...}) =
  union (op =) (map_filter (try SMTLIB_Interface.assert_index_of_name) prems @
     flat (map (fn x => add_used_asserts_in_step x []) subproof))

fun remove_rewrite_rules_from_rules n =
  (fn (step as Verit_Proof.VeriT_Replay_Node {id, ...}) =>
    (case try SMTLIB_Interface.assert_index_of_name id of
      NONE => SOME step
    | SOME a => if a < n then NONE else SOME step))


fun replay_theorem_step rewrite_rules ll_defs assumed inputs proof_prems
  (step as Verit_Proof.VeriT_Replay_Node {id, rule, prems, bounds, args, insts,
     subproof = (fixes, assms, input, subproof), concl, ...}) state =
  let
    val (proofs, stats, ctxt, concl_tranformation, global_transformation) = state
    val (_, ctxt) = Variable.variant_fixes (map fst bounds) ctxt
      |> (fn (names, ctxt) => (names,
        fold Variable.declare_term [SMTLIB_Isar.unskolemize_names ctxt concl] ctxt))

    val (names, sub_ctxt) = Variable.variant_fixes (map fst fixes) ctxt
       ||> fold Variable.declare_term (map Free fixes)
    val export_vars = concl_tranformation @
       (ListPair.zip (map Free fixes, map Free (ListPair.zip (names, map snd fixes))))

    val post = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy ((if Verit_Proof.keep_raw_lifting rule then tl rewrite_rules else rewrite_rules)) []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs andalso Verit_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
    val assms = map (subst_only_free global_transformation o Term.subst_free (export_vars) o post) assms
    val input = map (subst_only_free global_transformation o Term.subst_free (export_vars) o post) input
    val (all_proof_prems', sub_ctxt2) = Assumption.add_assumes (map (Thm.cterm_of sub_ctxt) (assms @ input))
      sub_ctxt
    fun is_refl thm = Thm.concl_of thm |> (fn (_ $ t) => t) |> HOLogic.dest_eq |> (op =) handle TERM _=> false
    val all_proof_prems' =
        all_proof_prems'
        |> filter_out is_refl
    val proof_prems' = take (length assms) all_proof_prems'
    val input = drop (length assms) all_proof_prems'
    val all_proof_prems = proof_prems @ proof_prems'
    val replay = replay_theorem_step rewrite_rules ll_defs assumed (input @ inputs) all_proof_prems
    val (proofs', stats, _, _, sub_global_rew) =
       fold replay subproof (proofs, stats, sub_ctxt2, export_vars, global_transformation)

    val export_thm = singleton (Proof_Context.export sub_ctxt2 ctxt)

    (*for sko_ex and sko_forall, assumptions are in proofs',  but the definition of the skolem
       function is in proofs *)
    val nthms = prems
      |> map (apsnd export_thm) o map_filter (Symtab.lookup (if (null subproof) then proofs else proofs'))
    val nthms' = (if Verit_Proof.is_skolemisation rule
         then prems else [])
      |> map_filter (Symtab.lookup proofs)
    val args = map (Term.subst_free concl_tranformation o subst_only_free global_transformation) args
    val insts = Symtab.map (K (Term.subst_free concl_tranformation o subst_only_free global_transformation)) insts
    val proof_prems =
       if Lethe_Replay_Methods.requires_subproof_assms prems rule then proof_prems else []
    val local_inputs =
       if Lethe_Replay_Methods.requires_local_input prems rule then input @ inputs else []
    val replay = Timing.timing (replay_thm Lethe_Replay_Methods.method_for rewrite_rules ll_defs
       ctxt assumed [] (proof_prems @ local_inputs) (nthms @ nthms') concl_tranformation
       global_transformation args insts)

    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay step
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out
    val stats' = Symtab.cons_list (rule, Time.toNanoseconds elapsed) stats
(*     val _ = ((Time.toMilliseconds elapsed > 10 andalso (rule = "cong")) ? @{print})
        ("WARNING slow " ^ id ^ @{make_string} rule ^ ": " ^ string_of_int (Time.toMilliseconds elapsed) ^ " "
         ^ @{make_string} (proof_prems @ local_inputs))
    val _ = ((Time.toMilliseconds elapsed > 10 andalso (rule = "cong")) ? @{print})
        ( (proof_prems @ local_inputs))
    val _ = ((Time.toMilliseconds elapsed > 10 andalso (rule = "cong")) ? @{print})
        thm
    val _ = ((Time.toMilliseconds elapsed > 40) ? @{print})
        ("WARNING slow " ^ id ^ @{make_string} rule ^ ": " ^ string_of_int (Time.toMilliseconds elapsed)) *)
    val proofs = Symtab.update (id, (map fst bounds, thm)) proofs
  in (proofs, stats', ctxt,
       concl_tranformation, sub_global_rew) end

fun replay_definition_step rewrite_rules ll_defs _ _ _
  (Verit_Proof.VeriT_Replay_Node {id, declarations = raw_declarations, subproof = (_, _, _, subproof), ...}) state =
  let
    val _ = if null subproof then ()
          else raise (Fail ("unrecognized veriT proof, definition has a subproof"))
    val (proofs, stats, ctxt, concl_tranformation, global_transformation) = state
    val global_transformer = subst_only_free global_transformation
    val rewrite = let val thy = Proof_Context.theory_of ctxt in
        Raw_Simplifier.rewrite_term thy (rewrite_rules) []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val start0 = Timing.start ()
    val declaration = map (apsnd (rewrite o global_transformer)) raw_declarations
    val (names, ctxt) = Variable.variant_fixes (map fst declaration) ctxt
       ||> fold Variable.declare_term (map Free (map (apsnd fastype_of) declaration))
    val old_names = map Free (map (fn (a, b) => (a, fastype_of b)) declaration)
    val new_names = map Free (ListPair.zip (names, map (fastype_of o snd) declaration))
    fun update_mapping (a, b) tab = 
          if a <> b andalso Termtab.lookup tab a = NONE
          then Termtab.update_new (a, b) tab else tab
    val global_transformation = global_transformation 
     |> fold update_mapping (ListPair.zip (old_names, new_names))
    val global_transformer = subst_only_free global_transformation

    val generate_definition =
      (fn (name, term) => (HOLogic.mk_Trueprop
        (Const(\<^const_name>\<open>HOL.eq\<close>, fastype_of term --> fastype_of term --> @{typ bool}) $
            Free (name, fastype_of term) $ term)))
      #> global_transformer
      #> Thm.cterm_of ctxt
    val decls = map generate_definition declaration
    val (defs, ctxt) = Assumption.add_assumes decls ctxt
    val thms_with_old_name = ListPair.zip (map fst declaration, defs)
    val proofs = fold
      (fn (name, thm) => Symtab.update (id, ([name], @{thm sym} OF [thm])))
      thms_with_old_name proofs
    val total = Time.toNanoseconds (#elapsed (Timing.result start0))
    val stats = Symtab.cons_list ("choice", total) stats
  in (proofs, stats, ctxt, concl_tranformation, global_transformation) end


fun replay_assumed assms ll_defs rewrite_rules stats ctxt term =
  let
    val rewrite = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val replay = Timing.timing (SMT_Replay_Methods.prove ctxt (rewrite term))
    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay
         (fn _ => Method.insert_tac ctxt (map snd assms) THEN' Classical.fast_tac ctxt)
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out
    val stats' = Symtab.cons_list (Verit_Proof.input_rule, Time.toNanoseconds elapsed) stats
  in
    (thm, stats')
  end


fun replay_step rewrite_rules ll_defs assumed inputs proof_prems
  (step as Verit_Proof.VeriT_Replay_Node {rule, ...}) state =
  if rule = Verit_Proof.veriT_def
  then replay_definition_step rewrite_rules ll_defs assumed inputs proof_prems step state
  else replay_theorem_step rewrite_rules ll_defs assumed inputs proof_prems step state


fun replay outer_ctxt
    ({context = ctxt, typs, terms, rewrite_rules, assms, ll_defs, ...} : SMT_Translate.replay_data)
     output =
  let
    val rewrite_rules =
      filter_out (fn thm => Term.could_unify (Thm.prop_of @{thm verit_eq_true_simplify},
          Thm.prop_of thm))
        rewrite_rules
    val num_ll_defs = length ll_defs
    val index_of_id = Integer.add (~ num_ll_defs)
    val id_of_index = Integer.add num_ll_defs

    val start0 = Timing.start ()
    val (actual_steps, ctxt2) =
      Verit_Proof.parse_replay typs terms output ctxt
    val parsing_time = Time.toNanoseconds (#elapsed (Timing.result start0))

    fun step_of_assume (j, (_, th)) =
      Verit_Proof.VeriT_Replay_Node {
        id = SMTLIB_Interface.assert_name_of_index (id_of_index j),
        rule = Verit_Proof.input_rule,
        args = [],
        prems = [],
        proof_ctxt = [],
        concl = Thm.prop_of th
          |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of
               (empty_simpset ctxt addsimps rewrite_rules)) rewrite_rules [],
        bounds = [],
        insts = Symtab.empty,
        declarations = [],
        subproof = ([], [], [], [])}
    val used_assert_ids = fold add_used_asserts_in_step actual_steps []
    fun normalize_tac ctxt = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
      Raw_Simplifier.rewrite_term thy rewrite_rules [] end
    val used_assm_js =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME (i, nth assms i)
          else NONE end)
        used_assert_ids

    val assm_steps = map step_of_assume used_assm_js

    fun extract (Verit_Proof.VeriT_Replay_Node {id, rule, concl, bounds, ...}) =
         (id, rule, concl, map fst bounds)
    fun cond rule = rule = Verit_Proof.input_rule
    val add_asssert = SMT_Replay.add_asserted Symtab.update Symtab.empty extract cond
    val ((_, _), (ctxt3, assumed)) =
      add_asssert outer_ctxt rewrite_rules assms
        (map_filter (remove_rewrite_rules_from_rules num_ll_defs) assm_steps) ctxt2

    val used_rew_js =
      map_filter (fn id => let val i = index_of_id id in if i < 0
          then SOME (id, normalize_tac ctxt (nth ll_defs id)) else NONE end)
        used_assert_ids
    val (assumed, stats) = fold (fn ((id, thm)) => fn (assumed, stats) =>
           let val (thm, stats) = replay_assumed assms ll_defs rewrite_rules stats ctxt thm
           in (Symtab.update (SMTLIB_Interface.assert_name_of_index id, ([], thm)) assumed, stats)
           end)
         used_rew_js (assumed, Symtab.cons_list ("parsing", parsing_time) Symtab.empty)

    val ctxt4 =
      ctxt3
      |> put_simpset (SMT_Replay.make_simpset ctxt3 [])
      |> Config.put SAT.solver (Config.get ctxt3 SMT_Config.sat_solver)
    val len = Verit_Proof.number_of_steps actual_steps
    fun steps_with_depth _ [] = []
      | steps_with_depth i (p :: ps) = (i +  Verit_Proof.number_of_steps [p], p) ::
          steps_with_depth (i +  Verit_Proof.number_of_steps [p]) ps
    val actual_steps = steps_with_depth 0 actual_steps
    val start = Timing.start ()
    val print_runtime_statistics = SMT_Replay.intermediate_statistics ctxt4 start len
    fun blockwise f (i, x) (next, y) =
      (if i > next then print_runtime_statistics i else ();
       (if i > next then i + 10 else next, f x y))
    val global_transformation : term Termtab.table = Termtab.empty
    val (_, (proofs, stats, ctxt5, _, _)) =
      fold (blockwise (replay_step rewrite_rules ll_defs assumed [] [])) actual_steps
        (1, (assumed, stats, ctxt4, [], global_transformation))
    val total = Time.toMilliseconds (#elapsed (Timing.result start))
    val (_, (_, Verit_Proof.VeriT_Replay_Node {id, ...})) = split_last actual_steps
    val _ = print_runtime_statistics len
    val thm_with_defs = Symtab.lookup proofs id |> the |> snd
      |> singleton (Proof_Context.export ctxt5 outer_ctxt)
    val _ = SMT_Config.statistics_msg ctxt5
      (Pretty.string_of o SMT_Replay.pretty_statistics "veriT" total) stats
    val _ = SMT_Replay.spying (SMT_Config.spy_verit ctxt) ctxt
      (fn () => SMT_Replay.print_stats (Symtab.dest stats)) "spy_verit"
  in
    Lethe_Replay_Methods.discharge ctxt [thm_with_defs] @{term False}
  end

end
