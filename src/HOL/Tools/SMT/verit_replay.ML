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

fun under_fixes f unchanged_prems (prems, nthms) names args (concl, ctxt) =
  let
    val thms1 = unchanged_prems @ map (SMT_Replay.varify ctxt) prems
    val _ =  SMT_Config.veriT_msg ctxt (fn () => @{print}  ("names =", names))
    val thms2 = map snd nthms
    val _ = SMT_Config.veriT_msg ctxt (fn () => @{print} ("prems=", prems))
    val _ = SMT_Config.veriT_msg ctxt (fn () => @{print} ("nthms=", nthms))
    val _ = SMT_Config.veriT_msg ctxt (fn () => @{print} ("thms1=", thms1))
    val _ = SMT_Config.veriT_msg ctxt (fn () => @{print} ("thms2=", thms2))
  in (f ctxt (thms1 @ thms2) args concl) end


(** Replaying **)

fun replay_thm method_for rewrite_rules ll_defs ctxt assumed unchanged_prems prems nthms
    concl_transformation global_transformation args
    (VeriT_Proof.VeriT_Replay_Node {id, rule, concl, bounds,  ...}) =
  let
    val _ = SMT_Config.veriT_msg ctxt (fn () => @{print} id)
    val rewrite = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val post = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
    val concl = concl
      |> concl_transformation
      |> global_transformation
      |> post
in
  if rule = VeriT_Proof.veriT_input_rule then
    (case Symtab.lookup assumed id of
      SOME (_, thm) => thm)
  else
    under_fixes (method_for rule) unchanged_prems
      (prems, nthms) (map fst bounds)
      (map rewrite args) (concl, ctxt)
end

fun add_used_asserts_in_step (VeriT_Proof.VeriT_Replay_Node {prems,
    subproof = (_, _, subproof), ...}) =
  union (op =) (map_filter (try SMTLIB_Interface.assert_index_of_name) prems @
     flat (map (fn x => add_used_asserts_in_step x []) subproof))

fun remove_rewrite_rules_from_rules n =
  (fn (step as VeriT_Proof.VeriT_Replay_Node {id, ...}) =>
    (case try SMTLIB_Interface.assert_index_of_name id of
      NONE => SOME step
    | SOME a => if a < n then NONE else SOME step))

fun replay_step rewrite_rules ll_defs assumed proof_prems
  (step as VeriT_Proof.VeriT_Replay_Node {id, rule, prems, bounds, args,
     subproof = (fixes, assms, subproof), concl, ...}) state =
  let
    val (proofs, stats, ctxt, concl_tranformation, global_transformation) = state
    val (_, ctxt) = Variable.variant_fixes (map fst bounds) ctxt
      |> (fn (names, ctxt) => (names,
        fold Variable.declare_term [SMTLIB_Isar.unskolemize_names ctxt concl] ctxt))

    val (names, sub_ctxt) = Variable.variant_fixes (map fst fixes) ctxt
       ||> fold Variable.declare_term (map Free fixes)
    val export_vars =
      Term.subst_free (ListPair.zip (map Free fixes, map Free (ListPair.zip (names, map snd fixes))))
      o concl_tranformation

    val post = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
    val assms = map (export_vars o global_transformation o post) assms
    val (proof_prems', sub_ctxt2) = Assumption.add_assumes (map (Thm.cterm_of sub_ctxt) assms)
      sub_ctxt

    val all_proof_prems = proof_prems @ proof_prems'
    val (proofs', stats, _, _, sub_global_rew) =
       fold (replay_step rewrite_rules ll_defs assumed all_proof_prems) subproof
         (assumed, stats, sub_ctxt2, export_vars, global_transformation)
    val export_thm = singleton (Proof_Context.export sub_ctxt2 ctxt)
    val nthms = prems
      |>  map (apsnd export_thm o the o (Symtab.lookup (if null subproof then proofs else proofs')))
    val proof_prems =
       if Verit_Replay_Methods.veriT_step_requires_subproof_assms rule then proof_prems else []
    val replay = Timing.timing (replay_thm Verit_Replay_Methods.method_for rewrite_rules ll_defs
       ctxt assumed [] (proof_prems) nthms concl_tranformation global_transformation args)
    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay step
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out
    val stats' = Symtab.cons_list (rule, Time.toMilliseconds elapsed) stats
  in (Symtab.update (id, (map fst bounds, thm)) proofs, stats', ctxt,
       concl_tranformation, sub_global_rew) end

fun replay_ll_def assms ll_defs rewrite_rules stats ctxt term =
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
    val stats' = Symtab.cons_list ("ll_defs", Time.toMilliseconds elapsed) stats
  in
    (thm, stats')
  end

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

    val (actual_steps, ctxt2) =
      VeriT_Proof.parse_replay typs terms output ctxt

    fun step_of_assume (j, (_, th)) =
      VeriT_Proof.VeriT_Replay_Node {
        id = SMTLIB_Interface.assert_name_of_index (id_of_index j),
        rule = VeriT_Proof.veriT_input_rule,
        args = [],
        prems = [],
        proof_ctxt = [],
        concl = Thm.prop_of th
          |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of
               (empty_simpset ctxt addsimps rewrite_rules)) [] [],
        bounds = [],
        subproof = ([], [], [])}
    val used_assert_ids = fold add_used_asserts_in_step actual_steps []
    fun normalize_tac ctxt = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
      Raw_Simplifier.rewrite_term thy rewrite_rules [] end
    val used_assm_js =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME (i, nth assms i)
          else NONE end)
        used_assert_ids

    val assm_steps = map step_of_assume used_assm_js
    val steps = assm_steps @ actual_steps

    fun extract (VeriT_Proof.VeriT_Replay_Node {id, rule, concl, bounds, ...}) =
         (id, rule, concl, map fst bounds)
    fun cond rule = rule = VeriT_Proof.veriT_input_rule
    val add_asssert = SMT_Replay.add_asserted Symtab.update Symtab.empty extract cond
    val ((_, _), (ctxt3, assumed)) =
      add_asssert outer_ctxt rewrite_rules assms
        (map_filter (remove_rewrite_rules_from_rules num_ll_defs) steps) ctxt2

    val used_rew_js =
      map_filter (fn id => let val i = index_of_id id in if i < 0
          then SOME (id, normalize_tac ctxt (nth ll_defs id)) else NONE end)
        used_assert_ids
    val (assumed, stats) = fold (fn ((id, thm)) => fn (assumed, stats) =>
           let val (thm, stats) =  replay_ll_def assms ll_defs rewrite_rules stats ctxt thm
           in (Symtab.update (SMTLIB_Interface.assert_name_of_index id, ([], thm)) assumed, stats)
           end)
         used_rew_js (assumed,  Symtab.empty)

    val ctxt4 =
      ctxt3
      |> put_simpset (SMT_Replay.make_simpset ctxt3 [])
      |> Config.put SAT.solver (Config.get ctxt3 SMT_Config.sat_solver)
    val len = length steps
    val start = Timing.start ()
    val print_runtime_statistics = SMT_Replay.intermediate_statistics ctxt4 start len
    fun blockwise f (i, x) y =
      (if i > 0 andalso i mod 100 = 0 then print_runtime_statistics i else (); f x y)
    val (proofs, stats, ctxt5, _, _) =
      fold_index (blockwise (replay_step rewrite_rules ll_defs assumed [])) steps
        (assumed, stats, ctxt4, fn x => x, fn x => x)
    val _ = print_runtime_statistics len
    val total = Time.toMilliseconds (#elapsed (Timing.result start))
    val (_, VeriT_Proof.VeriT_Replay_Node {id, ...}) = split_last steps
    val _ = SMT_Config.statistics_msg ctxt5
      (Pretty.string_of o SMT_Replay.pretty_statistics "veriT" total) stats
  in
    Symtab.lookup proofs id |> the |> snd |> singleton (Proof_Context.export ctxt5 outer_ctxt)
  end

end
