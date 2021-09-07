(*  Title:      Pure/goal.ML
    Author:     Makarius

Goals in tactical theorem proving, with support for forked proofs.
*)

signature BASIC_GOAL =
sig
  val quick_and_dirty: bool Config.T
  val SELECT_GOAL: tactic -> int -> tactic
  val PREFER_GOAL: tactic -> int -> tactic
  val CONJUNCTS: tactic -> int -> tactic
  val PRECISE_CONJUNCTS: int -> tactic -> int -> tactic
end;

signature GOAL =
sig
  include BASIC_GOAL
  val init: cterm -> thm
  val protect: int -> thm -> thm
  val conclude: thm -> thm
  val check_finished: Proof.context -> thm -> thm
  val finish: Proof.context -> thm -> thm
  val norm_result: Proof.context -> thm -> thm
  val skip_proofs_enabled: unit -> bool
  val future_result: Proof.context -> thm future -> term -> thm
  val prove_internal: Proof.context -> cterm list -> cterm -> (thm list -> tactic) -> thm
  val is_schematic: term -> bool
  val prove_common: Proof.context -> int option -> string list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm list
  val prove_future: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_global_future: theory -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_global: theory -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_sorry: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_sorry_global: theory -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val restrict: int -> int -> thm -> thm
  val unrestrict: int -> thm -> thm
  val conjunction_tac: int -> tactic
  val precise_conjunction_tac: int -> int -> tactic
  val recover_conjunction_tac: tactic
  val norm_hhf_tac: Proof.context -> int -> tactic
  val assume_rule_tac: Proof.context -> int -> tactic
end;

structure Goal: GOAL =
struct

(** goals **)

(*
  -------- (init)
  C \<Longrightarrow> #C
*)
fun init C = Thm.instantiate ([], [((("A", 0), propT), C)]) Drule.protectI;

(*
  A1 \<Longrightarrow> ... \<Longrightarrow> An \<Longrightarrow> C
  ------------------------ (protect n)
  A1 \<Longrightarrow> ... \<Longrightarrow> An \<Longrightarrow> #C
*)
fun protect n th = Drule.comp_no_flatten (th, n) 1 Drule.protectI;

(*
  A \<Longrightarrow> ... \<Longrightarrow> #C
  ---------------- (conclude)
  A \<Longrightarrow> ... \<Longrightarrow> C
*)
fun conclude th = Drule.comp_no_flatten (th, Thm.nprems_of th) 1 Drule.protectD;

(*
  #C
  --- (finish)
   C
*)
fun check_finished ctxt th =
  if Thm.no_prems th then th
  else
    raise THM ("Proof failed.\n" ^ Pretty.string_of (Goal_Display.pretty_goal ctxt th), 0, [th]);

fun finish ctxt = check_finished ctxt #> conclude;



(** results **)

(* normal form *)

fun norm_result ctxt =
  Drule.flexflex_unique (SOME ctxt)
  #> Raw_Simplifier.norm_hhf_protect ctxt
  #> Thm.strip_shyps
  #> Drule.zero_var_indexes;


(* scheduling parameters *)

fun skip_proofs_enabled () =
  let val skip = Options.default_bool "skip_proofs" in
    if Proofterm.proofs_enabled () andalso skip then
      (warning "Proof terms enabled -- cannot skip proofs"; false)
    else skip
  end;


(* future_result *)

fun future_result ctxt result prop =
  let
    val assms = Assumption.all_assms_of ctxt;
    val As = map Thm.term_of assms;

    val frees = Term_Subst.Frees.build (fold Term_Subst.add_frees (prop :: As));
    val xs = Term_Subst.Frees.fold_rev (cons o Thm.cterm_of ctxt o Free o #1) frees [];

    val tfrees = Term_Subst.TFrees.build (fold Term_Subst.add_tfrees (prop :: As));
    val Ts = Symtab.build (Term_Subst.TFrees.fold (Symtab.insert_set o #1 o #1) tfrees);
    val instT =
      build (tfrees |> Term_Subst.TFrees.fold (fn ((a, S), ()) =>
        cons (((a, 0), S), Thm.ctyp_of ctxt (TFree (a, S)))));

    val global_prop =
      Logic.list_implies (As, prop)
      |> Term_Subst.Frees.fold_rev (Logic.all o Free o #1) frees
      |> Logic.varify_types_global
      |> Thm.cterm_of ctxt
      |> Thm.weaken_sorts' ctxt;
    val global_result = result |> Future.map
      (Drule.flexflex_unique (SOME ctxt) #>
        Drule.implies_intr_list assms #>
        Drule.forall_intr_list xs #>
        Thm.adjust_maxidx_thm ~1 #>
        Thm.generalize (Ts, Symtab.empty) 0 #>
        Thm.strip_shyps #>
        Thm.solve_constraints);
    val local_result =
      Thm.future global_result global_prop
      |> Thm.close_derivation \<^here>
      |> Thm.instantiate (instT, [])
      |> Drule.forall_elim_list xs
      |> fold (Thm.elim_implies o Thm.assume) assms
      |> Thm.solve_constraints;
  in local_result end;



(** tactical theorem proving **)

(* prove_internal -- minimal checks, no normalization of result! *)

fun prove_internal ctxt casms cprop tac =
  (case SINGLE (tac (map (Assumption.assume ctxt) casms)) (init cprop) of
    SOME th => Drule.implies_intr_list casms (finish ctxt th)
  | NONE => error "Tactic failed");


(* prove variations *)

fun is_schematic t =
  Term.exists_subterm Term.is_Var t orelse
  Term.exists_type (Term.exists_subtype Term.is_TVar) t;

fun prove_common ctxt fork_pri xs asms props tac =
  let
    val thy = Proof_Context.theory_of ctxt;

    val schematic = exists is_schematic props;
    val immediate = is_none fork_pri;
    val future = Future.proofs_enabled 1 andalso not (Proofterm.proofs_enabled ());
    val skip = not immediate andalso not schematic andalso future andalso skip_proofs_enabled ();

    val pos = Position.thread_data ();
    fun err msg =
      cat_error msg
        ("The error(s) above occurred for the goal statement" ^ Position.here pos ^ ":\n" ^
          Syntax.string_of_term ctxt (Logic.list_implies (asms, Logic.mk_conjunction_list props)));

    fun cert_safe t = Thm.cterm_of ctxt (Envir.beta_norm (Term.no_dummy_patterns t))
      handle TERM (msg, _) => err msg | TYPE (msg, _, _) => err msg;
    val casms = map cert_safe asms;
    val cprops = map cert_safe props;

    val (prems, ctxt') = ctxt
      |> Variable.add_fixes_direct xs
      |> fold Variable.declare_term (asms @ props)
      |> Assumption.add_assumes casms
      ||> Variable.set_body true;

    val stmt = Thm.weaken_sorts' ctxt' (Conjunction.mk_conjunction_balanced cprops);

    fun tac' args st =
      if skip then ALLGOALS (Skip_Proof.cheat_tac ctxt) st before Skip_Proof.report ctxt
      else tac args st;
    fun result () =
      (case SINGLE (tac' {prems = prems, context = ctxt'}) (init stmt) of
        NONE => err "Tactic failed"
      | SOME st =>
          let
            val _ =
              Context.subthy_id (Thm.theory_id st, Context.theory_id thy) orelse
                err "Bad background theory of goal state";
            val res =
              (finish ctxt' st
                |> Drule.flexflex_unique (SOME ctxt')
                |> Thm.check_shyps ctxt'
                |> Thm.check_hyps (Context.Proof ctxt'))
              handle THM (msg, _, _) => err msg | ERROR msg => err msg;
          in
            if Unify.matches_list (Context.Proof ctxt') [Thm.term_of stmt] [Thm.prop_of res]
            then res
            else err ("Proved a different theorem: " ^ Syntax.string_of_term ctxt' (Thm.prop_of res))
          end);
    val res =
      if immediate orelse schematic orelse not future orelse skip then result ()
      else
        future_result ctxt'
          (Execution.fork {name = "Goal.prove", pos = Position.thread_data (), pri = the fork_pri}
            result)
          (Thm.term_of stmt);
  in
    res
    |> Thm.close_derivation \<^here>
    |> Conjunction.elim_balanced (length props)
    |> map (Assumption.export false ctxt' ctxt)
    |> Variable.export ctxt' ctxt
    |> map Drule.zero_var_indexes
  end;

fun prove_future_pri ctxt pri xs asms prop tac =
  hd (prove_common ctxt (SOME pri) xs asms [prop] tac);

fun prove_future ctxt = prove_future_pri ctxt ~1;

fun prove ctxt xs asms prop tac = hd (prove_common ctxt NONE xs asms [prop] tac);

fun prove_global_future thy xs asms prop tac =
  Drule.export_without_context (prove_future (Proof_Context.init_global thy) xs asms prop tac);

fun prove_global thy xs asms prop tac =
  Drule.export_without_context (prove (Proof_Context.init_global thy) xs asms prop tac);


(* skip proofs *)

val quick_and_dirty = Config.declare_option_bool ("quick_and_dirty", \<^here>);

fun prove_sorry ctxt xs asms prop tac =
  if Config.get ctxt quick_and_dirty then
    prove ctxt xs asms prop (fn _ => ALLGOALS (Skip_Proof.cheat_tac ctxt))
  else (if Future.proofs_enabled 1 then prove_future_pri ctxt ~2 else prove ctxt) xs asms prop tac;

fun prove_sorry_global thy xs asms prop tac =
  Drule.export_without_context
    (prove_sorry (Proof_Context.init_global thy) xs asms prop tac);



(** goal structure **)

(* rearrange subgoals *)

fun restrict i n st =
  if i < 1 orelse n < 1 orelse i + n - 1 > Thm.nprems_of st
  then raise THM ("Goal.restrict", i, [st])
  else rotate_prems (i - 1) st |> protect n;

fun unrestrict i = conclude #> rotate_prems (1 - i);

(*with structural marker*)
fun SELECT_GOAL tac i st =
  if Thm.nprems_of st = 1 andalso i = 1 then tac st
  else (PRIMITIVE (restrict i 1) THEN tac THEN PRIMITIVE (unrestrict i)) st;

(*without structural marker*)
fun PREFER_GOAL tac i st =
  if i < 1 orelse i > Thm.nprems_of st then Seq.empty
  else (PRIMITIVE (rotate_prems (i - 1)) THEN tac THEN PRIMITIVE (rotate_prems (1 - i))) st;


(* multiple goals *)

fun precise_conjunction_tac 0 i = eq_assume_tac i
  | precise_conjunction_tac 1 i = SUBGOAL (K all_tac) i
  | precise_conjunction_tac n i = PRIMITIVE (Drule.with_subgoal i (Conjunction.curry_balanced n));

val adhoc_conjunction_tac = REPEAT_ALL_NEW
  (SUBGOAL (fn (goal, i) =>
    if can Logic.dest_conjunction goal then resolve0_tac [Conjunction.conjunctionI] i
    else no_tac));

val conjunction_tac = SUBGOAL (fn (goal, i) =>
  precise_conjunction_tac (length (Logic.dest_conjunctions goal)) i ORELSE
  TRY (adhoc_conjunction_tac i));

val recover_conjunction_tac = PRIMITIVE (fn th =>
  Conjunction.uncurry_balanced (Thm.nprems_of th) th);

fun PRECISE_CONJUNCTS n tac =
  SELECT_GOAL (precise_conjunction_tac n 1
    THEN tac
    THEN recover_conjunction_tac);

fun CONJUNCTS tac =
  SELECT_GOAL (conjunction_tac 1
    THEN tac
    THEN recover_conjunction_tac);


(* hhf normal form *)

fun norm_hhf_tac ctxt =
  resolve_tac ctxt [Drule.asm_rl]  (*cheap approximation -- thanks to builtin Logic.flatten_params*)
  THEN' SUBGOAL (fn (t, i) =>
    if Drule.is_norm_hhf t then all_tac
    else rewrite_goal_tac ctxt Drule.norm_hhf_eqs i);


(* non-atomic goal assumptions *)

fun non_atomic (Const ("Pure.imp", _) $ _ $ _) = true
  | non_atomic (Const ("Pure.all", _) $ _) = true
  | non_atomic _ = false;

fun assume_rule_tac ctxt = norm_hhf_tac ctxt THEN' CSUBGOAL (fn (goal, i) =>
  let
    val ((_, goal'), ctxt') = Variable.focus_cterm NONE goal ctxt;
    val goal'' = Drule.cterm_rule (singleton (Variable.export ctxt' ctxt)) goal';
    val Rs = filter (non_atomic o Thm.term_of) (Drule.strip_imp_prems goal'');
    val tacs = Rs |> map (fn R =>
      eresolve_tac ctxt [Raw_Simplifier.norm_hhf ctxt (Thm.trivial R)] THEN_ALL_NEW assume_tac ctxt);
  in fold_rev (curry op APPEND') tacs (K no_tac) i end);

end;

structure Basic_Goal: BASIC_GOAL = Goal;
open Basic_Goal;
