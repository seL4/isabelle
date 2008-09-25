(*  Title:      Pure/goal.ML
    ID:         $Id$
    Author:     Makarius and Lawrence C Paulson

Goals in tactical theorem proving.
*)

signature BASIC_GOAL =
sig
  val SELECT_GOAL: tactic -> int -> tactic
  val CONJUNCTS: tactic -> int -> tactic
  val PRECISE_CONJUNCTS: int -> tactic -> int -> tactic
end;

signature GOAL =
sig
  include BASIC_GOAL
  val init: cterm -> thm
  val protect: thm -> thm
  val conclude: thm -> thm
  val finish: thm -> thm
  val norm_result: thm -> thm
  val promise_result: Proof.context -> (unit -> thm) -> term -> thm
  val prove_internal: cterm list -> cterm -> (thm list -> tactic) -> thm
  val prove_multi: Proof.context -> string list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm list
  val prove_promise: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_global: theory -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val extract: int -> int -> thm -> thm Seq.seq
  val retrofit: int -> int -> thm -> thm -> thm Seq.seq
  val conjunction_tac: int -> tactic
  val precise_conjunction_tac: int -> int -> tactic
  val recover_conjunction_tac: tactic
  val norm_hhf_tac: int -> tactic
  val compose_hhf_tac: thm -> int -> tactic
  val assume_rule_tac: Proof.context -> int -> tactic
end;

structure Goal: GOAL =
struct

(** goals **)

(*
  -------- (init)
  C ==> #C
*)
val init =
  let val A = #1 (Thm.dest_implies (Thm.cprop_of Drule.protectI))
  in fn C => Thm.instantiate ([], [(A, C)]) Drule.protectI end;

(*
   C
  --- (protect)
  #C
*)
fun protect th = th COMP_INCR Drule.protectI;

(*
  A ==> ... ==> #C
  ---------------- (conclude)
  A ==> ... ==> C
*)
fun conclude th =
  (case SINGLE (Thm.compose_no_flatten false (th, Thm.nprems_of th) 1)
      (Drule.incr_indexes th Drule.protectD) of
    SOME th' => th'
  | NONE => raise THM ("Failed to conclude goal", 0, [th]));

(*
  #C
  --- (finish)
   C
*)
fun finish th =
  (case Thm.nprems_of th of
    0 => conclude th
  | n => raise THM ("Proof failed.\n" ^
      Pretty.string_of (Pretty.chunks (Display.pretty_goals n th)) ^
      ("\n" ^ string_of_int n ^ " unsolved goal(s)!"), 0, [th]));



(** results **)

(* normal form *)

val norm_result =
  Drule.flexflex_unique
  #> MetaSimplifier.norm_hhf_protect
  #> Thm.strip_shyps
  #> Drule.zero_var_indexes;


(* promise *)

fun promise_result ctxt result prop =
  let
    val thy = ProofContext.theory_of ctxt;
    val _ = Context.reject_draft thy;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;

    val assms = Assumption.assms_of ctxt;
    val As = map Thm.term_of assms;

    val xs = map Free (fold Term.add_frees (prop :: As) []);
    val fixes = map cert xs;

    val tfrees = fold Term.add_tfrees (prop :: As) [];
    val instT = map (fn (a, S) => (certT (TVar ((a, 0), S)), certT (TFree (a, S)))) tfrees;

    val global_prop =
      Term.map_types Logic.varifyT (fold_rev Logic.all xs (Logic.list_implies (As, prop)));
    val global_result =
      Thm.generalize (map #1 tfrees, []) 0 o
      Drule.forall_intr_list fixes o
      Drule.implies_intr_list assms o
      Thm.adjust_maxidx_thm ~1 o result;
    val local_result =
      Thm.promise global_result (cert global_prop)
      |> Thm.instantiate (instT, [])
      |> Drule.forall_elim_list fixes
      |> fold (Thm.elim_implies o Thm.assume) assms;
  in local_result end;



(** tactical theorem proving **)

(* prove_internal -- minimal checks, no normalization of result! *)

fun prove_internal casms cprop tac =
  (case SINGLE (tac (map Assumption.assume casms)) (init cprop) of
    SOME th => Drule.implies_intr_list casms (finish th)
  | NONE => error "Tactic failed.");


(* prove_common etc. *)

fun prove_common immediate ctxt xs asms props tac =
  let
    val thy = ProofContext.theory_of ctxt;
    val string_of_term = Syntax.string_of_term ctxt;

    val pos = Position.thread_data ();
    fun err msg = cat_error msg
      ("The error(s) above occurred for the goal statement:\n" ^
        string_of_term (Logic.list_implies (asms, Logic.mk_conjunction_list props)) ^
        (case Position.str_of pos of "" => "" | s => "\n" ^ s));

    fun cert_safe t = Thm.cterm_of thy (Envir.beta_norm (Term.no_dummy_patterns t))
      handle TERM (msg, _) => err msg | TYPE (msg, _, _) => err msg;
    val casms = map cert_safe asms;
    val cprops = map cert_safe props;

    val (prems, ctxt') = ctxt
      |> Variable.add_fixes_direct xs
      |> fold Variable.declare_term (asms @ props)
      |> Assumption.add_assumes casms
      ||> Variable.set_body true;

    val stmt = Conjunction.mk_conjunction_balanced cprops;

    fun result () =
      (case SINGLE (tac {prems = prems, context = ctxt'}) (init stmt) of
        NONE => err "Tactic failed."
      | SOME st =>
          let val res = finish st handle THM (msg, _, _) => err msg in
            if Unify.matches_list thy [Thm.term_of stmt] [Thm.prop_of res] then res
            else err ("Proved a different theorem: " ^ string_of_term (Thm.prop_of res))
          end);
    val res =
      if immediate orelse #maxidx (Thm.rep_cterm stmt) >= 0 then result ()
      else promise_result ctxt' result (Thm.term_of stmt);
  in
    Conjunction.elim_balanced (length props) res
    |> map (Assumption.export false ctxt' ctxt)
    |> Variable.export ctxt' ctxt
    |> map Drule.zero_var_indexes
  end;

val prove_multi = prove_common true;

fun prove_promise ctxt xs asms prop tac = hd (prove_common false ctxt xs asms [prop] tac);
fun prove ctxt xs asms prop tac = hd (prove_common true ctxt xs asms [prop] tac);

fun prove_global thy xs asms prop tac =
  Drule.standard (prove (ProofContext.init thy) xs asms prop tac);



(** goal structure **)

(* nested goals *)

fun extract i n st =
  (if i < 1 orelse n < 1 orelse i + n - 1 > Thm.nprems_of st then Seq.empty
   else if n = 1 then Seq.single (Thm.cprem_of st i)
   else
     Seq.single (Conjunction.mk_conjunction_balanced (map (Thm.cprem_of st) (i upto i + n - 1))))
  |> Seq.map (Thm.adjust_maxidx_cterm ~1 #> init);

fun retrofit i n st' st =
  (if n = 1 then st
   else st |> Drule.with_subgoal i (Conjunction.uncurry_balanced n))
  |> Thm.compose_no_flatten false (conclude st', Thm.nprems_of st') i;

fun SELECT_GOAL tac i st =
  if Thm.nprems_of st = 1 andalso i = 1 then tac st
  else Seq.lifts (retrofit i 1) (Seq.maps tac (extract i 1 st)) st;


(* multiple goals *)

fun precise_conjunction_tac 0 i = eq_assume_tac i
  | precise_conjunction_tac 1 i = SUBGOAL (K all_tac) i
  | precise_conjunction_tac n i = PRIMITIVE (Drule.with_subgoal i (Conjunction.curry_balanced n));

val adhoc_conjunction_tac = REPEAT_ALL_NEW
  (SUBGOAL (fn (goal, i) =>
    if can Logic.dest_conjunction goal then rtac Conjunction.conjunctionI i
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

val norm_hhf_tac =
  rtac Drule.asm_rl  (*cheap approximation -- thanks to builtin Logic.flatten_params*)
  THEN' SUBGOAL (fn (t, i) =>
    if Drule.is_norm_hhf t then all_tac
    else MetaSimplifier.rewrite_goal_tac [Drule.norm_hhf_eq] i);

fun compose_hhf_tac th i st =
  PRIMSEQ (Thm.bicompose false (false, Drule.lift_all (Thm.cprem_of st i) th, 0) i) st;


(* non-atomic goal assumptions *)

fun non_atomic (Const ("==>", _) $ _ $ _) = true
  | non_atomic (Const ("all", _) $ _) = true
  | non_atomic _ = false;

fun assume_rule_tac ctxt = norm_hhf_tac THEN' CSUBGOAL (fn (goal, i) =>
  let
    val ((_, goal'), ctxt') = Variable.focus goal ctxt;
    val goal'' = Drule.cterm_rule (singleton (Variable.export ctxt' ctxt)) goal';
    val Rs = filter (non_atomic o Thm.term_of) (Drule.strip_imp_prems goal'');
    val tacs = Rs |> map (fn R =>
      Tactic.etac (MetaSimplifier.norm_hhf (Thm.trivial R)) THEN_ALL_NEW assume_tac);
  in fold_rev (curry op APPEND') tacs (K no_tac) i end);

end;

structure BasicGoal: BASIC_GOAL = Goal;
open BasicGoal;
