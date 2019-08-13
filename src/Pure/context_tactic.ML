(*  Title:      Pure/context_tactic.ML
    Author:     Makarius

Tactics with proof context / cases -- as basis for Isar proof methods.
*)

infix 1 CONTEXT_THEN_ALL_NEW;

signature BASIC_CONTEXT_TACTIC =
sig
  type context_state = Proof.context * thm
  type context_tactic = context_state -> context_state Seq.result Seq.seq
  val TACTIC_CONTEXT: Proof.context -> thm Seq.seq -> context_state Seq.result Seq.seq
  val CONTEXT_TACTIC: tactic -> context_tactic
  val NO_CONTEXT_TACTIC: Proof.context -> context_tactic -> tactic
  val CONTEXT_CASES: Rule_Cases.cases -> tactic -> context_tactic
  val CONTEXT_SUBGOAL: (term * int -> context_tactic) -> int -> context_tactic
  val CONTEXT_THEN_ALL_NEW: (int -> context_tactic) * (int -> tactic) -> int -> context_tactic
  val SUBPROOFS: context_tactic -> context_tactic
end;

signature CONTEXT_TACTIC =
sig
  include BASIC_CONTEXT_TACTIC
end;

structure Context_Tactic: CONTEXT_TACTIC =
struct

(* type context_tactic *)

type context_state = Proof.context * thm;
type context_tactic = context_state -> context_state Seq.result Seq.seq;

fun TACTIC_CONTEXT ctxt : thm Seq.seq -> context_state Seq.result Seq.seq =
  Seq.map (Seq.Result o pair ctxt);

fun CONTEXT_TACTIC tac : context_tactic =
  fn (ctxt, st) => TACTIC_CONTEXT ctxt (tac st);

fun NO_CONTEXT_TACTIC ctxt (tac: context_tactic) st =
  tac (ctxt, st) |> Seq.filter_results |> Seq.map snd;

fun CONTEXT_CASES cases tac : context_tactic =
  fn (ctxt, st) => TACTIC_CONTEXT (Proof_Context.update_cases cases ctxt) (tac st);

fun CONTEXT_SUBGOAL tac i : context_tactic =
  fn (ctxt, st) =>
    (case try Logic.nth_prem (i, Thm.prop_of st) of
      SOME goal => tac (goal, i) (ctxt, st)
    | NONE => Seq.empty);

fun (tac1 CONTEXT_THEN_ALL_NEW tac2) i : context_tactic =
  fn (ctxt, st) =>
    (ctxt, st) |> tac1 i |> Seq.maps_results (fn (ctxt', st') =>
      TACTIC_CONTEXT ctxt' ((Seq.INTERVAL tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st)) st'));


(* subproofs with closed derivation *)

fun SUBPROOFS tac : context_tactic =
  let
    fun apply (g :: gs) (SOME (Seq.Result (results, ctxt))) =
          (case Seq.pull (tac (ctxt, Goal.init g)) of
            SOME (Seq.Result (ctxt', st'), _) =>
              apply gs (SOME (Seq.Result (st' :: results, ctxt')))
          | SOME (Seq.Error msg, _) => SOME (Seq.Error msg)
          | NONE => NONE)
      | apply _ x = x;
  in
    fn (ctxt, st) =>
      (case Par_Tactical.strip_goals st of
        SOME goals =>
          (case apply goals (SOME (Seq.Result ([], ctxt))) of
            SOME (Seq.Result (results, ctxt')) =>
              TACTIC_CONTEXT ctxt' (Par_Tactical.retrofit_tac {close = true} results st)
          | SOME (Seq.Error msg) => Seq.single (Seq.Error msg)
          | NONE => Seq.empty)
      | NONE => Seq.DETERM tac (ctxt, st))
  end;

end;

structure Basic_Context_Tactic: BASIC_CONTEXT_TACTIC = Context_Tactic;
open Basic_Context_Tactic;
