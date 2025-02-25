(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML
    Author:     Jasmin Blanchette, LMU Muenchen

Isabelle tactics as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_TACTIC =
sig
  type stature = ATP_Problem_Generate.stature
  type mode = Sledgehammer_Prover.mode
  type prover = Sledgehammer_Prover.prover
  type base_slice = Sledgehammer_ATP_Systems.base_slice

  val autoN : string
  val blastN : string
  val simpN : string

  val tactic_provers : string list
  val is_tactic_prover : string -> bool
  val good_slices_of_tactic_prover : string -> base_slice list
  val run_tactic_prover : mode -> string -> prover
end;

structure Sledgehammer_Prover_Tactic : SLEDGEHAMMER_PROVER_TACTIC =
struct

open ATP_Problem_Generate
open ATP_Proof
open Sledgehammer_ATP_Systems
open Sledgehammer_Proof_Methods
open Sledgehammer_Prover

val autoN = "auto"
val blastN = "blast"
val simpN = "simp"

val tactic_provers = [autoN, blastN, simpN]

val is_tactic_prover = member (op =) tactic_provers

val meshN = "mesh"

fun good_slices_of_tactic_prover name =
  (* FUDGE *)
  [(1, false, false, 0, meshN),
   (1, false, false, 2, meshN),
   (1, false, false, 4, meshN),
   (1, false, false, 8, meshN),
   (1, false, false, 16, meshN)]

(* In sync with Sledgehammer_Proof_Methods.tac_of_proof_method *)
fun tac_of ctxt name (local_facts, global_facts) =
  if name = autoN then
    Method.insert_tac ctxt (local_facts @ global_facts) THEN'
    SELECT_GOAL (Clasimp.auto_tac ctxt)
  else if name = blastN then
    Method.insert_tac ctxt (local_facts @ global_facts) THEN'
    blast_tac ctxt
  else if name = simpN then
    Method.insert_tac ctxt local_facts THEN'
    Simplifier.asm_full_simp_tac (ctxt addsimps global_facts)
  else
    error ("Unknown tactic: " ^ quote name)

fun meth_of name =
  if name = autoN then
    Auto_Method
  else if name = blastN then
    Blast_Method
  else if name = simpN then
    Simp_Method
  else
    error ("Unknown tactic: " ^ quote name)

fun run_tactic_prover mode name ({timeout, ...} : params)
    ({state, goal, subgoal, subgoal_count, factss, found_something, ...} : prover_problem) slice =
  let
    val (basic_slice, No_Slice) = slice
    val facts = facts_of_basic_slice basic_slice factss
    val {facts = chained, ...} = Proof.goal state
    val ctxt = Proof.context_of state

    val (local_facts, global_facts) =
      ([], [])
      |> fold (fn fact => if fst (snd (fst fact)) = Global then apsnd (cons (snd fact))
        else apfst (cons (snd fact))) facts
      |> apfst (append chained)

    val timer = Timer.startRealTimer ()

    val out =
      (Timeout.apply timeout
         (Goal.prove ctxt [] [] (Logic.get_goal (Thm.prop_of goal) subgoal))
         (fn {context = ctxt, ...} =>
            HEADGOAL (tac_of ctxt name (local_facts, global_facts)));
       NONE)
      handle ERROR _ => SOME GaveUp
           | Timeout.TIMEOUT _ => SOME TimedOut

    val run_time = Timer.checkRealTimer timer

    val (outcome, used_facts) =
      (case out of
        NONE =>
        (found_something name;
         (NONE, map fst facts))
      | some_failure => (some_failure, []))

    val message = fn _ =>
      (case outcome of
        NONE =>
        one_line_proof_text ((used_facts, (meth_of name, Played run_time)), proof_banner mode name,
          subgoal, subgoal_count)
      | SOME failure => string_of_atp_failure failure)
  in
    {outcome = outcome, used_facts = used_facts, used_from = facts,
     preferred_methss = (meth_of name, []), run_time = run_time, message = message}
  end

end;
