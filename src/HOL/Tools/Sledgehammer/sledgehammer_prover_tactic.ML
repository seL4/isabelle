(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML
    Author:     Jasmin Blanchette, LMU Muenchen
    Author:     Martin Desharnais, LMU Muenchen

Isabelle tactics as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_TACTIC =
sig
  type stature = ATP_Problem_Generate.stature
  type mode = Sledgehammer_Prover.mode
  type prover = Sledgehammer_Prover.prover
  type base_slice = Sledgehammer_ATP_Systems.base_slice

  val is_tactic_prover : string -> bool
  val good_slices_of_tactic_prover : string -> base_slice list
  val run_tactic_prover : mode -> string -> prover
end;

structure Sledgehammer_Prover_Tactic : SLEDGEHAMMER_PROVER_TACTIC =
struct

open ATP_Proof
open Sledgehammer_Proof_Methods
open Sledgehammer_Prover

val is_tactic_prover : string -> bool = is_some o Try0.get_proof_method

local

val slices_of_max_facts = map (fn max_facts => (1, false, false, max_facts, "mesh"))

in

(* FUDGE *)
fun good_slices_of_tactic_prover "metis" = slices_of_max_facts [0, 64, 32, 8, 16, 4, 2, 1]
  | good_slices_of_tactic_prover "fastforce" = slices_of_max_facts [0, 16, 32, 8, 4, 64, 2, 1]
  | good_slices_of_tactic_prover "simp" = slices_of_max_facts [0, 16, 32, 8, 64, 4, 1, 2]
  | good_slices_of_tactic_prover "auto" = slices_of_max_facts [0, 16, 32, 8, 4, 64, 2, 1]
  | good_slices_of_tactic_prover _ = slices_of_max_facts [0, 2, 8, 16, 32, 64]

end

fun meth_of "algebra" = Algebra_Method
  | meth_of "argo" = Argo_Method
  | meth_of "auto" = Auto_Method
  | meth_of "blast" = Blast_Method
  | meth_of "fastforce" = Fastforce_Method
  | meth_of "force" = Force_Method
  | meth_of "linarith" = Linarith_Method
  | meth_of "meson" = Meson_Method
  | meth_of "metis" = Metis_Method (NONE, NONE, [])
  | meth_of "order" = Order_Method
  | meth_of "presburger" = Presburger_Method
  | meth_of "satx" = SATx_Method
  | meth_of "simp" = Simp_Method
  | meth_of _ = Metis_Method (NONE, NONE, [])

fun run_tactic_prover mode name ({slices, timeout, ...} : params)
    ({state, subgoal, subgoal_count, factss, found_something, ...} : prover_problem) slice =
  let
    val (basic_slice as (slice_size, _, _, _, _), No_Slice) = slice
    val facts = facts_of_basic_slice basic_slice factss
    val ctxt = Proof.context_of state

    fun run_try0 () : Try0.result option =
      let
        val run_timeout = slice_timeout slice_size slices timeout
        fun is_cartouche str = String.isPrefix "\<open>" str andalso String.isSuffix "\<close>" str
        fun xref_of_fact (((name, _), thm) : Sledgehammer_Fact.fact) =
            let
              val xref =
                if is_cartouche name then
                  Facts.Fact (Pretty.pure_string_of (Thm.pretty_thm ctxt thm))
                else
                  Facts.named name
            in
              (xref, [])
            end
        val xrefs = map xref_of_fact facts
        val facts : Try0.facts = {usings = xrefs, simps = [], intros = [], elims = [], dests = []}
      in
        Try0.get_proof_method_or_noop name (SOME run_timeout) facts state
      end

    val timer = Timer.startRealTimer ()
    val (outcome, command) =
      (case run_try0 () of
        NONE => (SOME GaveUp, "")
      | SOME {command, ...} => (NONE, command))
      handle ERROR _ => (SOME GaveUp, "")
           | Exn.Interrupt_Breakdown => (SOME GaveUp, "")
           | Timeout.TIMEOUT _ => (SOME TimedOut, "")
    val run_time = Timer.checkRealTimer timer

    val used_facts =
      (case outcome of
        NONE => (found_something name; map fst facts)
      | SOME _ => [])

    val message = fn _ =>
      (case outcome of
        NONE => try_command_line (proof_banner mode name) (Played run_time) command
      | SOME failure => string_of_atp_failure failure)
  in
    {outcome = outcome, used_facts = used_facts, used_from = facts,
     preferred_methss = (meth_of name, []), run_time = run_time, message = message}
  end

end;
