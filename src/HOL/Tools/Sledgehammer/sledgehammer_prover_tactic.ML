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

  val algebraN : string
  val argoN : string
  val autoN : string
  val blastN : string
  val fastforceN : string
  val forceN : string
  val linarithN : string
  val mesonN : string
  val metisN : string
  val orderN : string
  val presburgerN : string
  val satxN : string
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

val algebraN = "algebra"
val argoN = "argo"
val autoN = "auto"
val blastN = "blast"
val fastforceN = "fastforce"
val forceN = "force"
val linarithN = "linarith"
val mesonN = "meson"
val metisN = "metis"
val orderN = "order"
val presburgerN = "presburger"
val satxN = "satx"
val simpN = "simp"

val tactic_provers =
  [algebraN, argoN, autoN, blastN, fastforceN, forceN, linarithN, mesonN,
   metisN, orderN, presburgerN, satxN, simpN]

val is_tactic_prover = member (op =) tactic_provers

val meshN = "mesh"

fun good_slices_of_tactic_prover _ =
  (* FUDGE *)
  [(1, false, false, 0, meshN),
   (1, false, false, 2, meshN),
   (1, false, false, 8, meshN),
   (1, false, false, 32, meshN)]

fun meth_of name =
  if name = algebraN then Algebra_Method
  else if name = argoN then Argo_Method
  else if name = autoN then Auto_Method
  else if name = blastN then Blast_Method
  else if name = fastforceN then Fastforce_Method
  else if name = forceN then Force_Method
  else if name = linarithN then Linarith_Method
  else if name = mesonN then Meson_Method
  else if name = metisN then Metis_Method (NONE, NONE, [])
  else if name = orderN then Order_Method
  else if name = presburgerN then Presburger_Method
  else if name = satxN then SATx_Method
  else if name = simpN then Simp_Method
  else error ("Unknown tactic: " ^ quote name)

fun tac_of ctxt name (local_facts, global_facts) =
  Sledgehammer_Proof_Methods.tac_of_proof_method ctxt (local_facts, global_facts) (meth_of name)

fun run_tactic_prover mode name ({slices, timeout, ...} : params)
    ({state, goal, subgoal, subgoal_count, factss, found_something, ...} : prover_problem) slice =
  let
    val (basic_slice as (slice_size, _, _, _, _), No_Slice) = slice
    val facts = facts_of_basic_slice basic_slice factss
    val ctxt = Proof.context_of state

    fun run_try0 () : Try0.result option =
      let
        val _ = Proof_Context.get_fact
        val _ = Args.named_fact
        val _ = Pretty.pure_string_of
        val _ = Thm.pretty_thm
        val run_timeout = slice_timeout slice_size slices timeout
        fun is_cartouche str = String.isPrefix "\<open>" str andalso String.isSuffix "\<close>" str
        fun xref_of_fact (((name, (_, status)), thm) : Sledgehammer_Fact.fact) =
            let
              val xref =
                if is_cartouche name then
                  (* Facts.Fact (Thm.string_of_thm ctxt thm |> @{print}) *)
                  Facts.Fact (Pretty.pure_string_of (Thm.pretty_thm ctxt thm) |> @{print})
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
    val out =
      (case run_try0 () of
        NONE => SOME GaveUp
      | SOME _ => NONE)
      handle ERROR _ => SOME GaveUp
           | Exn.Interrupt_Breakdown => SOME GaveUp
           | Timeout.TIMEOUT _ => SOME TimedOut
    val run_time = Timer.checkRealTimer timer

    val (outcome, used_facts) =
      (case out of
        NONE => (found_something name; (NONE, map fst facts))
      | some_failure => (some_failure, []))

    val message = fn _ =>
      (case outcome of
        NONE =>
        one_line_proof_text ((map (apfst Pretty.str) used_facts, (meth_of name, Played run_time)),
          proof_banner mode name, subgoal, subgoal_count)
      | SOME failure => string_of_atp_failure failure)
  in
    {outcome = outcome, used_facts = used_facts, used_from = facts,
     preferred_methss = (meth_of name, []), run_time = run_time, message = message}
  end

end;
