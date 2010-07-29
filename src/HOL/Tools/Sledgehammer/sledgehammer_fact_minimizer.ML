(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact_minimizer.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of theorem list for Metis using automatic theorem provers.
*)

signature SLEDGEHAMMER_FACT_MINIMIZER =
sig
  type params = Sledgehammer.params

  val minimize_theorems :
    params -> int -> int -> Proof.state -> (string * thm list) list
    -> (string * thm list) list option * string
  val run_minimizer : params -> int -> Facts.ref list -> Proof.state -> unit
end;

structure Sledgehammer_Fact_Minimizer : SLEDGEHAMMER_FACT_MINIMIZER =
struct

open ATP_Systems
open Sledgehammer_Util
open Sledgehammer_Fact_Filter
open Sledgehammer_Proof_Reconstruct
open Sledgehammer

(* wrapper for calling external prover *)

fun string_for_failure Unprovable = "Unprovable."
  | string_for_failure TimedOut = "Timed out."
  | string_for_failure _ = "Unknown error."

fun n_theorems name_thms_pairs =
  let val n = length name_thms_pairs in
    string_of_int n ^ " theorem" ^ plural_s n ^
    (if n > 0 then
       ": " ^ space_implode " " (sort_distinct string_ord name_thms_pairs)
     else
       "")
  end

fun sledgehammer_test_theorems (params : params) (prover : prover) timeout
                               subgoal state name_thms_pairs =
  let
    val _ =
      priority ("Testing " ^ n_theorems (map fst name_thms_pairs) ^ "...")
    val axioms = maps (fn (n, ths) => map (pair n) ths) name_thms_pairs
    val {context = ctxt, facts, goal} = Proof.goal state
    val problem =
     {subgoal = subgoal, goal = (ctxt, (facts, goal)),
      relevance_override = {add = [], del = [], only = false},
      axioms = SOME axioms}
    val result as {outcome, used_thm_names, ...} =
      prover params (K "") timeout problem
  in
    priority (case outcome of
                NONE =>
                if length used_thm_names = length name_thms_pairs then
                  "Found proof."
                else
                  "Found proof with " ^ n_theorems used_thm_names ^ "."
              | SOME failure => string_for_failure failure);
    result
  end

(* minimalization of thms *)

fun filter_used_facts used = filter (member (op =) used o fst)

fun sublinear_minimize _ [] p = p
  | sublinear_minimize test (x :: xs) (seen, result) =
    case test (xs @ seen) of
      result as {outcome = NONE, proof, used_thm_names, ...}
      : prover_result =>
      sublinear_minimize test (filter_used_facts used_thm_names xs)
                         (filter_used_facts used_thm_names seen, result)
    | _ => sublinear_minimize test xs (x :: seen, result)

(* Give the ATP some slack. The ATP gets further slack because the Sledgehammer
   preprocessing time is included in the estimate below but isn't part of the
   timeout. *)
val fudge_msecs = 250

fun minimize_theorems {atps = [], ...} _ _ _ _ = error "No ATP is set."
  | minimize_theorems
        (params as {debug, verbose, overlord, atps as atp :: _, full_types,
                    explicit_apply, relevance_threshold, relevance_convergence,
                    theory_relevant, defs_relevant, isar_proof,
                    isar_shrink_factor, minimize_timeout, ...})
        i n state name_thms_pairs =
  let
    val thy = Proof.theory_of state
    val prover = get_prover_fun thy atp
    val msecs = Time.toMilliseconds minimize_timeout
    val _ =
      priority ("Sledgehammer minimizer: ATP " ^ quote atp ^
                " with a time limit of " ^ string_of_int msecs ^ " ms.")
    fun test_facts timeout =
      sledgehammer_test_theorems params prover timeout i state
    val {context = ctxt, goal, ...} = Proof.goal state
    val timer = Timer.startRealTimer ()
  in
    (case test_facts minimize_timeout name_thms_pairs of
       result as {outcome = NONE, pool, used_thm_names,
                  conjecture_shape, ...} =>
       let
         val time = Timer.checkRealTimer timer
         val new_timeout =
           Int.min (msecs, Time.toMilliseconds time + fudge_msecs)
           |> Time.fromMilliseconds
         val (min_thms, {proof, internal_thm_names, ...}) =
           sublinear_minimize (test_facts new_timeout)
               (filter_used_facts used_thm_names name_thms_pairs) ([], result)
         val m = length min_thms
         val _ = priority (cat_lines
           ["Minimized: " ^ string_of_int m ^ " theorem" ^ plural_s m] ^ ".")
       in
         (SOME min_thms,
          proof_text isar_proof
              (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
              (full_types, K "", proof, internal_thm_names, goal, i) |> fst)
       end
     | {outcome = SOME TimedOut, ...} =>
       (NONE, "Timeout: You can increase the time limit using the \"timeout\" \
              \option (e.g., \"timeout = " ^
              string_of_int (10 + msecs div 1000) ^ " s\").")
     | {outcome = SOME UnknownError, ...} =>
       (* Failure sometimes mean timeout, unfortunately. *)
       (NONE, "Failure: No proof was found with the current time limit. You \
              \can increase the time limit using the \"timeout\" \
              \option (e.g., \"timeout = " ^
              string_of_int (10 + msecs div 1000) ^ " s\").")
     | {message, ...} => (NONE, "ATP error: " ^ message))
    handle ERROR msg => (NONE, "Error: " ^ msg)
  end

fun run_minimizer params i refs state =
  let
    val ctxt = Proof.context_of state
    val chained_ths = #facts (Proof.goal state)
    val name_thms_pairs = map (name_thms_pair_from_ref ctxt chained_ths) refs
  in
    case subgoal_count state of
      0 => priority "No subgoal!"
    | n =>
      (kill_atps ();
       priority (#2 (minimize_theorems params i n state name_thms_pairs)))
  end

end;
