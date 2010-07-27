(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact_minimizer.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of theorem list for Metis using automatic theorem provers.
*)

signature SLEDGEHAMMER_FACT_MINIMIZER =
sig
  type params = Sledgehammer.params
  type prover_result = Sledgehammer.prover_result

  val minimize_theorems :
    params -> int -> int -> Proof.state -> (string * thm list) list
    -> (string * thm list) list option * string
end;

structure Sledgehammer_Fact_Minimizer : SLEDGEHAMMER_FACT_MINIMIZER =
struct

open Metis_Clauses
open Sledgehammer_Util
open Sledgehammer_Proof_Reconstruct
open Sledgehammer

(* wrapper for calling external prover *)

fun string_for_failure Unprovable = "Unprovable."
  | string_for_failure IncompleteUnprovable = "Failed."
  | string_for_failure TimedOut = "Timed out."
  | string_for_failure OutOfResources = "Failed."
  | string_for_failure OldSpass = "Error."
  | string_for_failure MalformedOutput = "Error."
  | string_for_failure UnknownError = "Failed."
fun string_for_outcome NONE = "Success."
  | string_for_outcome (SOME failure) = string_for_failure failure

fun sledgehammer_test_theorems (params : params) prover timeout subgoal state
                               filtered_clauses name_thms_pairs =
  let
    val thy = Proof.theory_of state
    val num_theorems = length name_thms_pairs
    val _ =
      priority ("Testing " ^ string_of_int num_theorems ^
                " theorem" ^ plural_s num_theorems ^
                (if num_theorems > 0 then
                   ": " ^ space_implode " "
                              (name_thms_pairs
                               |> map fst |> sort_distinct string_ord)
                 else
                   "") ^ "...")
    val name_thm_pairs = maps (fn (n, ths) => map (pair n) ths) name_thms_pairs
    val {context = ctxt, facts, goal} = Proof.goal state
    val problem =
     {subgoal = subgoal, goal = (ctxt, (facts, goal)),
      relevance_override = {add = [], del = [], only = false},
      axiom_clauses = SOME name_thm_pairs,
      filtered_clauses = SOME (the_default name_thm_pairs filtered_clauses)}
  in
    prover params (K "") timeout problem
    |> tap (fn result : prover_result =>
         priority (string_for_outcome (#outcome result)))
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

fun minimize_theorems (params as {debug, atps, full_types, minimize_timeout,
                                  isar_proof, isar_shrink_factor, ...})
                      i n state name_thms_pairs =
  let
    val thy = Proof.theory_of state
    val prover = case atps of
                   [atp_name] => get_prover thy atp_name
                 | _ => error "Expected a single ATP."
    val msecs = Time.toMilliseconds minimize_timeout
    val _ =
      priority ("Sledgehammer minimizer: ATP " ^ quote (the_single atps) ^
                " with a time limit of " ^ string_of_int msecs ^ " ms.")
    val test_facts =
      sledgehammer_test_theorems params prover minimize_timeout i state
    val {context = ctxt, goal, ...} = Proof.goal state;
  in
    (* try prove first to check result and get used theorems *)
    (case test_facts NONE name_thms_pairs of
       result as {outcome = NONE, pool, proof, used_thm_names,
                  conjecture_shape, filtered_clauses, ...} =>
       let
         val (min_thms, {proof, internal_thm_names, ...}) =
           sublinear_minimize (test_facts (SOME filtered_clauses))
                              (filter_used_facts used_thm_names name_thms_pairs)
                              ([], result)
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

end;
