(*  Title:      HOL/Tools/ATP_Manager/atp_minimal.ML
    Author:     Philipp Meyer, TU Muenchen

Minimization of theorem list for Metis using automatic theorem provers.
*)

signature ATP_MINIMAL =
sig
  type params = ATP_Manager.params
  type prover = ATP_Manager.prover
  type prover_result = ATP_Manager.prover_result

  val minimize_theorems :
    params -> prover -> string -> int -> Proof.state -> (string * thm list) list
    -> (string * thm list) list option * string
end;

structure ATP_Minimal : ATP_MINIMAL =
struct

open Sledgehammer_Util
open Sledgehammer_Fact_Preprocessor
open Sledgehammer_Proof_Reconstruct
open ATP_Manager

(* Linear minimization algorithm *)

fun linear_minimize test s =
  let
    fun aux [] p = p
      | aux (x :: xs) (needed, result) =
        case test (xs @ needed) of
          SOME result => aux xs (needed, result)
        | NONE => aux xs (x :: needed, result)
  in aux s end


(* failure check and producing answer *)

datatype outcome = Success | Failure | Timeout | Error

val string_of_outcome =
  fn Success => "Success"
   | Failure => "Failure"
   | Timeout => "Timeout"
   | Error => "Error"

val failure_strings =
  [("SPASS beiseite: Ran out of time.", Timeout),
   ("Timeout", Timeout),
   ("time limit exceeded", Timeout),
   ("# Cannot determine problem status within resource limit", Timeout),
   ("Error", Error)]

fun outcome_of_result (result as {success, proof, ...} : prover_result) =
  if success then
    Success
  else case get_first (fn (s, outcome) =>
                          if String.isSubstring s proof then SOME outcome
                          else NONE) failure_strings of
    SOME outcome => outcome
  | NONE => Failure

(* wrapper for calling external prover *)

fun sledgehammer_test_theorems (params as {full_types, ...} : params) prover
        timeout subgoal state filtered_clauses name_thms_pairs =
  let
    val num_theorems = length name_thms_pairs
    val _ = priority ("Testing " ^ string_of_int num_theorems ^
                      " theorem" ^ plural_s num_theorems ^ "...")
    val name_thm_pairs = maps (fn (n, ths) => map (pair n) ths) name_thms_pairs
    val axclauses = cnf_rules_pairs (Proof.theory_of state) name_thm_pairs
    val {context = ctxt, facts, goal} = Proof.goal state
    val problem =
     {subgoal = subgoal, goal = (ctxt, (facts, goal)),
      relevance_override = {add = [], del = [], only = false},
      axiom_clauses = SOME axclauses,
      filtered_clauses = SOME (the_default axclauses filtered_clauses)}
  in
    `outcome_of_result (prover params timeout problem)
    |>> tap (priority o string_of_outcome)
  end

(* minimalization of thms *)

fun minimize_theorems (params as {minimize_timeout, isar_proof, modulus,
                                  sorts, ...})
                      prover atp_name i state name_thms_pairs =
  let
    val msecs = Time.toMilliseconds minimize_timeout
    val n = length name_thms_pairs
    val _ =
      priority ("Sledgehammer minimizer: ATP " ^ quote atp_name ^
                " with a time limit of " ^ string_of_int msecs ^ " ms.")
    val test_thms_fun =
      sledgehammer_test_theorems params prover minimize_timeout i state
    fun test_thms filtered thms =
      case test_thms_fun filtered thms of
        (Success, result) => SOME result
      | _ => NONE

    val {context = ctxt, facts, goal} = Proof.goal state;
    val n = Logic.count_prems (prop_of goal)
  in
    (* try prove first to check result and get used theorems *)
    (case test_thms_fun NONE name_thms_pairs of
      (Success, result as {internal_thm_names, filtered_clauses, ...}) =>
        let
          val used = internal_thm_names |> Vector.foldr (op ::) []
                                        |> sort_distinct string_ord
          val to_use =
            if length used < length name_thms_pairs then
              filter (fn (name1, _) => List.exists (curry (op =) name1) used)
                     name_thms_pairs
            else name_thms_pairs
          val (min_thms, {proof, internal_thm_names, ...}) =
            linear_minimize (test_thms (SOME filtered_clauses)) to_use
                            ([], result)
          val n = length min_thms
          val _ = priority (cat_lines
            ["Minimized: " ^ string_of_int n ^ " theorem" ^ plural_s n] ^ ".")
        in
          (SOME min_thms,
           proof_text isar_proof true modulus sorts atp_name proof
                      internal_thm_names ctxt goal i |> fst)
        end
    | (Timeout, _) =>
        (NONE, "Timeout: You can increase the time limit using the \"timeout\" \
               \option (e.g., \"timeout = " ^
               string_of_int (10 + msecs div 1000) ^ " s\").")
    | (Error, {message, ...}) => (NONE, "ATP error: " ^ message)
    | (Failure, _) =>
        (* Failure sometimes mean timeout, unfortunately. *)
        (NONE, "Failure: No proof was found with the current time limit. You \
               \can increase the time limit using the \"timeout\" \
               \option (e.g., \"timeout = " ^
               string_of_int (10 + msecs div 1000) ^ " s\")."))
    handle Sledgehammer_HOL_Clause.TRIVIAL =>
        (SOME [], metis_line i n [])
      | ERROR msg => (NONE, "Error: " ^ msg)
  end

end;
