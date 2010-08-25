(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact_minimize.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of theorem list for Metis using automatic theorem provers.
*)

signature SLEDGEHAMMER_FACT_MINIMIZE =
sig
  type params = Sledgehammer.params

  val minimize_theorems :
    params -> int -> int -> Proof.state -> ((string * bool) * thm list) list
    -> ((string * bool) * thm list) list option * string
  val run_minimize : params -> int -> Facts.ref list -> Proof.state -> unit
end;

structure Sledgehammer_Fact_Minimize : SLEDGEHAMMER_FACT_MINIMIZE =
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

fun n_theorems names =
  let val n = length names in
    string_of_int n ^ " theorem" ^ plural_s n ^
    (if n > 0 then
       ": " ^ (names |> map fst
                     |> sort_distinct string_ord |> space_implode " ")
     else
       "")
  end

fun test_theorems ({debug, verbose, overlord, atps, full_types,
                    relevance_threshold, relevance_decay, isar_proof,
                    isar_shrink_factor, ...} : params)
                  (prover : prover) explicit_apply timeout subgoal state
                  name_thms_pairs =
  let
    val _ =
      priority ("Testing " ^ n_theorems (map fst name_thms_pairs) ^ "...")
    val params =
      {debug = debug, verbose = verbose, overlord = overlord, atps = atps,
       full_types = full_types, explicit_apply = explicit_apply,
       relevance_threshold = relevance_threshold,
       relevance_decay = relevance_decay, max_relevant_per_iter = NONE,
       theory_relevant = NONE, isar_proof = isar_proof,
       isar_shrink_factor = isar_shrink_factor, timeout = timeout}
    val axioms = maps (fn (n, ths) => map (pair n) ths) name_thms_pairs
    val {context = ctxt, facts, goal} = Proof.goal state
    val problem =
     {subgoal = subgoal, goal = (ctxt, (facts, goal)),
      relevance_override = {add = [], del = [], only = false},
      axioms = SOME axioms}
    val result as {outcome, used_thm_names, ...} = prover params (K "") problem
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
      result as {outcome = NONE, proof, used_thm_names, ...} : prover_result =>
      sublinear_minimize test (filter_used_facts used_thm_names xs)
                         (filter_used_facts used_thm_names seen, result)
    | _ => sublinear_minimize test xs (x :: seen, result)

(* Give the ATP some slack. The ATP gets further slack because the Sledgehammer
   preprocessing time is included in the estimate below but isn't part of the
   timeout. *)
val fudge_msecs = 1000

fun minimize_theorems {atps = [], ...} _ _ _ _ = error "No ATP is set."
  | minimize_theorems
        (params as {debug, atps = atp :: _, full_types, isar_proof,
                    isar_shrink_factor, timeout, ...})
        i n state name_thms_pairs =
  let
    val thy = Proof.theory_of state
    val prover = get_prover_fun thy atp
    val msecs = Time.toMilliseconds timeout
    val _ = priority ("Sledgehammer minimize: ATP " ^ quote atp ^ ".")
    val {context = ctxt, goal, ...} = Proof.goal state
    val (_, hyp_ts, concl_t) = strip_subgoal goal i
    val explicit_apply =
      not (forall (Meson.is_fol_term thy)
                  (concl_t :: hyp_ts @
                   maps (map prop_of o snd) name_thms_pairs))
    fun do_test timeout =
      test_theorems params prover explicit_apply timeout i state
    val timer = Timer.startRealTimer ()
  in
    (case do_test timeout name_thms_pairs of
       result as {outcome = NONE, pool, used_thm_names,
                  conjecture_shape, ...} =>
       let
         val time = Timer.checkRealTimer timer
         val new_timeout =
           Int.min (msecs, Time.toMilliseconds time + fudge_msecs)
           |> Time.fromMilliseconds
         val (min_thms, {proof, axiom_names, ...}) =
           sublinear_minimize (do_test new_timeout)
               (filter_used_facts used_thm_names name_thms_pairs) ([], result)
         val n = length min_thms
         val _ = priority (cat_lines
           ["Minimized: " ^ string_of_int n ^ " theorem" ^ plural_s n] ^
            (case length (filter (snd o fst) min_thms) of
               0 => ""
             | n => " (including " ^ Int.toString n ^ " chained)") ^ ".")
       in
         (SOME min_thms,
          proof_text isar_proof
              (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
              (full_types, K "", proof, axiom_names, goal, i) |> fst)
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

fun run_minimize params i refs state =
  let
    val ctxt = Proof.context_of state
    val reserved = reserved_isar_keyword_table ()
    val chained_ths = #facts (Proof.goal state)
    val name_thms_pairs =
      map (apfst (fn f => f ())
           o name_thms_pair_from_ref ctxt reserved chained_ths) refs
  in
    case subgoal_count state of
      0 => priority "No subgoal!"
    | n =>
      (kill_atps ();
       priority (#2 (minimize_theorems params i n state name_thms_pairs)))
  end

end;
