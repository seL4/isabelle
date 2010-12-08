(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_minimize.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of fact list for Metis using external provers.
*)

signature SLEDGEHAMMER_MINIMIZE =
sig
  type locality = Sledgehammer_Filter.locality
  type params = Sledgehammer_Provers.params

  val filter_used_facts :
    (string * locality) list -> ((string * locality) * thm list) list
    -> ((string * locality) * thm list) list
  val minimize_facts :
    params -> bool -> int -> int -> Proof.state
    -> ((string * locality) * thm list) list
    -> ((string * locality) * thm list) list option * string
  val run_minimize :
    params -> int -> (Facts.ref * Attrib.src list) list -> Proof.state -> unit
end;

structure Sledgehammer_Minimize : SLEDGEHAMMER_MINIMIZE =
struct

open ATP_Proof
open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_Provers

(* wrapper for calling external prover *)

fun string_for_failure ATP_Proof.Unprovable = "Unprovable."
  | string_for_failure ATP_Proof.TimedOut = "Timed out."
  | string_for_failure ATP_Proof.Interrupted = "Interrupted."
  | string_for_failure _ = "Error."

fun n_facts names =
  let val n = length names in
    string_of_int n ^ " fact" ^ plural_s n ^
    (if n > 0 then
       ": " ^ (names |> map fst
                     |> sort_distinct string_ord |> space_implode " ")
     else
       "")
  end

fun print silent f = if silent then () else Output.urgent_message (f ())

fun test_facts ({debug, overlord, provers, full_types, isar_proof,
                 isar_shrink_factor, ...} : params) silent (prover : prover)
               explicit_apply timeout i n state facts =
  let
    val _ = print silent (fn () => "Testing " ^ n_facts (map fst facts) ^ "...")
    val params =
      {blocking = true, debug = debug, verbose = false, overlord = overlord,
       provers = provers, full_types = full_types,
       explicit_apply = explicit_apply, relevance_thresholds = (1.01, 1.01),
       max_relevant = NONE, isar_proof = isar_proof,
       isar_shrink_factor = isar_shrink_factor, timeout = timeout, expect = ""}
    val facts =
      facts |> maps (fn (n, ths) => ths |> map (Untranslated_Fact o pair n))
    val {goal, ...} = Proof.goal state
    val problem =
      {state = state, goal = goal, subgoal = i, subgoal_count = n,
       facts = facts}
    val result as {outcome, used_facts, ...} = prover params (K "") problem
  in
    print silent
        (fn () => case outcome of
                    SOME failure => string_for_failure failure
                  | NONE =>
                    if length used_facts = length facts then "Found proof."
                    else "Found proof with " ^ n_facts used_facts ^ ".");
    result
  end

(* minimalization of facts *)

(* The sublinear algorithm works well in almost all situations, except when the
   external prover cannot return the list of used facts and hence returns all
   facts as used. In that case, the binary algorithm is much more
   appropriate. We can usually detect that situation just by looking at the
   number of used facts reported by the prover. *)
val binary_threshold = 50

fun filter_used_facts used = filter (member (op =) used o fst)

fun sublinear_minimize _ [] p = p
  | sublinear_minimize test (x :: xs) (seen, result) =
    case test (xs @ seen) of
      result as {outcome = NONE, used_facts, ...} : prover_result =>
      sublinear_minimize test (filter_used_facts used_facts xs)
                         (filter_used_facts used_facts seen, result)
    | _ => sublinear_minimize test xs (x :: seen, result)

fun binary_minimize test xs =
  let
    fun p xs = #outcome (test xs : prover_result) = NONE
    fun split [] p = p
      | split [h] (l, r) = (h :: l, r)
      | split (h1 :: h2 :: t) (l, r) = split t (h1 :: l, h2 :: r)
    fun min _ [] = raise Empty
      | min _ [s0] = [s0]
      | min sup xs =
        let val (l0, r0) = split xs ([], []) in
          if p (sup @ l0) then
            min sup l0
          else if p (sup @ r0) then
            min sup r0
          else
            let
              val l = min (sup @ r0) l0
              val r = min (sup @ l) r0
            in l @ r end
        end
    val xs =
      case min [] xs of
        [x] => if p [] then [] else [x]
      | xs => xs
  in (xs, test xs) end

(* Give the external prover some slack. The ATP gets further slack because the
   Sledgehammer preprocessing time is included in the estimate below but isn't
   part of the timeout. *)
val fudge_msecs = 1000

fun minimize_facts {provers = [], ...} _ _ _ _ _ = error "No prover is set."
  | minimize_facts (params as {provers = prover_name :: _, timeout, ...}) silent
                   i n state facts =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val prover = get_prover ctxt false prover_name
    val msecs = Time.toMilliseconds timeout
    val _ = print silent (fn () => "Sledgehammer minimize: " ^
                                   quote prover_name ^ ".")
    val {goal, ...} = Proof.goal state
    val (_, hyp_ts, concl_t) = strip_subgoal goal i
    val explicit_apply =
      not (forall (Meson.is_fol_term thy)
                  (concl_t :: hyp_ts @ maps (map prop_of o snd) facts))
    fun do_test timeout =
      test_facts params silent prover explicit_apply timeout i n state
    val timer = Timer.startRealTimer ()
  in
    (case do_test timeout facts of
       result as {outcome = NONE, used_facts, ...} =>
       let
         val time = Timer.checkRealTimer timer
         val new_timeout =
           Int.min (msecs, Time.toMilliseconds time + fudge_msecs)
           |> Time.fromMilliseconds
         val facts = filter_used_facts used_facts facts
         val (min_thms, {message, ...}) =
           if length facts >= binary_threshold then
             binary_minimize (do_test new_timeout) facts
           else
             sublinear_minimize (do_test new_timeout) facts ([], result)
         val n = length min_thms
         val _ = print silent (fn () => cat_lines
           ["Minimized: " ^ string_of_int n ^ " fact" ^ plural_s n] ^
            (case length (filter (curry (op =) Chained o snd o fst) min_thms) of
               0 => ""
             | n => " (including " ^ Int.toString n ^ " chained)") ^ ".")
       in (SOME min_thms, message) end
     | {outcome = SOME TimedOut, ...} =>
       (NONE, "Timeout: You can increase the time limit using the \"timeout\" \
              \option (e.g., \"timeout = " ^
              string_of_int (10 + msecs div 1000) ^ "\").")
     | {outcome = SOME UnknownError, ...} =>
       (* Failure sometimes mean timeout, unfortunately. *)
       (NONE, "Failure: No proof was found with the current time limit. You \
              \can increase the time limit using the \"timeout\" \
              \option (e.g., \"timeout = " ^
              string_of_int (10 + msecs div 1000) ^ "\").")
     | {message, ...} => (NONE, "Prover error: " ^ message))
    handle ERROR msg => (NONE, "Error: " ^ msg)
  end

fun run_minimize params i refs state =
  let
    val ctxt = Proof.context_of state
    val reserved = reserved_isar_keyword_table ()
    val chained_ths = #facts (Proof.goal state)
    val facts =
      refs
      |> maps (map (apsnd single) o fact_from_ref ctxt reserved chained_ths)
  in
    case subgoal_count state of
      0 => Output.urgent_message "No subgoal!"
    | n =>
      (kill_provers ();
       Output.urgent_message (#2 (minimize_facts params false i n state facts)))
  end

end;
