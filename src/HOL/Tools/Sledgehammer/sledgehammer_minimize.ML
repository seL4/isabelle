(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_minimize.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of fact list for Metis using external provers.
*)

signature SLEDGEHAMMER_MINIMIZE =
sig
  type locality = Sledgehammer_Filter.locality
  type params = Sledgehammer_Provers.params

  val binary_min_facts : int Unsynchronized.ref
  val filter_used_facts : ''a list -> (''a * 'b) list -> (''a * 'b) list
  val minimize_facts :
    string -> params -> bool option -> bool -> int -> int -> Proof.state
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

fun test_facts ({debug, verbose, overlord, provers, monomorphize_limit,
                 type_sys, isar_proof, isar_shrink_factor, ...} : params)
        explicit_apply_opt silent (prover : prover) timeout i n state facts =
  let
    val thy = Proof.theory_of state
    val _ =
      print silent (fn () =>
          "Testing " ^ n_facts (map fst facts) ^
          (if verbose then " (timeout: " ^ string_from_time timeout ^ ")"
          else "") ^ "...")
    val {goal, ...} = Proof.goal state
    val explicit_apply =
      case explicit_apply_opt of
        SOME explicit_apply => explicit_apply
      | NONE =>
        let val (_, hyp_ts, concl_t) = strip_subgoal goal i in
          not (forall (Meson.is_fol_term thy)
                      (concl_t :: hyp_ts @ maps (map prop_of o snd) facts))
        end
    val params =
      {debug = debug, verbose = verbose, overlord = overlord, blocking = true,
       provers = provers, type_sys = type_sys, explicit_apply = explicit_apply,
       relevance_thresholds = (1.01, 1.01), max_relevant = NONE,
       monomorphize = false, monomorphize_limit = monomorphize_limit,
       isar_proof = isar_proof, isar_shrink_factor = isar_shrink_factor,
       timeout = timeout, expect = ""}
    val facts =
      facts |> maps (fn (n, ths) => ths |> map (Untranslated_Fact o pair n))
    val problem =
      {state = state, goal = goal, subgoal = i, subgoal_count = n,
       facts = facts, smt_filter = NONE}
    val result as {outcome, used_facts, ...} = prover params (K "") problem
  in
    print silent (fn () =>
        case outcome of
          SOME failure => string_for_failure failure
        | NONE => if length used_facts = length facts then "Found proof."
                  else "Found proof with " ^ n_facts used_facts ^ ".");
    result
  end

(* minimalization of facts *)

(* The sublinear algorithm works well in almost all situations, except when the
   external prover cannot return the list of used facts and hence returns all
   facts as used. In that case, the binary algorithm is much more appropriate.
   We can usually detect the situation by looking at the number of used facts
   reported by the prover. *)
val binary_min_facts = Unsynchronized.ref 20

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
    fun min _ _ [] = raise Empty
      | min _ _ [s0] = [s0]
      | min depth sup xs =
        let
(*
          val _ = warning (replicate_string depth " " ^ "{" ^ ("  " ^
                           n_facts (map fst sup) ^ " and " ^
                           n_facts (map fst xs)))
*)
          val (l0, r0) = split xs ([], [])
        in
          if p (sup @ l0) then
            min (depth + 1) sup l0
          else if p (sup @ r0) then
            min (depth + 1) sup r0
          else
            let
              val l = min (depth + 1) (sup @ r0) l0
              val r = min (depth + 1) (sup @ l) r0
            in l @ r end
        end
(*
        |> tap (fn _ => warning (replicate_string depth " " ^ "}"))
*)
    val xs =
      case min 0 [] xs of
        [x] => if p [] then [] else [x]
      | xs => xs
  in (xs, test xs) end

(* Give the external prover some slack. The ATP gets further slack because the
   Sledgehammer preprocessing time is included in the estimate below but isn't
   part of the timeout. *)
val slack_msecs = 200

fun minimize_facts prover_name (params as {timeout, ...}) explicit_apply_opt
                   silent i n state facts =
  let
    val ctxt = Proof.context_of state
    val prover = get_prover ctxt false prover_name
    val msecs = Time.toMilliseconds timeout
    val _ = print silent (fn () => "Sledgehammer minimize: " ^
                                   quote prover_name ^ ".")
    fun do_test timeout =
      test_facts params explicit_apply_opt silent prover timeout i n state
    val timer = Timer.startRealTimer ()
  in
    (case do_test timeout facts of
       result as {outcome = NONE, used_facts, ...} =>
       let
         val time = Timer.checkRealTimer timer
         val new_timeout =
           Int.min (msecs, Time.toMilliseconds time + slack_msecs)
           |> Time.fromMilliseconds
         val facts = filter_used_facts used_facts facts
         val (min_thms, {message, ...}) =
           if length facts >= !binary_min_facts then
             binary_minimize (do_test new_timeout) facts
           else
             sublinear_minimize (do_test new_timeout) facts ([], result)
         val n = length min_thms
         val _ = print silent (fn () => cat_lines
           ["Minimized: " ^ string_of_int n ^ " fact" ^ plural_s n] ^
            (case length (filter (curry (op =) Chained o snd o fst) min_thms) of
               0 => ""
             | n => " (including " ^ string_of_int n ^ " chained)") ^ ".")
       in (SOME min_thms, message) end
     | {outcome = SOME TimedOut, ...} =>
       (NONE, "Timeout: You can increase the time limit using the \"timeout\" \
              \option (e.g., \"timeout = " ^
              string_of_int (10 + msecs div 1000) ^ "\").")
     | {message, ...} => (NONE, "Prover error: " ^ message))
    handle ERROR msg => (NONE, "Error: " ^ msg)
  end

fun run_minimize (params as {provers, ...}) i refs state =
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
    | n => case provers of
             [] => error "No prover is set."
           | prover :: _ =>
             (kill_provers ();
              minimize_facts prover params NONE false i n state facts
              |> #2 |> Output.urgent_message)
  end

end;
