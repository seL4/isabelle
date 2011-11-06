(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_minimize.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of fact list for Metis using external provers.
*)

signature SLEDGEHAMMER_MINIMIZE =
sig
  type locality = ATP_Translate.locality
  type play = ATP_Reconstruct.play
  type params = Sledgehammer_Provers.params

  val binary_min_facts : int Config.T
  val minimize_facts :
    string -> params -> bool -> int -> int -> Proof.state
    -> ((string * locality) * thm list) list
    -> ((string * locality) * thm list) list option
       * ((unit -> play) * (play -> string) * string)
  val run_minimize :
    params -> int -> (Facts.ref * Attrib.src list) list -> Proof.state -> unit
end;

structure Sledgehammer_Minimize : SLEDGEHAMMER_MINIMIZE =
struct

open ATP_Util
open ATP_Proof
open ATP_Translate
open ATP_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_Provers

(* wrapper for calling external prover *)

fun n_facts names =
  let val n = length names in
    string_of_int n ^ " fact" ^ plural_s n ^
    (if n > 0 then
       ": " ^ (names |> map fst |> sort_distinct string_ord
                     |> space_implode " ")
     else
       "")
  end

fun print silent f = if silent then () else Output.urgent_message (f ())

fun test_facts ({debug, verbose, overlord, provers, max_mono_iters,
                 max_new_mono_instances, type_enc, isar_proof,
                 isar_shrink_factor, preplay_timeout, ...} : params)
               silent (prover : prover) timeout i n state facts =
  let
    val _ =
      print silent (fn () =>
          "Testing " ^ n_facts (map fst facts) ^
          (if verbose then " (timeout: " ^ string_from_time timeout ^ ")"
           else "") ^ "...")
    val {goal, ...} = Proof.goal state
    val facts =
      facts |> maps (fn (n, ths) => ths |> map (Untranslated_Fact o pair n))
    val params =
      {debug = debug, verbose = verbose, overlord = overlord, blocking = true,
       provers = provers, type_enc = type_enc, sound = true,
       relevance_thresholds = (1.01, 1.01), max_relevant = SOME (length facts),
       max_mono_iters = max_mono_iters,
       max_new_mono_instances = max_new_mono_instances, isar_proof = isar_proof,
       isar_shrink_factor = isar_shrink_factor, slicing = false,
       timeout = timeout, preplay_timeout = preplay_timeout, expect = ""}
    val problem =
      {state = state, goal = goal, subgoal = i, subgoal_count = n,
       facts = facts, smt_filter = NONE}
    val result as {outcome, used_facts, run_time_in_msecs, ...} =
      prover params (K (K "")) problem
  in
    print silent
          (fn () =>
              case outcome of
                SOME failure => string_for_failure failure
              | NONE =>
                "Found proof" ^
                 (if length used_facts = length facts then ""
                  else " with " ^ n_facts used_facts) ^
                 (case run_time_in_msecs of
                    SOME ms =>
                    " (" ^ string_from_time (Time.fromMilliseconds ms) ^ ")"
                  | NONE => "") ^ ".");
    result
  end

(* minimalization of facts *)

(* The sublinear algorithm works well in almost all situations, except when the
   external prover cannot return the list of used facts and hence returns all
   facts as used. In that case, the binary algorithm is much more appropriate.
   We can usually detect the situation by looking at the number of used facts
   reported by the prover. *)
val binary_min_facts =
  Attrib.setup_config_int @{binding sledgehammer_minimize_binary_min_facts}
                          (K 20)

fun sublinear_minimize _ [] p = p
  | sublinear_minimize test (x :: xs) (seen, result) =
    case test (xs @ seen) of
      result as {outcome = NONE, used_facts, ...} : prover_result =>
      sublinear_minimize test (filter_used_facts used_facts xs)
                         (filter_used_facts used_facts seen, result)
    | _ => sublinear_minimize test xs (x :: seen, result)

fun binary_minimize test xs =
  let
    fun pred xs = #outcome (test xs : prover_result) = NONE
    fun min _ _ [] = raise Empty
      | min _ _ [s0] = [s0]
      | min depth sup xs =
        let
          val (l0, r0) = chop ((length xs + 1) div 2) xs
(*
          val _ = warning (replicate_string depth " " ^ "{ " ^
                           "sup: " ^ n_facts (map fst sup))
          val _ = warning (replicate_string depth " " ^ "  " ^
                           "xs: " ^ n_facts (map fst xs))
          val _ = warning (replicate_string depth " " ^ "  " ^
                           "l0: " ^ n_facts (map fst l0))
          val _ = warning (replicate_string depth " " ^ "  " ^
                           "r0: " ^ n_facts (map fst r0))
*)
        in
          if pred (sup @ l0) then
            min (depth + 1) sup l0
          else if pred (sup @ r0) then
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
        [x] => if pred [] then [] else [x]
      | xs => xs
  in (xs, test xs) end

(* Give the external prover some slack. The ATP gets further slack because the
   Sledgehammer preprocessing time is included in the estimate below but isn't
   part of the timeout. *)
val slack_msecs = 200

fun minimize_facts prover_name (params as {timeout, ...}) silent i n state
                   facts =
  let
    val ctxt = Proof.context_of state
    val prover = get_prover ctxt Minimize prover_name
    val msecs = Time.toMilliseconds timeout
    val _ = print silent (fn () => "Sledgehammer minimizer: " ^
                                   quote prover_name ^ ".")
    fun do_test timeout = test_facts params silent prover timeout i n state
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
         val (min_facts, {preplay, message, message_tail, ...}) =
           if length facts >= Config.get ctxt binary_min_facts then
             binary_minimize (do_test new_timeout) facts
           else
             sublinear_minimize (do_test new_timeout) facts ([], result)
         val _ = print silent (fn () => cat_lines
           ["Minimized to " ^ n_facts (map fst min_facts)] ^
            (case length (filter (curry (op =) Chained o snd o fst) min_facts) of
               0 => ""
             | n => "\n(including " ^ string_of_int n ^ " chained)") ^ ".")
       in (SOME min_facts, (preplay, message, message_tail)) end
     | {outcome = SOME TimedOut, preplay, ...} =>
       (NONE,
        (preplay,
         fn _ => "Timeout: You can increase the time limit using the \
                 \\"timeout\" option (e.g., \"timeout = " ^
                 string_of_int (10 + msecs div 1000) ^ "\").",
         ""))
     | {preplay, message, ...} =>
       (NONE, (preplay, prefix "Prover error: " o message, "")))
    handle ERROR msg =>
           (NONE, (K (Failed_to_Play Metis), fn _ => "Error: " ^ msg, ""))
  end

fun run_minimize (params as {provers, ...}) i refs state =
  let
    val ctxt = Proof.context_of state
    val reserved = reserved_isar_keyword_table ()
    val chained_ths = normalize_chained_theorems (#facts (Proof.goal state))
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
              minimize_facts prover params false i n state facts
              |> (fn (_, (preplay, message, message_tail)) =>
                     message (preplay ()) ^ message_tail
                     |> Output.urgent_message))
  end

end;
