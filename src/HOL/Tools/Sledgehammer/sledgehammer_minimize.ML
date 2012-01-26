(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_minimize.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of fact list for Metis using external provers.
*)

signature SLEDGEHAMMER_MINIMIZE =
sig
  type stature = ATP_Problem_Generate.stature
  type play = ATP_Proof_Reconstruct.play
  type params = Sledgehammer_Provers.params

  val binary_min_facts : int Config.T
  val minimize_facts :
    string -> params -> bool -> int -> int -> Proof.state
    -> ((string * stature) * thm list) list
    -> ((string * stature) * thm list) list option
       * ((unit -> play) * (play -> string) * string)
  val run_minimize :
    params -> int -> (Facts.ref * Attrib.src list) list -> Proof.state -> unit
end;

structure Sledgehammer_Minimize : SLEDGEHAMMER_MINIMIZE =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
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
                 max_new_mono_instances, type_enc, strict, lam_trans,
                 isar_proof, isar_shrink_factor, preplay_timeout, ...} : params)
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
       provers = provers, type_enc = type_enc, strict = strict,
       lam_trans = lam_trans, relevance_thresholds = (1.01, 1.01),
       max_relevant = SOME (length facts), max_mono_iters = max_mono_iters,
       max_new_mono_instances = max_new_mono_instances, isar_proof = isar_proof,
       isar_shrink_factor = isar_shrink_factor, slice = false,
       minimize = SOME false, timeout = timeout,
       preplay_timeout = preplay_timeout, expect = ""}
    val problem =
      {state = state, goal = goal, subgoal = i, subgoal_count = n,
       facts = facts, smt_filter = NONE}
    val result as {outcome, used_facts, run_time, ...} =
      prover params (K (K (K ""))) problem
  in
    print silent
          (fn () =>
              case outcome of
                SOME failure => string_for_failure failure
              | NONE =>
                "Found proof" ^
                 (if length used_facts = length facts then ""
                  else " with " ^ n_facts used_facts) ^
                 " (" ^ string_from_time run_time ^ ").");
    result
  end

(* minimalization of facts *)

(* Give the external prover some slack. The ATP gets further slack because the
   Sledgehammer preprocessing time is included in the estimate below but isn't
   part of the timeout. *)
val slack_msecs = 200

fun new_timeout timeout run_time =
  Int.min (Time.toMilliseconds timeout,
           Time.toMilliseconds run_time + slack_msecs)
  |> Time.fromMilliseconds

(* The linear algorithm usually outperforms the binary algorithm when over 60%
   of the facts are actually needed. The binary algorithm is much more
   appropriate for provers that cannot return the list of used facts and hence
   returns all facts as used. Since we cannot know in advance how many facts are
   actually needed, we heuristically set the threshold to 10 facts. *)
val binary_min_facts =
  Attrib.setup_config_int @{binding sledgehammer_minimize_binary_min_facts}
                          (K 20)

fun linear_minimize test timeout result xs =
  let
    fun min _ [] p = p
      | min timeout (x :: xs) (seen, result) =
        case test timeout (xs @ seen) of
          result as {outcome = NONE, used_facts, run_time, ...}
          : prover_result =>
          min (new_timeout timeout run_time) (filter_used_facts used_facts xs)
              (filter_used_facts used_facts seen, result)
        | _ => min timeout xs (x :: seen, result)
  in min timeout xs ([], result) end

fun binary_minimize test timeout result xs =
  let
    fun min depth (result as {run_time, ...} : prover_result) sup
            (xs as _ :: _ :: _) =
        let
          val (l0, r0) = chop (length xs div 2) xs
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
          val depth = depth + 1
          val timeout = new_timeout timeout run_time
        in
          case test timeout (sup @ l0) of
            result as {outcome = NONE, used_facts, ...} =>
            min depth result (filter_used_facts used_facts sup)
                      (filter_used_facts used_facts l0)
          | _ =>
            case test timeout (sup @ r0) of
              result as {outcome = NONE, used_facts, ...} =>
              min depth result (filter_used_facts used_facts sup)
                        (filter_used_facts used_facts r0)
            | _ =>
              let
                val (sup_r0, (l, result)) = min depth result (sup @ r0) l0
                val (sup, r0) =
                  (sup, r0) |> pairself (filter_used_facts (map fst sup_r0))
                val (sup_l, (r, result)) = min depth result (sup @ l) r0
                val sup = sup |> filter_used_facts (map fst sup_l)
              in (sup, (l @ r, result)) end
        end
(*
        |> tap (fn _ => warning (replicate_string depth " " ^ "}"))
*)
      | min _ result sup xs = (sup, (xs, result))
  in
    case snd (min 0 result [] xs) of
      ([x], result as {run_time, ...}) =>
      (case test (new_timeout timeout run_time) [] of
         result as {outcome = NONE, ...} => ([], result)
       | _ => ([x], result))
    | p => p
  end

fun minimize_facts prover_name (params as {timeout, ...}) silent i n state
                   facts =
  let
    val ctxt = Proof.context_of state
    val prover =
      get_prover ctxt (if silent then Auto_Minimize else Minimize) prover_name
    val _ = print silent (fn () => "Sledgehammer minimizer: " ^
                                   quote prover_name ^ ".")
    fun test timeout = test_facts params silent prover timeout i n state
  in
    (case test timeout facts of
       result as {outcome = NONE, used_facts, run_time, ...} =>
       let
         val facts = filter_used_facts used_facts facts
         val min =
           if length facts >= Config.get ctxt binary_min_facts then
             binary_minimize
           else
             linear_minimize
         val (min_facts, {preplay, message, message_tail, ...}) =
           min test (new_timeout timeout run_time) result facts
         val _ = print silent (fn () => cat_lines
           ["Minimized to " ^ n_facts (map fst min_facts)] ^
            (case min_facts |> filter (fn ((_, (sc, _)), _) => sc = Chained)
                            |> length of
               0 => ""
             | n => "\n(including " ^ string_of_int n ^ " chained)") ^ ".")
       in (SOME min_facts, (preplay, message, message_tail)) end
     | {outcome = SOME TimedOut, preplay, ...} =>
       (NONE,
        (preplay,
         fn _ => "Timeout: You can increase the time limit using the \
                 \\"timeout\" option (e.g., \"timeout = " ^
                 string_of_int (10 + Time.toMilliseconds timeout div 1000) ^
                 "\").",
         ""))
     | {preplay, message, ...} =>
       (NONE, (preplay, prefix "Prover error: " o message, "")))
    handle ERROR msg =>
           (NONE, (K (Failed_to_Play plain_metis), fn _ => "Error: " ^ msg, ""))
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
