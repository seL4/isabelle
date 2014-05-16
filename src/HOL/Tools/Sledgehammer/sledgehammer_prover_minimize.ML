(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_minimize.ML
    Author:     Philipp Meyer, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Minimization of fact list for Metis using external provers.
*)

signature SLEDGEHAMMER_PROVER_MINIMIZE =
sig
  type stature = ATP_Problem_Generate.stature
  type proof_method = Sledgehammer_Proof_Methods.proof_method
  type play_outcome = Sledgehammer_Proof_Methods.play_outcome
  type mode = Sledgehammer_Prover.mode
  type params = Sledgehammer_Prover.params
  type prover = Sledgehammer_Prover.prover

  val is_prover_supported : Proof.context -> string -> bool
  val is_prover_installed : Proof.context -> string -> bool
  val default_max_facts_of_prover : Proof.context -> string -> int
  val get_prover : Proof.context -> mode -> string -> prover

  val binary_min_facts : int Config.T
  val auto_minimize_min_facts : int Config.T
  val auto_minimize_max_time : real Config.T
  val minimize_facts : (thm list -> unit) -> string -> params -> bool -> int -> int ->
    Proof.state -> thm -> (proof_method * play_outcome) Lazy.lazy option ->
    ((string * stature) * thm list) list ->
    ((string * stature) * thm list) list option
      * ((proof_method * play_outcome) Lazy.lazy * ((proof_method * play_outcome) -> string)
         * string)
  val get_minimizing_prover : Proof.context -> mode -> (thm list -> unit) -> string -> prover

  val run_minimize : params -> (thm list -> unit) -> int -> (Facts.ref * Attrib.src list) list ->
    Proof.state -> unit
end;

structure Sledgehammer_Prover_Minimize : SLEDGEHAMMER_PROVER_MINIMIZE =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open ATP_Systems
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Prover_SMT
open Sledgehammer_Prover_SMT2

fun run_proof_method mode name (params as {debug, verbose, timeout, type_enc, lam_trans, ...})
    minimize_command
    ({state, subgoal, subgoal_count, factss = (_, facts) :: _, ...} : prover_problem) =
  let
    val meth =
      if name = metisN then Metis_Method (type_enc, lam_trans)
      else if name = smtN then SMT2_Method
      else raise Fail ("unknown proof_method: " ^ quote name)
    val used_facts = facts |> map fst
  in
    (case play_one_line_proof (if mode = Minimize then Normal else mode) debug verbose timeout
        facts state subgoal meth [meth] of
      play as (_, Played time) =>
      {outcome = NONE, used_facts = used_facts, used_from = facts, run_time = time,
       preplay = Lazy.value play,
       message =
         fn play =>
            let
              val ctxt = Proof.context_of state
              val (_, override_params) = extract_proof_method params meth
              val one_line_params =
                (play, proof_banner mode name, used_facts, minimize_command override_params name,
                 subgoal, subgoal_count)
              val num_chained = length (#facts (Proof.goal state))
            in
              one_line_proof_text ctxt num_chained one_line_params
            end,
       message_tail = ""}
    | play =>
      let
        val failure = (case play of (_, Play_Failed) => GaveUp | _ => TimedOut)
      in
        {outcome = SOME failure, used_facts = [], used_from = [],
         run_time = Time.zeroTime, preplay = Lazy.value play,
         message = fn _ => string_of_atp_failure failure, message_tail = ""}
      end)
  end

fun is_prover_supported ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    is_proof_method orf is_atp thy orf is_smt_prover ctxt orf is_smt2_prover ctxt
  end

fun is_prover_installed ctxt =
  is_proof_method orf is_smt_prover ctxt orf is_smt2_prover ctxt orf
  is_atp_installed (Proof_Context.theory_of ctxt)

val proof_method_default_max_facts = 20

fun default_max_facts_of_prover ctxt name =
  let val thy = Proof_Context.theory_of ctxt in
    if is_proof_method name then
      proof_method_default_max_facts
    else if is_atp thy name then
      fold (Integer.max o fst o #1 o fst o snd) (#best_slices (get_atp thy name ()) ctxt) 0
    else if is_smt_prover ctxt name then
      SMT_Solver.default_max_relevant ctxt name
    else if is_smt2_prover ctxt name then
      SMT2_Solver.default_max_relevant ctxt name
    else
      error ("No such prover: " ^ name ^ ".")
  end

fun get_prover ctxt mode name =
  let val thy = Proof_Context.theory_of ctxt in
    if is_proof_method name then run_proof_method mode name
    else if is_atp thy name then run_atp mode name
    else if is_smt_prover ctxt name then run_smt_solver mode name
    else if is_smt2_prover ctxt name then run_smt2_solver mode name
    else error ("No such prover: " ^ name ^ ".")
  end

(* wrapper for calling external prover *)

fun n_facts names =
  let val n = length names in
    string_of_int n ^ " fact" ^ plural_s n ^
    (if n > 0 then
       ": " ^ (names |> map fst |> sort string_ord |> space_implode " ")
     else
       "")
  end

fun print silent f = if silent then () else Output.urgent_message (f ())

fun test_facts ({debug, verbose, overlord, spy, provers, max_mono_iters, max_new_mono_instances,
      type_enc, strict, lam_trans, uncurried_aliases, isar_proofs, compress_isar, try0_isar,
      smt_proofs, preplay_timeout, ...} : params)
    silent (prover : prover) timeout i n state goal facts =
  let
    val _ =
      print silent (fn () =>
        "Testing " ^ n_facts (map fst facts) ^
        (if verbose then " (timeout: " ^ string_of_time timeout ^ ")" else "") ^ "...")
    val facts = facts |> maps (fn (n, ths) => map (pair n) ths)
    val params =
      {debug = debug, verbose = verbose, overlord = overlord, spy = spy, blocking = true,
       provers = provers, type_enc = type_enc, strict = strict, lam_trans = lam_trans,
       uncurried_aliases = uncurried_aliases, learn = false, fact_filter = NONE,
       max_facts = SOME (length facts), fact_thresholds = (1.01, 1.01),
       max_mono_iters = max_mono_iters, max_new_mono_instances = max_new_mono_instances,
       isar_proofs = isar_proofs, compress_isar = compress_isar, try0_isar = try0_isar,
       smt_proofs = smt_proofs, slice = false, minimize = SOME false, timeout = timeout,
       preplay_timeout = preplay_timeout, expect = ""}
    val problem =
      {comment = "", state = state, goal = goal, subgoal = i, subgoal_count = n,
       factss = [("", facts)]}
    val result as {outcome, used_facts, run_time, ...} =
      prover params (K (K (K ""))) problem
  in
    print silent (fn () =>
      (case outcome of
        SOME failure => string_of_atp_failure failure
      | NONE =>
        "Found proof" ^
         (if length used_facts = length facts then "" else " with " ^ n_facts used_facts) ^
         " (" ^ string_of_time run_time ^ ")."));
    result
  end

(* minimalization of facts *)

(* Give the external prover some slack. The ATP gets further slack because the
   Sledgehammer preprocessing time is included in the estimate below but isn't
   part of the timeout. *)
val slack_msecs = 200

fun new_timeout timeout run_time =
  Int.min (Time.toMilliseconds timeout, Time.toMilliseconds run_time + slack_msecs)
  |> Time.fromMilliseconds

(* The linear algorithm usually outperforms the binary algorithm when over 60%
   of the facts are actually needed. The binary algorithm is much more
   appropriate for provers that cannot return the list of used facts and hence
   returns all facts as used. Since we cannot know in advance how many facts are
   actually needed, we heuristically set the threshold to 10 facts. *)
val binary_min_facts =
  Attrib.setup_config_int @{binding sledgehammer_minimize_binary_min_facts} (K 20)
val auto_minimize_min_facts =
  Attrib.setup_config_int @{binding sledgehammer_auto_minimize_min_facts}
      (fn generic => Config.get_generic generic binary_min_facts)
val auto_minimize_max_time =
  Attrib.setup_config_real @{binding sledgehammer_auto_minimize_max_time} (K 5.0)

fun linear_minimize test timeout result xs =
  let
    fun min _ [] p = p
      | min timeout (x :: xs) (seen, result) =
        (case test timeout (xs @ seen) of
          result as {outcome = NONE, used_facts, run_time, ...} : prover_result =>
          min (new_timeout timeout run_time) (filter_used_facts true used_facts xs)
            (filter_used_facts false used_facts seen, result)
        | _ => min timeout xs (x :: seen, result))
  in
    min timeout xs ([], result)
  end

fun binary_minimize test timeout result xs =
  let
    fun min depth (result as {run_time, ...} : prover_result) sup (xs as _ :: _ :: _) =
        let
          val (l0, r0) = chop (length xs div 2) xs
(*
          val _ = warning (replicate_string depth " " ^ "{ " ^ "sup: " ^ n_facts (map fst sup))
          val _ = warning (replicate_string depth " " ^ " " ^ "xs: " ^ n_facts (map fst xs))
          val _ = warning (replicate_string depth " " ^ " " ^ "l0: " ^ n_facts (map fst l0))
          val _ = warning (replicate_string depth " " ^ " " ^ "r0: " ^ n_facts (map fst r0))
*)
          val depth = depth + 1
          val timeout = new_timeout timeout run_time
        in
          (case test timeout (sup @ l0) of
            result as {outcome = NONE, used_facts, ...} =>
            min depth result (filter_used_facts true used_facts sup)
                      (filter_used_facts true used_facts l0)
          | _ =>
            (case test timeout (sup @ r0) of
              result as {outcome = NONE, used_facts, ...} =>
              min depth result (filter_used_facts true used_facts sup)
                        (filter_used_facts true used_facts r0)
            | _ =>
              let
                val (sup_r0, (l, result)) = min depth result (sup @ r0) l0
                val (sup, r0) = (sup, r0) |> pairself (filter_used_facts true (map fst sup_r0))
                val (sup_l, (r, result)) = min depth result (sup @ l) r0
                val sup = sup |> filter_used_facts true (map fst sup_l)
              in (sup, (l @ r, result)) end))
        end
(*
        |> tap (fn _ => warning (replicate_string depth " " ^ "}"))
*)
      | min _ result sup xs = (sup, (xs, result))
  in
    (case snd (min 0 result [] xs) of
      ([x], result as {run_time, ...}) =>
      (case test (new_timeout timeout run_time) [] of
        result as {outcome = NONE, ...} => ([], result)
      | _ => ([x], result))
    | p => p)
  end

fun minimize_facts do_learn prover_name (params as {learn, timeout, ...}) silent i n state goal
    preplay0 facts =
  let
    val ctxt = Proof.context_of state
    val prover = get_prover ctxt (if silent then Auto_Minimize else Minimize) prover_name
    fun test timeout = test_facts params silent prover timeout i n state goal
    val (chained, non_chained) = List.partition is_fact_chained facts
    (* Push chained facts to the back, so that they are less likely to be
       kicked out by the linear minimization algorithm. *)
    val facts = non_chained @ chained
  in
    (print silent (fn () => "Sledgehammer minimizer: " ^ quote prover_name ^ ".");
     (case test timeout facts of
       result as {outcome = NONE, used_facts, run_time, ...} =>
       let
         val facts = filter_used_facts true used_facts facts
         val min =
           if length facts >= Config.get ctxt binary_min_facts then binary_minimize
           else linear_minimize
         val (min_facts, {preplay, message, message_tail, ...}) =
           min test (new_timeout timeout run_time) result facts
       in
         print silent (fn () => cat_lines
             ["Minimized to " ^ n_facts (map fst min_facts)] ^
              (case min_facts |> filter is_fact_chained |> length of
                 0 => ""
               | n => "\n(including " ^ string_of_int n ^ " chained)") ^ ".");
         (if learn then do_learn (maps snd min_facts) else ());
         (SOME min_facts,
          (if is_some preplay0 andalso length min_facts = length facts then the preplay0
           else preplay,
           message, message_tail))
       end
     | {outcome = SOME TimedOut, preplay, ...} =>
       (NONE, (preplay, fn _ =>
          "Timeout: You can increase the time limit using the \"timeout\" option (e.g., \
          \timeout = " ^ string_of_int (10 + Time.toMilliseconds timeout div 1000) ^ "\").", ""))
     | {preplay, message, ...} => (NONE, (preplay, prefix "Prover error: " o message, ""))))
    handle ERROR msg =>
      (NONE, (Lazy.value (Metis_Method (NONE, NONE), Play_Failed), fn _ => "Error: " ^ msg, ""))
  end

fun adjust_proof_method_params override_params
    ({debug, verbose, overlord, spy, blocking, provers, type_enc, strict, lam_trans,
      uncurried_aliases, learn, fact_filter, max_facts, fact_thresholds, max_mono_iters,
      max_new_mono_instances, isar_proofs, compress_isar, try0_isar, smt_proofs, slice, minimize,
      timeout, preplay_timeout, expect} : params) =
  let
    fun lookup_override name default_value =
      (case AList.lookup (op =) override_params name of
        SOME [s] => SOME s
      | _ => default_value)
    (* Only those options that proof_methods are interested in are considered here. *)
    val type_enc = lookup_override "type_enc" type_enc
    val lam_trans = lookup_override "lam_trans" lam_trans
  in
    {debug = debug, verbose = verbose, overlord = overlord, spy = spy, blocking = blocking,
     provers = provers, type_enc = type_enc, strict = strict, lam_trans = lam_trans,
     uncurried_aliases = uncurried_aliases, learn = learn, fact_filter = fact_filter,
     max_facts = max_facts, fact_thresholds = fact_thresholds, max_mono_iters = max_mono_iters,
     max_new_mono_instances = max_new_mono_instances, isar_proofs = isar_proofs,
     compress_isar = compress_isar, try0_isar = try0_isar, smt_proofs = smt_proofs, slice = slice,
     minimize = minimize, timeout = timeout, preplay_timeout = preplay_timeout, expect = expect}
  end

fun maybe_minimize ctxt mode do_learn name (params as {verbose, isar_proofs, minimize, ...})
    ({state, goal, subgoal, subgoal_count, ...} : prover_problem)
    (result as {outcome, used_facts, used_from, run_time, preplay, message, message_tail} :
     prover_result) =
  if is_some outcome orelse null used_facts then
    result
  else
    let
      val thy = Proof_Context.theory_of ctxt
      val num_facts = length used_facts

      val ((perhaps_minimize, (minimize_name, params)), preplay) =
        if mode = Normal then
          if num_facts >= Config.get ctxt auto_minimize_min_facts then
            ((true, (name, params)), preplay)
          else
            let
              fun can_min_fast_enough time =
                0.001
                * Real.fromInt ((num_facts + 1) * Time.toMilliseconds time)
                <= Config.get ctxt auto_minimize_max_time
              fun prover_fast_enough () = can_min_fast_enough run_time
            in
              (case Lazy.force preplay of
                 (meth as Metis_Method _, Played timeout) =>
                 if isar_proofs = SOME true then
                   (* Cheat: Assume the selected ATP is as fast as "metis" for the goal it proved
                      itself. *)
                   (can_min_fast_enough timeout, (isar_supported_prover_of thy name, params))
                 else if can_min_fast_enough timeout then
                   (true, extract_proof_method params meth
                          ||> (fn override_params =>
                                  adjust_proof_method_params override_params params))
                 else
                   (prover_fast_enough (), (name, params))
               | (SMT2_Method, Played timeout) =>
                 (* Cheat: Assume the original prover is as fast as "smt" for the goal it proved
                    itself. *)
                 (can_min_fast_enough timeout, (name, params))
               | _ => (prover_fast_enough (), (name, params)),
               preplay)
            end
        else
          ((false, (name, params)), preplay)
      val minimize = minimize |> the_default perhaps_minimize
      val (used_facts, (preplay, message, _)) =
        if minimize then
          minimize_facts do_learn minimize_name params
            (not verbose orelse (mode <> Normal andalso mode <> MaSh)) subgoal subgoal_count state
            goal (SOME preplay) (filter_used_facts true used_facts (map (apsnd single) used_from))
          |>> Option.map (map fst)
        else
          (SOME used_facts, (preplay, message, ""))
    in
      (case used_facts of
        SOME used_facts =>
        {outcome = NONE, used_facts = used_facts, used_from = used_from, run_time = run_time,
         preplay = preplay, message = message, message_tail = message_tail}
      | NONE => result)
    end

fun get_minimizing_prover ctxt mode do_learn name params minimize_command
                          problem =
  get_prover ctxt mode name params minimize_command problem
  |> maybe_minimize ctxt mode do_learn name params problem

fun run_minimize (params as {provers, ...}) do_learn i refs state =
  let
    val ctxt = Proof.context_of state
    val {goal, facts = chained_ths, ...} = Proof.goal state
    val reserved = reserved_isar_keyword_table ()
    val css = clasimpset_rule_table_of ctxt
    val facts = refs |> maps (map (apsnd single) o fact_of_ref ctxt reserved chained_ths css)
  in
    (case subgoal_count state of
      0 => Output.urgent_message "No subgoal!"
    | n => (case provers of
             [] => error "No prover is set."
           | prover :: _ =>
             (kill_provers ();
              minimize_facts do_learn prover params false i n state goal NONE facts
              |> (fn (_, (preplay, message, message_tail)) =>
                     message (Lazy.force preplay) ^ message_tail
                     |> Output.urgent_message))))
  end

end;
