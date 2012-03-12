(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_run.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER_RUN =
sig
  type minimize_command = ATP_Proof_Reconstruct.minimize_command
  type relevance_override = Sledgehammer_Filter.relevance_override
  type mode = Sledgehammer_Provers.mode
  type params = Sledgehammer_Provers.params
  type prover = Sledgehammer_Provers.prover

  val someN : string
  val noneN : string
  val timeoutN : string
  val unknownN : string
  val auto_minimize_min_facts : int Config.T
  val auto_minimize_max_time : real Config.T
  val get_minimizing_prover : Proof.context -> mode -> string -> prover
  val run_sledgehammer :
    params -> mode -> int -> relevance_override
    -> ((string * string list) list -> string -> minimize_command)
    -> Proof.state -> bool * (string * Proof.state)
end;

structure Sledgehammer_Run : SLEDGEHAMMER_RUN =
struct

open ATP_Util
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_Provers
open Sledgehammer_Minimize

val someN = "some"
val noneN = "none"
val timeoutN = "timeout"
val unknownN = "unknown"

val ordered_outcome_codes = [someN, unknownN, timeoutN, noneN]

fun max_outcome_code codes =
  NONE
  |> fold (fn candidate =>
              fn accum as SOME _ => accum
               | NONE => if member (op =) codes candidate then SOME candidate
                         else NONE)
          ordered_outcome_codes
  |> the_default unknownN

fun prover_description ctxt ({verbose, blocking, ...} : params) name num_facts i
                       n goal =
  (name,
   (if verbose then
      " with " ^ string_of_int num_facts ^ " fact" ^ plural_s num_facts
    else
      "") ^
   " on " ^ (if n = 1 then "goal" else "subgoal " ^ string_of_int i) ^
   (if blocking then "."
    else "\n" ^ Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i))))

val auto_minimize_min_facts =
  Attrib.setup_config_int @{binding sledgehammer_auto_minimize_min_facts}
      (fn generic => Config.get_generic generic binary_min_facts)
val auto_minimize_max_time =
  Attrib.setup_config_real @{binding sledgehammer_auto_minimize_max_time}
                           (K 5.0)

fun adjust_reconstructor_params override_params
        ({debug, verbose, overlord, blocking, provers, type_enc, strict,
         lam_trans, uncurried_aliases, relevance_thresholds, max_relevant,
         max_mono_iters, max_new_mono_instances, isar_proof, isar_shrink_factor,
         slice, minimize, timeout, preplay_timeout, expect} : params) =
  let
    fun lookup_override name default_value =
      case AList.lookup (op =) override_params name of
        SOME [s] => SOME s
      | _ => default_value
    (* Only those options that reconstructors are interested in are considered
       here. *)
    val type_enc = lookup_override "type_enc" type_enc
    val lam_trans = lookup_override "lam_trans" lam_trans
  in
    {debug = debug, verbose = verbose, overlord = overlord, blocking = blocking,
     provers = provers, type_enc = type_enc, strict = strict,
     lam_trans = lam_trans, uncurried_aliases = uncurried_aliases,
     max_relevant = max_relevant, relevance_thresholds = relevance_thresholds,
     max_mono_iters = max_mono_iters,
     max_new_mono_instances = max_new_mono_instances, isar_proof = isar_proof,
     isar_shrink_factor = isar_shrink_factor, slice = slice,
     minimize = minimize, timeout = timeout, preplay_timeout = preplay_timeout,
     expect = expect}
  end

fun minimize ctxt mode name
             (params as {debug, verbose, isar_proof, minimize, ...})
             ({state, subgoal, subgoal_count, facts, ...} : prover_problem)
             (result as {outcome, used_facts, run_time, preplay, message,
                         message_tail} : prover_result) =
  if is_some outcome orelse null used_facts then
    result
  else
    let
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
              if isar_proof then
                ((prover_fast_enough (), (name, params)), preplay)
              else
                let val preplay = preplay () in
                  (case preplay of
                     Played (reconstr, timeout) =>
                     if can_min_fast_enough timeout then
                       (true, extract_reconstructor params reconstr
                              ||> (fn override_params =>
                                      adjust_reconstructor_params
                                          override_params params))
                     else
                       (prover_fast_enough (), (name, params))
                   | _ => (prover_fast_enough (), (name, params)),
                   K preplay)
                end
            end
        else
          ((false, (name, params)), preplay)
      val minimize = minimize |> the_default perhaps_minimize
      val (used_facts, (preplay, message, _)) =
        if minimize then
          minimize_facts minimize_name params (not verbose) subgoal
                         subgoal_count state
                         (filter_used_facts used_facts
                              (map (apsnd single o untranslated_fact) facts))
          |>> Option.map (map fst)
        else
          (SOME used_facts, (preplay, message, ""))
    in
      case used_facts of
        SOME used_facts =>
        (if debug andalso not (null used_facts) then
           facts ~~ (0 upto length facts - 1)
           |> map (fn (fact, j) => fact |> untranslated_fact |> apsnd (K j))
           |> filter_used_facts used_facts
           |> map (fn ((name, _), j) => name ^ "@" ^ string_of_int j)
           |> commas
           |> enclose ("Fact" ^ plural_s (length facts) ^ " in " ^ quote name ^
                       " proof (of " ^ string_of_int (length facts) ^ "): ") "."
           |> Output.urgent_message
         else
           ();
         {outcome = NONE, used_facts = used_facts, run_time = run_time,
          preplay = preplay, message = message, message_tail = message_tail})
      | NONE => result
    end

fun get_minimizing_prover ctxt mode name params minimize_command problem =
  get_prover ctxt mode name params minimize_command problem
  |> minimize ctxt mode name params problem

fun is_induction_fact (Untranslated_Fact ((_, (_, Induct)), _)) = true
  | is_induction_fact _ = false

fun launch_prover (params as {debug, verbose, blocking, max_relevant, slice,
                              timeout, expect, ...})
        mode minimize_command only
        {state, goal, subgoal, subgoal_count, facts, smt_filter} name =
  let
    val ctxt = Proof.context_of state
    val hard_timeout = Time.+ (timeout, timeout)
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, hard_timeout)
    val max_relevant =
      max_relevant
      |> the_default (default_max_relevant_for_prover ctxt slice name)
    val num_facts = length facts |> not only ? Integer.min max_relevant
    fun desc () =
      prover_description ctxt params name num_facts subgoal subgoal_count goal
    val problem =
      let
        val filter_induction = filter_out is_induction_fact
      in {state = state, goal = goal, subgoal = subgoal,
         subgoal_count = subgoal_count, facts =
          ((Sledgehammer_Provers.is_ho_atp ctxt name |> not) ? filter_induction)
            facts
          |> take num_facts,
         smt_filter = smt_filter}
      end
    fun really_go () =
      problem
      |> get_minimizing_prover ctxt mode name params minimize_command
      |> (fn {outcome, preplay, message, message_tail, ...} =>
             (if outcome = SOME ATP_Proof.TimedOut then timeoutN
              else if is_some outcome then noneN
              else someN, fn () => message (preplay ()) ^ message_tail))
    fun go () =
      let
        val (outcome_code, message) =
          if debug then
            really_go ()
          else
            (really_go ()
             handle ERROR msg => (unknownN, fn () => "Error: " ^ msg ^ "\n")
                  | exn =>
                    if Exn.is_interrupt exn then
                      reraise exn
                    else
                      (unknownN, fn () => "Internal error:\n" ^
                                          ML_Compiler.exn_message exn ^ "\n"))
        val _ =
          (* The "expect" argument is deliberately ignored if the prover is
             missing so that the "Metis_Examples" can be processed on any
             machine. *)
          if expect = "" orelse outcome_code = expect orelse
             not (is_prover_installed ctxt name) then
            ()
          else if blocking then
            error ("Unexpected outcome: " ^ quote outcome_code ^ ".")
          else
            warning ("Unexpected outcome: " ^ quote outcome_code ^ ".");
      in (outcome_code, message) end
  in
    if mode = Auto_Try then
      let val (outcome_code, message) = TimeLimit.timeLimit timeout go () in
        (outcome_code,
         state
         |> outcome_code = someN
            ? Proof.goal_message (fn () =>
                  [Pretty.str "",
                   Pretty.mark Isabelle_Markup.hilite (Pretty.str (message ()))]
                  |> Pretty.chunks))
      end
    else if blocking then
      let
        val (outcome_code, message) = TimeLimit.timeLimit hard_timeout go ()
      in
        (if outcome_code = someN orelse mode = Normal then
           quote name ^ ": " ^ message ()
         else
           "")
        |> Async_Manager.break_into_chunks
        |> List.app Output.urgent_message;
        (outcome_code, state)
      end
    else
      (Async_Manager.launch das_tool birth_time death_time (desc ())
                            ((fn (outcome_code, message) =>
                                 (verbose orelse outcome_code = someN,
                                  message ())) o go);
       (unknownN, state))
  end

fun class_of_smt_solver ctxt name =
  ctxt |> select_smt_solver name
       |> SMT_Config.solver_class_of |> SMT_Utils.string_of_class

fun dest_SMT_Weighted_Fact (SMT_Weighted_Fact p) = p
  | dest_SMT_Weighted_Fact _ = raise Fail "dest_SMT_Weighted_Fact"

val auto_try_max_relevant_divisor = 2 (* FUDGE *)

fun run_sledgehammer (params as {debug, verbose, blocking, provers,
                                 relevance_thresholds, max_relevant, slice,
                                 timeout, ...})
        mode i (relevance_override as {only, ...}) minimize_command state =
  if null provers then
    error "No prover is set."
  else case subgoal_count state of
    0 => (Output.urgent_message "No subgoal!"; (false, (noneN, state)))
  | n =>
    let
      val _ = Proof.assert_backward state
      val print = if mode = Normal then Output.urgent_message else K ()
      val state =
        state |> Proof.map_context (Config.put SMT_Config.verbose debug)
      val ctxt = Proof.context_of state
      val {facts = chained_ths, goal, ...} = Proof.goal state
      val chained_ths = chained_ths |> normalize_chained_theorems
      val (_, hyp_ts, concl_t) = strip_subgoal ctxt goal i
      val ho_atp = exists (Sledgehammer_Provers.is_ho_atp ctxt) provers
      val facts =
        nearly_all_facts ctxt ho_atp relevance_override chained_ths hyp_ts
                         concl_t
      val _ = () |> not blocking ? kill_provers
      val _ = case find_first (not o is_prover_supported ctxt) provers of
                SOME name => error ("No such prover: " ^ name ^ ".")
              | NONE => ()
      val _ = print "Sledgehammering..."
      val (smts, (ueq_atps, full_atps)) =
        provers |> List.partition (is_smt_prover ctxt)
                ||> List.partition (is_unit_equational_atp ctxt)
      fun launch_provers state get_facts translate maybe_smt_filter provers =
        let
          val facts = get_facts ()
          val num_facts = length facts
          val facts = facts ~~ (0 upto num_facts - 1)
                      |> map (translate num_facts)
          val problem =
            {state = state, goal = goal, subgoal = i, subgoal_count = n,
             facts = facts,
             smt_filter = maybe_smt_filter
                  (fn () => map_filter (try dest_SMT_Weighted_Fact) facts) i}
          val launch = launch_prover params mode minimize_command only
        in
          if mode = Auto_Try orelse mode = Try then
            (unknownN, state)
            |> fold (fn prover => fn accum as (outcome_code, _) =>
                        if outcome_code = someN then accum
                        else launch problem prover)
                    provers
          else
            provers
            |> (if blocking then Par_List.map else map)
                   (launch problem #> fst)
            |> max_outcome_code |> rpair state
        end
      fun get_facts label is_appropriate_prop relevance_fudge provers =
        let
          val max_max_relevant =
            case max_relevant of
              SOME n => n
            | NONE =>
              0 |> fold (Integer.max
                         o default_max_relevant_for_prover ctxt slice)
                        provers
                |> mode = Auto_Try
                   ? (fn n => n div auto_try_max_relevant_divisor)
          val is_built_in_const =
            is_built_in_const_for_prover ctxt (hd provers)
        in
          facts
          |> (case is_appropriate_prop of
                SOME is_app => filter (is_app o prop_of o snd)
              | NONE => I)
          |> relevant_facts ctxt relevance_thresholds max_max_relevant
                            is_built_in_const relevance_fudge relevance_override
                            chained_ths hyp_ts concl_t
          |> tap (fn facts =>
                     if debug then
                       label ^ plural_s (length provers) ^ ": " ^
                       (if null facts then
                          "Found no relevant facts."
                        else
                          "Including (up to) " ^ string_of_int (length facts) ^
                          " relevant fact" ^ plural_s (length facts) ^ ":\n" ^
                          (facts |> map (fst o fst) |> space_implode " ") ^ ".")
                       |> print
                     else
                       ())
        end
      fun launch_atps label is_appropriate_prop atps accum =
        if null atps then
          accum
        else if is_some is_appropriate_prop andalso
                not (the is_appropriate_prop concl_t) then
          (if verbose orelse length atps = length provers then
             "Goal outside the scope of " ^
             space_implode " " (serial_commas "and" (map quote atps)) ^ "."
             |> Output.urgent_message
           else
             ();
           accum)
        else
          launch_provers state
              (get_facts label is_appropriate_prop atp_relevance_fudge o K atps)
              (K (Untranslated_Fact o fst)) (K (K NONE)) atps
      fun launch_smts accum =
        if null smts then
          accum
        else
          let
            val facts = get_facts "SMT solver" NONE smt_relevance_fudge smts
            val weight = SMT_Weighted_Fact oo weight_smt_fact ctxt
            fun smt_filter facts =
              (if debug then curry (op o) SOME
               else TimeLimit.timeLimit timeout o try)
                  (SMT_Solver.smt_filter_preprocess state (facts ()))
          in
            smts |> map (`(class_of_smt_solver ctxt))
                 |> AList.group (op =)
                 |> map (snd #> launch_provers state (K facts) weight smt_filter
                             #> fst)
                 |> max_outcome_code |> rpair state
          end
      val launch_full_atps = launch_atps "ATP" NONE full_atps
      val launch_ueq_atps =
        launch_atps "Unit equational provers" (SOME is_unit_equality) ueq_atps
      fun launch_atps_and_smt_solvers () =
        [launch_full_atps, launch_smts, launch_ueq_atps]
        |> Par_List.map (fn f => ignore (f (unknownN, state)))
        handle ERROR msg => (print ("Error: " ^ msg); error msg)
      fun maybe f (accum as (outcome_code, _)) =
        accum |> (mode = Normal orelse outcome_code <> someN) ? f
    in
      (unknownN, state)
      |> (if blocking then
            launch_full_atps
            #> mode <> Auto_Try ? (maybe launch_ueq_atps #> maybe launch_smts)
          else
            (fn p => Future.fork (tap launch_atps_and_smt_solvers) |> K p))
      handle TimeLimit.TimeOut =>
             (print "Sledgehammer ran out of time."; (unknownN, state))
    end
    |> `(fn (outcome_code, _) => outcome_code = someN)

end;
