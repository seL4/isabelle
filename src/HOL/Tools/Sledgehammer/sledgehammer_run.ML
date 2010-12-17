(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_run.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER_RUN =
sig
  type relevance_override = Sledgehammer_Filter.relevance_override
  type minimize_command = Sledgehammer_ATP_Reconstruct.minimize_command
  type params = Sledgehammer_Provers.params

  (* for experimentation purposes -- do not use in production code *)
  val smt_weights : bool Unsynchronized.ref
  val smt_weight_min_facts : int Unsynchronized.ref
  val smt_min_weight : int Unsynchronized.ref
  val smt_max_weight : int Unsynchronized.ref
  val smt_max_weight_index : int Unsynchronized.ref
  val smt_weight_curve : (int -> int) Unsynchronized.ref

  val run_sledgehammer :
    params -> bool -> int -> relevance_override -> (string -> minimize_command)
    -> Proof.state -> bool * Proof.state
end;

structure Sledgehammer_Run : SLEDGEHAMMER_RUN =
struct

open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_ATP_Translate
open Sledgehammer_Provers
open Sledgehammer_Minimize

fun prover_description ctxt ({verbose, blocking, ...} : params) name num_facts i
                       n goal =
  quote name ^
  (if verbose then
     " with " ^ string_of_int num_facts ^ " fact" ^ plural_s num_facts
   else
     "") ^
  " on " ^ (if n = 1 then "goal" else "subgoal " ^ string_of_int i) ^ ":" ^
  (if blocking then
     ""
   else
     "\n" ^ Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i)))

val implicit_minimization_threshold = 50

fun run_prover (params as {debug, blocking, max_relevant, timeout, expect, ...})
               auto minimize_command only
               {state, goal, subgoal, subgoal_count, facts, smt_head} name =
  let
    val ctxt = Proof.context_of state
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val max_relevant =
      the_default (default_max_relevant_for_prover ctxt name) max_relevant
    val num_facts = length facts |> not only ? Integer.min max_relevant
    val desc =
      prover_description ctxt params name num_facts subgoal subgoal_count goal
    val prover = get_prover ctxt auto name
    val problem =
      {state = state, goal = goal, subgoal = subgoal,
       subgoal_count = subgoal_count, facts = take num_facts facts,
       smt_head = smt_head}
    fun go () =
      let
        fun really_go () =
          prover params (minimize_command name) problem
          |> (fn {outcome, used_facts, message, ...} =>
                 if is_some outcome then
                   ("none", message)
                 else
                   ("some",
                    if length used_facts >= implicit_minimization_threshold then
                      minimize_facts params true subgoal subgoal_count state
                          (filter_used_facts used_facts
                               (map (apsnd single o untranslated_fact) facts))
                      |> snd
                    else
                      message))
        val (outcome_code, message) =
          if debug then
            really_go ()
          else
            (really_go ()
             handle ERROR message => ("unknown", "Error: " ^ message ^ "\n")
                  | exn =>
                    if Exn.is_interrupt exn then
                      reraise exn
                    else
                      ("unknown", "Internal error:\n" ^
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
      in (outcome_code = "some", message) end
  in
    if auto then
      let val (success, message) = TimeLimit.timeLimit timeout go () in
        (success, state |> success ? Proof.goal_message (fn () =>
             Pretty.chunks [Pretty.str "",
                            Pretty.mark Markup.hilite (Pretty.str message)]))
      end
    else if blocking then
      let val (success, message) = TimeLimit.timeLimit timeout go () in
        List.app Output.urgent_message
                 (Async_Manager.break_into_chunks [desc ^ "\n" ^ message]);
        (success, state)
      end
    else
      (Async_Manager.launch das_Tool birth_time death_time desc (snd o go);
       (false, state))
  end

val smt_weights = Unsynchronized.ref true
val smt_weight_min_facts = Unsynchronized.ref 20

(* FUDGE *)
val smt_min_weight = Unsynchronized.ref 0
val smt_max_weight = Unsynchronized.ref 10
val smt_max_weight_index = Unsynchronized.ref 200
val smt_weight_curve = Unsynchronized.ref (fn x : int => x * x)

fun smt_fact_weight j num_facts =
  if !smt_weights andalso num_facts >= !smt_weight_min_facts then
    SOME (!smt_max_weight
          - (!smt_max_weight - !smt_min_weight + 1)
            * !smt_weight_curve (Int.max (0, !smt_max_weight_index - j - 1))
            div !smt_weight_curve (!smt_max_weight_index))
  else
    NONE

fun weight_smt_fact thy num_facts (fact, j) =
  fact |> apsnd (pair (smt_fact_weight j num_facts) o Thm.transfer thy)

fun class_of_smt_solver ctxt name =
  ctxt |> select_smt_solver name
       |> SMT_Config.solver_class_of |> SMT_Utils.string_of_class

(* Makes backtraces more transparent and might be more efficient as well. *)
fun smart_par_list_map _ [] = []
  | smart_par_list_map f [x] = [f x]
  | smart_par_list_map f xs = Par_List.map f xs

(* FUDGE *)
val auto_max_relevant_divisor = 2

fun run_sledgehammer (params as {debug, blocking, provers, type_sys,
                                 relevance_thresholds, max_relevant, ...})
                     auto i (relevance_override as {only, ...}) minimize_command
                     state =
  if null provers then
    error "No prover is set."
  else case subgoal_count state of
    0 => (Output.urgent_message "No subgoal!"; (false, state))
  | n =>
    let
      val _ = Proof.assert_backward state
      val state =
        state |> Proof.map_context (Config.put SMT_Config.verbose debug)
      val ctxt = Proof.context_of state
      val thy = ProofContext.theory_of ctxt
      val {facts = chained_ths, goal, ...} = Proof.goal state
      val (_, hyp_ts, concl_t) = strip_subgoal goal i
      val no_dangerous_types = types_dangerous_types type_sys
      val _ = () |> not blocking ? kill_provers
      val _ = case find_first (not o is_prover_available ctxt) provers of
                SOME name => error ("No such prover: " ^ name ^ ".")
              | NONE => ()
      val _ = if auto then () else Output.urgent_message "Sledgehammering..."
      val (smts, atps) = provers |> List.partition (is_smt_prover ctxt)
      fun run_provers get_facts translate maybe_smt_head provers
                      (res as (success, state)) =
        if success orelse null provers then
          res
        else
          let
            val facts = get_facts ()
            val num_facts = length facts
            val facts = facts ~~ (0 upto num_facts - 1)
                        |> map (translate num_facts)
            val problem =
              {state = state, goal = goal, subgoal = i, subgoal_count = n,
               facts = facts,
               smt_head = maybe_smt_head (map smt_weighted_fact facts) i}
            val run_prover = run_prover params auto minimize_command only
          in
            if auto then
              fold (fn prover => fn (true, state) => (true, state)
                                  | (false, _) => run_prover problem prover)
                   provers (false, state)
            else
              provers
              |> (if blocking then smart_par_list_map else map)
                     (run_prover problem)
              |> exists fst |> rpair state
          end
      fun get_facts label no_dangerous_types relevance_fudge provers =
        let
          val max_max_relevant =
            case max_relevant of
              SOME n => n
            | NONE =>
              0 |> fold (Integer.max o default_max_relevant_for_prover ctxt)
                        provers
                |> auto ? (fn n => n div auto_max_relevant_divisor)
          val is_built_in_const =
            is_built_in_const_for_prover ctxt (hd provers)
        in
          relevant_facts ctxt no_dangerous_types relevance_thresholds
                         max_max_relevant is_built_in_const relevance_fudge
                         relevance_override chained_ths hyp_ts concl_t
          |> tap (fn facts =>
                     if debug then
                       label ^ plural_s (length provers) ^ ": " ^
                       (if null facts then
                          "Found no relevant facts."
                        else
                          "Including (up to) " ^ string_of_int (length facts) ^
                          " relevant fact" ^ plural_s (length facts) ^ ":\n" ^
                          (facts |> map (fst o fst) |> space_implode " ") ^ ".")
                       |> Output.urgent_message
                     else
                       ())
        end
      val run_atps =
        run_provers
            (get_facts "ATP" no_dangerous_types atp_relevance_fudge o K atps)
            (ATP_Translated_Fact oo K (translate_atp_fact ctxt o fst))
            (K (K NONE)) atps
      fun run_smts (accum as (success, _)) =
        if success orelse null smts then
          accum
        else
          let
            val facts = get_facts "SMT solver" true smt_relevance_fudge smts
            val translate = SMT_Weighted_Fact oo weight_smt_fact thy
            val maybe_smt_head = try o SMT_Solver.smt_filter_head state
          in
            smts |> map (`(class_of_smt_solver ctxt))
                 |> AList.group (op =)
                 |> map (fn (_, smts) => run_provers (K facts) translate
                                                     maybe_smt_head smts accum)
                 |> exists fst |> rpair state
          end
      fun run_atps_and_smt_solvers () =
        [run_atps, run_smts]
        |> smart_par_list_map (fn f => f (false, state) |> K ())
        handle ERROR msg => (Output.urgent_message ("Error: " ^ msg); error msg)
    in
      (false, state)
      |> (if blocking then run_atps #> not auto ? run_smts
          else (fn p => Future.fork (tap run_atps_and_smt_solvers) |> K p))
    end

end;
