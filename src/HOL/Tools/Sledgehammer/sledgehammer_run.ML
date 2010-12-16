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
               {state, goal, subgoal, subgoal_count, facts} name =
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
       subgoal_count = subgoal_count, facts = take num_facts facts}
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
      val ctxt = Proof.context_of state
      val {facts = chained_ths, goal, ...} = Proof.goal state
      val (_, hyp_ts, concl_t) = strip_subgoal goal i
      val no_dangerous_types = types_dangerous_types type_sys
      val _ = () |> not blocking ? kill_provers
      val _ = case find_first (not o is_prover_available ctxt) provers of
                SOME name => error ("No such prover: " ^ name ^ ".")
              | NONE => ()
      val _ = if auto then () else Output.urgent_message "Sledgehammering..."
      val (smts, atps) = provers |> List.partition (is_smt_prover ctxt)
      fun run_provers label no_dangerous_types relevance_fudge maybe_translate
                      provers (res as (success, state)) =
        if success orelse null provers then
          res
        else
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
            val facts =
              relevant_facts ctxt no_dangerous_types relevance_thresholds
                             max_max_relevant is_built_in_const relevance_fudge
                             relevance_override chained_ths hyp_ts concl_t
              |> map maybe_translate
            val problem =
              {state = state, goal = goal, subgoal = i, subgoal_count = n,
               facts = facts}
            val run_prover = run_prover params auto minimize_command only
          in
            if debug then
              Output.urgent_message (label ^ plural_s (length provers) ^ ": " ^
                  (if null facts then
                     "Found no relevant facts."
                   else
                     "Including (up to) " ^ string_of_int (length facts) ^
                     " relevant fact" ^ plural_s (length facts) ^ ":\n" ^
                     (facts |> map (fst o fst o untranslated_fact)
                            |> space_implode " ") ^ "."))
            else
              ();
            if auto then
              fold (fn prover => fn (true, state) => (true, state)
                                  | (false, _) => run_prover problem prover)
                   provers (false, state)
            else
              provers
              |> (if blocking andalso length provers > 1 then Par_List.map
                  else map)
                     (run_prover problem)
              |> exists fst |> rpair state
          end
      val run_atps =
        run_provers "ATP" no_dangerous_types atp_relevance_fudge
                    (ATP_Translated_Fact o translate_atp_fact ctxt) atps
      val run_smts =
        run_provers "SMT solver" true smt_relevance_fudge Untranslated_Fact smts
      fun run_atps_and_smt_solvers () =
        [run_atps, run_smts] |> Par_List.map (fn f => f (false, state) |> K ())
        handle ERROR msg => (Output.urgent_message ("Error: " ^ msg); error msg)
    in
      (false, state)
      |> (if blocking then run_atps #> not auto ? run_smts
          else (fn p => Future.fork (tap run_atps_and_smt_solvers) |> K p))
    end

end;
