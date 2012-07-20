(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_run.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER_RUN =
sig
  type minimize_command = ATP_Proof_Reconstruct.minimize_command
  type fact_override = Sledgehammer_Fact.fact_override
  type mode = Sledgehammer_Provers.mode
  type params = Sledgehammer_Provers.params

  val someN : string
  val noneN : string
  val timeoutN : string
  val unknownN : string
  val run_sledgehammer :
    params -> mode -> int -> fact_override
    -> ((string * string list) list -> string -> minimize_command)
    -> Proof.state -> bool * (string * Proof.state)
end;

structure Sledgehammer_Run : SLEDGEHAMMER_RUN =
struct

open ATP_Util
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Provers
open Sledgehammer_Minimize
open Sledgehammer_MaSh

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
  (quote name,
   (if verbose then
      " with " ^ string_of_int num_facts ^ " fact" ^ plural_s num_facts
    else
      "") ^
   " on " ^ (if n = 1 then "goal" else "subgoal " ^ string_of_int i) ^
   (if blocking then "."
    else "\n" ^ Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i))))

fun launch_prover (params as {debug, verbose, blocking, max_facts, slice,
                              timeout, expect, ...})
        mode minimize_command only {state, goal, subgoal, subgoal_count, facts}
        name =
  let
    val ctxt = Proof.context_of state
    val hard_timeout = Time.+ (timeout, timeout)
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, hard_timeout)
    val max_facts =
      max_facts |> the_default (default_max_facts_for_prover ctxt slice name)
    val num_facts = length facts |> not only ? Integer.min max_facts
    fun desc () =
      prover_description ctxt params name num_facts subgoal subgoal_count goal
    val problem =
      {state = state, goal = goal, subgoal = subgoal,
       subgoal_count = subgoal_count,
       facts = facts
               |> not (Sledgehammer_Provers.is_ho_atp ctxt name)
                  ? filter_out (curry (op =) Induction o snd o snd o fst
                                o untranslated_fact)
               |> take num_facts}
    fun print_used_facts used_facts =
      tag_list 1 facts
      |> map (fn (j, fact) => fact |> untranslated_fact |> apsnd (K j))
      |> filter_used_facts used_facts
      |> map (fn ((name, _), j) => name ^ "@" ^ string_of_int j)
      |> commas
      |> enclose ("Fact" ^ plural_s (length facts) ^ " in " ^ quote name ^
                  " proof (of " ^ string_of_int (length facts) ^ "): ") "."
      |> Output.urgent_message
    fun really_go () =
      problem
      |> get_minimizing_prover ctxt mode
             (mash_learn_proof ctxt params name (prop_of goal)
                               (map untranslated_fact facts))
             name params minimize_command
      |> verbose ? tap (fn {outcome = NONE, used_facts as _ :: _, ...} =>
                           print_used_facts used_facts
                         | _ => ())
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
      (Async_Manager.launch SledgehammerN birth_time death_time (desc ())
                            ((fn (outcome_code, message) =>
                                 (verbose orelse outcome_code = someN,
                                  message ())) o go);
       (unknownN, state))
  end

fun class_of_smt_solver ctxt name =
  ctxt |> select_smt_solver name
       |> SMT_Config.solver_class_of |> SMT_Utils.string_of_class

val auto_try_max_facts_divisor = 2 (* FUDGE *)

fun run_sledgehammer (params as {debug, verbose, blocking, provers, max_facts,
                                 slice, ...})
        mode i (fact_override as {only, ...}) minimize_command state =
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
      val {facts = chained, goal, ...} = Proof.goal state
      val (_, hyp_ts, concl_t) = strip_subgoal ctxt goal i
      val ho_atp = exists (Sledgehammer_Provers.is_ho_atp ctxt) provers
      val reserved = reserved_isar_keyword_table ()
      val css = clasimpset_rule_table_of ctxt
      val facts =
        nearly_all_facts ctxt ho_atp fact_override reserved css chained hyp_ts
                         concl_t
      val _ = () |> not blocking ? kill_provers
      val _ = case find_first (not o is_prover_supported ctxt) provers of
                SOME name => error ("No such prover: " ^ name ^ ".")
              | NONE => ()
      val _ = print "Sledgehammering..."
      val (smts, (ueq_atps, full_atps)) =
        provers |> List.partition (is_smt_prover ctxt)
                ||> List.partition (is_unit_equational_atp ctxt)
      fun launch_provers state get_facts translate provers =
        let
          val facts = get_facts ()
          val num_facts = length facts
          val facts = facts ~~ (0 upto num_facts - 1)
                      |> map (translate num_facts)
          val problem =
            {state = state, goal = goal, subgoal = i, subgoal_count = n,
             facts = facts}
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
      fun get_facts label is_appropriate_prop provers =
        let
          val max_max_facts =
            case max_facts of
              SOME n => n
            | NONE =>
              0 |> fold (Integer.max o default_max_facts_for_prover ctxt slice)
                        provers
                |> mode = Auto_Try ? (fn n => n div auto_try_max_facts_divisor)
        in
          facts
          |> (case is_appropriate_prop of
                SOME is_app => filter (is_app o prop_of o snd)
              | NONE => I)
          |> relevant_facts ctxt params (hd provers) max_max_facts fact_override
                            hyp_ts concl_t
          |> map (apfst (apfst (fn name => name ())))
          |> tap (fn facts =>
                     if verbose then
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
          launch_provers state (get_facts label is_appropriate_prop o K atps)
                         (K (Untranslated_Fact o fst)) atps
      fun launch_smts accum =
        if null smts then
          accum
        else
          let
            val facts = get_facts "SMT solver" NONE smts
            val weight = SMT_Weighted_Fact oo weight_smt_fact ctxt
          in
            smts |> map (`(class_of_smt_solver ctxt))
                 |> AList.group (op =)
                 |> map (snd #> launch_provers state (K facts) weight #> fst)
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
