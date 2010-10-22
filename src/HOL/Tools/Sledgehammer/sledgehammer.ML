(*  Title:      HOL/Tools/Sledgehammer/sledgehammer.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER =
sig
  type failure = ATP_Systems.failure
  type locality = Sledgehammer_Filter.locality
  type relevance_override = Sledgehammer_Filter.relevance_override
  type fol_formula = Sledgehammer_Translate.fol_formula
  type minimize_command = Sledgehammer_Reconstruct.minimize_command

  type params =
    {blocking: bool,
     debug: bool,
     verbose: bool,
     overlord: bool,
     provers: string list,
     full_types: bool,
     explicit_apply: bool,
     relevance_thresholds: real * real,
     max_relevant: int option,
     isar_proof: bool,
     isar_shrink_factor: int,
     timeout: Time.time,
     expect: string}

  datatype axiom =
    Unprepared of (string * locality) * thm |
    Prepared of term * ((string * locality) * fol_formula) option

  type prover_problem =
    {state: Proof.state,
     goal: thm,
     subgoal: int,
     axioms: axiom list,
     only: bool}

  type prover_result =
    {outcome: failure option,
     used_axioms: (string * locality) list,
     run_time_in_msecs: int option,
     message: string}

  type prover = params -> minimize_command -> prover_problem -> prover_result

  val smtN : string
  val smt_prover_names : string list
  val smt_default_max_relevant : int
  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_run_time : bool Config.T
  val available_provers : theory -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
  val get_prover : theory -> string -> prover
  val run_sledgehammer :
    params -> bool -> int -> relevance_override -> (string -> minimize_command)
    -> Proof.state -> bool * Proof.state
  val setup : theory -> theory
end;

structure Sledgehammer : SLEDGEHAMMER =
struct

open ATP_Problem
open ATP_Proof
open ATP_Systems
open Metis_Translate
open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_Translate
open Sledgehammer_Reconstruct


(** The Sledgehammer **)

(* Identifier to distinguish Sledgehammer from other tools using
   "Async_Manager". *)
val das_Tool = "Sledgehammer"

val smtN = "smt"
val smt_prover_names = [smtN, remote_prefix ^ smtN]

val smt_default_max_relevant = 300 (* FUDGE *)
val auto_max_relevant_divisor = 2 (* FUDGE *)

fun available_provers thy =
  let
    val (remote_provers, local_provers) =
      sort_strings (available_atps thy) @ smt_prover_names
      |> List.partition (String.isPrefix remote_prefix)
  in
    priority ("Available provers: " ^ commas (local_provers @ remote_provers) ^
              ".")
  end

fun kill_provers () = Async_Manager.kill_threads das_Tool "provers"
fun running_provers () = Async_Manager.running_threads das_Tool "provers"
val messages = Async_Manager.thread_messages das_Tool "prover"

(** problems, results, ATPs, etc. **)

type params =
  {blocking: bool,
   debug: bool,
   verbose: bool,
   overlord: bool,
   provers: string list,
   full_types: bool,
   explicit_apply: bool,
   relevance_thresholds: real * real,
   max_relevant: int option,
   isar_proof: bool,
   isar_shrink_factor: int,
   timeout: Time.time,
   expect: string}

datatype axiom =
  Unprepared of (string * locality) * thm |
  Prepared of term * ((string * locality) * fol_formula) option

type prover_problem =
  {state: Proof.state,
   goal: thm,
   subgoal: int,
   axioms: axiom list,
   only: bool}

type prover_result =
  {outcome: failure option,
   message: string,
   used_axioms: (string * locality) list,
   run_time_in_msecs: int option}

type prover = params -> minimize_command -> prover_problem -> prover_result

(* configuration attributes *)

val (dest_dir, dest_dir_setup) =
  Attrib.config_string "sledgehammer_dest_dir" (K "")
  (* Empty string means create files in Isabelle's temporary files directory. *)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "sledgehammer_problem_prefix" (K "prob")

val (measure_run_time, measure_run_time_setup) =
  Attrib.config_bool "sledgehammer_measure_run_time" (K false)

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path)

fun prover_description ctxt ({blocking, verbose, ...} : params) name num_axioms
                       i n goal =
  quote name ^
  (if verbose then
     " with " ^ string_of_int num_axioms ^ " fact" ^ plural_s num_axioms
   else
     "") ^
  " on " ^ (if n = 1 then "goal" else "subgoal " ^ string_of_int i) ^ ":" ^
  (if blocking then
     ""
   else
     "\n" ^ Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i)))

fun proof_banner auto =
  if auto then "Sledgehammer found a proof" else "Try this command"

(* generic TPTP-based ATPs *)

fun dest_Unprepared (Unprepared p) = p
  | dest_Unprepared (Prepared _) = raise Fail "dest_Unprepared"
fun prepared_axiom ctxt (Unprepared p) = prepare_axiom ctxt p
  | prepared_axiom _ (Prepared p) = p

fun int_option_add (SOME m) (SOME n) = SOME (m + n)
  | int_option_add _ _ = NONE

(* Important messages are important but not so important that users want to see
   them each time. *)
val important_message_keep_factor = 0.1

fun atp_fun auto atp_name
        {exec, required_execs, arguments, has_incomplete_mode, proof_delims,
         known_failures, default_max_relevant, explicit_forall,
         use_conjecture_for_hypotheses}
        ({debug, verbose, overlord, full_types, explicit_apply,
          max_relevant, isar_proof, isar_shrink_factor, timeout, ...} : params)
        minimize_command
        ({state, goal, subgoal, axioms, only} : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val (_, hyp_ts, concl_t) = strip_subgoal goal subgoal
    val axioms =
      axioms |> not only ? take (the_default default_max_relevant max_relevant)
             |> map (prepared_axiom ctxt)
    val dest_dir = if overlord then getenv "ISABELLE_HOME_USER"
                   else Config.get ctxt dest_dir
    val problem_prefix = Config.get ctxt problem_prefix
    val problem_file_name =
      Path.basic ((if overlord then "prob_" ^ atp_name
                   else problem_prefix ^ serial_string ())
                  ^ "_" ^ string_of_int subgoal)
    val problem_path_name =
      if dest_dir = "" then
        File.tmp_path problem_file_name
      else if File.exists (Path.explode dest_dir) then
        Path.append (Path.explode dest_dir) problem_file_name
      else
        error ("No such directory: " ^ quote dest_dir ^ ".")
    val measure_run_time = verbose orelse Config.get ctxt measure_run_time
    val command = Path.explode (getenv (fst exec) ^ "/" ^ snd exec)
    (* write out problem file and call ATP *)
    fun command_line complete timeout probfile =
      let
        val core = File.shell_path command ^ " " ^ arguments complete timeout ^
                   " " ^ File.shell_path probfile
      in
        (if measure_run_time then "TIMEFORMAT='%3R'; { time " ^ core ^ " ; }"
         else "exec " ^ core) ^ " 2>&1"
      end
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n");
        val (output, t) = s |> split |> split_last |> apfst cat_lines;
        fun as_num f = f >> (fst o read_int);
        val num = as_num (Scan.many1 Symbol.is_ascii_digit);
        val digit = Scan.one Symbol.is_ascii_digit;
        val num3 = as_num (digit ::: digit ::: (digit >> single));
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b);
        val as_time = Scan.read Symbol.stopper time o explode
      in (output, as_time t) end;
    fun run_on probfile =
      case filter (curry (op =) "" o getenv o fst) (exec :: required_execs) of
        (home_var, _) :: _ =>
        error ("The environment variable " ^ quote home_var ^ " is not set.")
      | [] =>
        if File.exists command then
          let
            fun run complete timeout =
              let
                val command = command_line complete timeout probfile
                val ((output, msecs), res_code) =
                  bash_output command
                  |>> (if overlord then
                         prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n")
                       else
                         I)
                  |>> (if measure_run_time then split_time else rpair NONE)
                val (tstplike_proof, outcome) =
                  extract_tstplike_proof_and_outcome complete res_code
                      proof_delims known_failures output
              in (output, msecs, tstplike_proof, outcome) end
            val readable_names = debug andalso overlord
            val (atp_problem, pool, conjecture_offset, axiom_names) =
              prepare_atp_problem ctxt readable_names explicit_forall full_types
                                  explicit_apply hyp_ts concl_t axioms
            val ss = tptp_strings_for_atp_problem use_conjecture_for_hypotheses
                                                  atp_problem
            val _ = File.write_list probfile ss
            val conjecture_shape =
              conjecture_offset + 1 upto conjecture_offset + length hyp_ts + 1
              |> map single
            val run_twice = has_incomplete_mode andalso not auto
            val timer = Timer.startRealTimer ()
            val result =
              run false (if run_twice then
                           Time.fromMilliseconds
                                         (2 * Time.toMilliseconds timeout div 3)
                         else
                           timeout)
              |> run_twice
                 ? (fn (_, msecs0, _, SOME _) =>
                       run true (Time.- (timeout, Timer.checkRealTimer timer))
                       |> (fn (output, msecs, tstplike_proof, outcome) =>
                              (output, int_option_add msecs0 msecs,
                               tstplike_proof, outcome))
                     | result => result)
          in ((pool, conjecture_shape, axiom_names), result) end
        else
          error ("Bad executable: " ^ Path.implode command ^ ".")

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup probfile =
      if dest_dir = "" then try File.rm probfile else NONE
    fun export probfile (_, (output, _, _, _)) =
      if dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode probfile ^ "_proof")) output
    val ((pool, conjecture_shape, axiom_names),
         (output, msecs, tstplike_proof, outcome)) =
      with_path cleanup export run_on problem_path_name
    val (conjecture_shape, axiom_names) =
      repair_conjecture_shape_and_axiom_names output conjecture_shape
                                              axiom_names
    val important_message =
      if random () <= important_message_keep_factor then
        extract_important_message output
      else
        ""
    val (message, used_axioms) =
      case outcome of
        NONE =>
        proof_text isar_proof
            (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
            (proof_banner auto, full_types, minimize_command, tstplike_proof,
             axiom_names, goal, subgoal)
        |>> (fn message =>
                message ^ (if verbose then
                             "\nATP real CPU time: " ^
                             string_of_int (the msecs) ^ " ms."
                           else
                             "") ^
                (if important_message <> "" then
                   "\n\nImportant message from Dr. Geoff Sutcliffe:\n" ^
                   important_message
                 else
                   ""))
      | SOME failure => (string_for_failure failure, [])
  in
    {outcome = outcome, message = message, used_axioms = used_axioms,
     run_time_in_msecs = msecs}
  end

fun get_atp_as_prover thy name = atp_fun false name (get_atp thy name)

fun run_atp_somehow (params as {blocking, debug, max_relevant, timeout,
                                expect, ...})
                    auto i n minimize_command
                    (problem as {state, goal, axioms, ...})
                    (prover as {default_max_relevant, ...}, atp_name) =
  let
    val ctxt = Proof.context_of state
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val max_relevant = the_default default_max_relevant max_relevant
    val num_axioms = Int.min (length axioms, max_relevant)
    val desc = prover_description ctxt params atp_name num_axioms i n goal
    fun go () =
      let
        fun really_go () =
          atp_fun auto atp_name prover params (minimize_command atp_name)
                  problem
          |> (fn {outcome, message, ...} =>
                 (if is_some outcome then "none" else "some", message))
        val (outcome_code, message) =
          if debug then
            really_go ()
          else
            (really_go ()
             handle ERROR message => ("unknown", "Error: " ^ message ^ "\n")
                  | exn => ("unknown", "Internal error:\n" ^
                                       ML_Compiler.exn_message exn ^ "\n"))
        val _ =
          if expect = "" orelse outcome_code = expect then
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
             Pretty.chunks [Pretty.str "", Pretty.mark Markup.hilite
                 (Pretty.str message)]))
      end
    else if blocking then
      let val (success, message) = TimeLimit.timeLimit timeout go () in
        List.app priority
                 (Async_Manager.break_into_chunks [desc ^ "\n" ^ message]);
        (success, state)
      end
    else
      (Async_Manager.launch das_Tool birth_time death_time desc (snd o go);
       (false, state))
  end

(* FIXME: dummy *)
fun run_smt_solver remote timeout state axioms i =
  {outcome = NONE, used_axioms = axioms |> take 5 |> map fst,
   run_time_in_msecs = NONE}

fun get_smt_solver_as_prover remote ({timeout, ...} : params) minimize_command
                             ({state, subgoal, axioms, ...} : prover_problem) =
  let
    val {outcome, used_axioms, run_time_in_msecs} =
      run_smt_solver remote timeout state
                     (map_filter (try dest_Unprepared) axioms) subgoal
    val message =
      if outcome = NONE then
        sendback_line (proof_banner false)
                      (apply_on_subgoal subgoal (subgoal_count state) ^
                       command_call smtN (map fst used_axioms))
      else
        ""
  in
    {outcome = outcome, used_axioms = used_axioms,
     run_time_in_msecs = run_time_in_msecs, message = message}
  end

fun get_prover thy name =
  if member (op =) smt_prover_names name then
    get_smt_solver_as_prover (String.isPrefix remote_prefix)
  else
    get_atp_as_prover thy name

fun run_smt_solver_somehow state params minimize_command i n goal axioms
                           (remote, name) =
  let
    val ctxt = Proof.context_of state
    val desc = prover_description ctxt params name (length axioms) i n goal
    val problem =
      {state = state, goal = goal, subgoal = i,
       axioms = axioms |> map Unprepared, only = true}
    val {outcome, used_axioms, message, ...} =
      get_smt_solver_as_prover remote params minimize_command problem
    val _ =
      priority (das_Tool ^ ": " ^ desc ^ "\n" ^
                (if outcome = NONE then message
                 else "An unknown error occurred."))
  in outcome = NONE end

fun run_sledgehammer (params as {blocking, provers, full_types,
                                 relevance_thresholds, max_relevant, timeout,
                                 ...})
                     auto i (relevance_override as {only, ...}) minimize_command
                     state =
  if null provers then
    error "No prover is set."
  else case subgoal_count state of
    0 => (priority "No subgoal!"; (false, state))
  | n =>
    let
      val _ = Proof.assert_backward state
      val thy = Proof.theory_of state
      val {context = ctxt, facts = chained_ths, goal} = Proof.goal state
      val (_, hyp_ts, concl_t) = strip_subgoal goal i
      val _ = () |> not blocking ? kill_provers
      val _ = if auto then () else priority "Sledgehammering..."
      val (smts, atps) =
        provers |> List.partition (member (op =) smt_prover_names)
                |>> (take 1 #> map (`(String.isPrefix remote_prefix)))
                ||> map (`(get_atp thy))
      fun run_atps (res as (success, state)) =
        if success orelse null atps then
          res
        else
          let
            val max_max_relevant =
              case max_relevant of
                SOME n => n
              | NONE =>
                0 |> fold (Integer.max o #default_max_relevant o fst) atps
                  |> auto ? (fn n => n div auto_max_relevant_divisor)
            val axioms =
              relevant_facts ctxt full_types relevance_thresholds
                             max_max_relevant relevance_override chained_ths
                             hyp_ts concl_t
            val problem =
              {state = state, goal = goal, subgoal = i,
               axioms = axioms |> map (Prepared o prepare_axiom ctxt),
               only = only}
            val run_atp_somehow =
              run_atp_somehow params auto i n minimize_command problem
          in
            if auto then
              fold (fn prover => fn (true, state) => (true, state)
                                  | (false, _) => run_atp_somehow prover)
                   atps (false, state)
            else
              atps |> (if blocking then Par_List.map else map) run_atp_somehow
                   |> exists fst |> rpair state
          end
      fun run_smt_solvers (res as (success, state)) =
        if success orelse null smts then
          res
        else
          let
            val max_relevant =
              max_relevant |> the_default smt_default_max_relevant
            val axioms =
              relevant_facts ctxt full_types relevance_thresholds
                             max_relevant relevance_override chained_ths
                             hyp_ts concl_t
          in
            smts |> map (run_smt_solver_somehow state params minimize_command i
                                                n goal axioms)
                 |> exists I |> rpair state
          end
      fun run_atps_and_smt_solvers () =
        [run_atps, run_smt_solvers]
        |> Par_List.map (fn f => f (false, state) |> K ())
    in
      if blocking then
        (false, state) |> run_atps |> not auto ? run_smt_solvers
      else
        Future.fork (tap run_atps_and_smt_solvers) |> K (false, state)
    end

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_run_time_setup

end;
