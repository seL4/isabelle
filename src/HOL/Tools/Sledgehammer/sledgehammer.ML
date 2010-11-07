(*  Title:      HOL/Tools/Sledgehammer/sledgehammer.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER =
sig
  type failure = ATP_Proof.failure
  type locality = Sledgehammer_Filter.locality
  type relevance_fudge = Sledgehammer_Filter.relevance_fudge
  type relevance_override = Sledgehammer_Filter.relevance_override
  type translated_formula = Sledgehammer_ATP_Translate.translated_formula
  type minimize_command = Sledgehammer_ATP_Reconstruct.minimize_command

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

  datatype fact =
    Untranslated of (string * locality) * thm |
    Translated of term * ((string * locality) * translated_formula) option

  type prover_problem =
    {state: Proof.state,
     goal: thm,
     subgoal: int,
     subgoal_count: int,
     facts: fact list,
     only: bool}

  type prover_result =
    {outcome: failure option,
     used_facts: (string * locality) list,
     run_time_in_msecs: int option,
     message: string}

  type prover = params -> minimize_command -> prover_problem -> prover_result

  val smtN : string
  val is_prover_available : theory -> string -> bool
  val is_prover_installed : Proof.context -> string -> bool
  val default_max_relevant_for_prover : theory -> string -> int
  val is_built_in_const_for_prover :
    Proof.context -> string -> string * typ -> bool
  val relevance_fudge_for_prover : string -> relevance_fudge
  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_run_time : bool Config.T
  val available_provers : theory -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
  val get_prover : theory -> bool -> string -> prover
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
open Sledgehammer_ATP_Translate
open Sledgehammer_ATP_Reconstruct


(** The Sledgehammer **)

(* Identifier to distinguish Sledgehammer from other tools using
   "Async_Manager". *)
val das_Tool = "Sledgehammer"

val smtN = "smt"
val smt_prover_names = [smtN, remote_prefix ^ smtN]

val is_smt_prover = member (op =) smt_prover_names

fun is_prover_available thy name =
  is_smt_prover name orelse member (op =) (available_atps thy) name

fun is_prover_installed ctxt name =
  let val thy = ProofContext.theory_of ctxt in
    if is_smt_prover name then SMT_Solver.is_locally_installed ctxt
    else is_atp_installed thy name
  end

val smt_default_max_relevant = 250 (* FUDGE (FIXME) *)
val auto_max_relevant_divisor = 2 (* FUDGE *)

fun default_max_relevant_for_prover thy name =
  if is_smt_prover name then smt_default_max_relevant
  else #default_max_relevant (get_atp thy name)

(* These are typically simplified away by "Meson.presimplify". Equality is
   handled specially via "fequal". *)
val atp_irrelevant_consts =
  [@{const_name False}, @{const_name True}, @{const_name If}, @{const_name Let},
   @{const_name HOL.eq}]

fun is_built_in_const_for_prover ctxt name (s, T) =
  if is_smt_prover name then SMT_Builtin.is_builtin ctxt (s, T)
  else member (op =) atp_irrelevant_consts s

(* FUDGE *)
val atp_relevance_fudge =
  {worse_irrel_freq = 100.0,
   higher_order_irrel_weight = 1.05,
   abs_rel_weight = 0.5,
   abs_irrel_weight = 2.0,
   skolem_irrel_weight = 0.75,
   theory_const_rel_weight = 0.5,
   theory_const_irrel_weight = 0.25,
   intro_bonus = 0.15,
   elim_bonus = 0.15,
   simp_bonus = 0.15,
   local_bonus = 0.55,
   assum_bonus = 1.05,
   chained_bonus = 1.5,
   max_imperfect = 11.5,
   max_imperfect_exp = 1.0,
   threshold_divisor = 2.0,
   ridiculous_threshold = 0.1}

(* FUDGE (FIXME) *)
val smt_relevance_fudge =
  {worse_irrel_freq = #worse_irrel_freq atp_relevance_fudge,
   higher_order_irrel_weight = #higher_order_irrel_weight atp_relevance_fudge,
   abs_rel_weight = #abs_rel_weight atp_relevance_fudge,
   abs_irrel_weight = #abs_irrel_weight atp_relevance_fudge,
   skolem_irrel_weight = #skolem_irrel_weight atp_relevance_fudge,
   theory_const_rel_weight = #theory_const_rel_weight atp_relevance_fudge,
   theory_const_irrel_weight = #theory_const_irrel_weight atp_relevance_fudge,
   intro_bonus = #intro_bonus atp_relevance_fudge,
   elim_bonus = #elim_bonus atp_relevance_fudge,
   simp_bonus = #simp_bonus atp_relevance_fudge,
   local_bonus = #local_bonus atp_relevance_fudge,
   assum_bonus = #assum_bonus atp_relevance_fudge,
   chained_bonus = #chained_bonus atp_relevance_fudge,
   max_imperfect = #max_imperfect atp_relevance_fudge,
   max_imperfect_exp = #max_imperfect_exp atp_relevance_fudge,
   threshold_divisor = #threshold_divisor atp_relevance_fudge,
   ridiculous_threshold = #ridiculous_threshold atp_relevance_fudge}

fun relevance_fudge_for_prover name =
  if is_smt_prover name then smt_relevance_fudge else atp_relevance_fudge

fun available_provers thy =
  let
    val (remote_provers, local_provers) =
      sort_strings (available_atps thy) @ smt_prover_names
      |> List.partition (String.isPrefix remote_prefix)
  in
    Output.urgent_message ("Available provers: " ^
                           commas (local_provers @ remote_provers) ^ ".")
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

datatype fact =
  Untranslated of (string * locality) * thm |
  Translated of term * ((string * locality) * translated_formula) option

type prover_problem =
  {state: Proof.state,
   goal: thm,
   subgoal: int,
   subgoal_count: int,
   facts: fact list,
   only: bool}

type prover_result =
  {outcome: failure option,
   message: string,
   used_facts: (string * locality) list,
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

fun prover_description ctxt ({blocking, verbose, ...} : params) name num_facts i
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

fun proof_banner auto =
  if auto then "Auto Sledgehammer found a proof" else "Try this command"

(* generic TPTP-based ATPs *)

fun dest_Untranslated (Untranslated p) = p
  | dest_Untranslated (Translated _) = raise Fail "dest_Untranslated"
fun translated_fact ctxt (Untranslated p) = translate_fact ctxt p
  | translated_fact _ (Translated p) = p
fun fact_name (Untranslated ((name, _), _)) = SOME name
  | fact_name (Translated (_, p)) = Option.map (fst o fst) p

fun int_opt_add (SOME m) (SOME n) = SOME (m + n)
  | int_opt_add _ _ = NONE

(* Important messages are important but not so important that users want to see
   them each time. *)
val important_message_keep_factor = 0.1

fun run_atp auto atp_name
        {exec, required_execs, arguments, has_incomplete_mode, proof_delims,
         known_failures, default_max_relevant, explicit_forall,
         use_conjecture_for_hypotheses}
        ({debug, verbose, overlord, full_types, explicit_apply,
          max_relevant, isar_proof, isar_shrink_factor, timeout, ...} : params)
        minimize_command
        ({state, goal, subgoal, facts, only, ...} : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val (_, hyp_ts, concl_t) = strip_subgoal goal subgoal
    val facts =
      facts |> not only ? take (the_default default_max_relevant max_relevant)
            |> map (translated_fact ctxt)
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
            val (atp_problem, pool, conjecture_offset, fact_names) =
              prepare_atp_problem ctxt readable_names explicit_forall full_types
                                  explicit_apply hyp_ts concl_t facts
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
                              (output, int_opt_add msecs0 msecs, tstplike_proof,
                               outcome))
                     | result => result)
          in ((pool, conjecture_shape, fact_names), result) end
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
    val ((pool, conjecture_shape, fact_names),
         (output, msecs, tstplike_proof, outcome)) =
      with_path cleanup export run_on problem_path_name
    val (conjecture_shape, fact_names) =
      repair_conjecture_shape_and_fact_names output conjecture_shape fact_names
    val important_message =
      if not auto andalso random () <= important_message_keep_factor then
        extract_important_message output
      else
        ""
    val (message, used_facts) =
      case outcome of
        NONE =>
        proof_text isar_proof
            (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
            (proof_banner auto, full_types, minimize_command, tstplike_proof,
             fact_names, goal, subgoal)
        |>> (fn message =>
                message ^
                (if verbose then
                   "\nATP real CPU time: " ^
                   string_from_time (Time.fromMilliseconds (the msecs)) ^ "."
                 else
                   "") ^
                (if important_message <> "" then
                   "\n\nImportant message from Dr. Geoff Sutcliffe:\n" ^
                   important_message
                 else
                   ""))
      | SOME failure => (string_for_failure failure, [])
  in
    {outcome = outcome, message = message, used_facts = used_facts,
     run_time_in_msecs = msecs}
  end

fun failure_from_smt_failure (SMT_Solver.Counterexample _) = Unprovable
  | failure_from_smt_failure SMT_Solver.Time_Out = TimedOut
  | failure_from_smt_failure SMT_Solver.Out_Of_Memory = OutOfResources
  | failure_from_smt_failure _ = UnknownError

val smt_filter_max_iter = 5
val smt_filter_fact_divisor = 2

fun smt_filter_loop iter outcome0 msecs_so_far remote timeout state facts i =
  let
    val timer = Timer.startRealTimer ()
    val {outcome, used_facts, run_time_in_msecs} =
      SMT_Solver.smt_filter remote timeout state facts i
    val outcome0 = if is_none outcome0 then SOME outcome else outcome0
    val msecs_so_far = int_opt_add run_time_in_msecs msecs_so_far
    val too_many_facts_perhaps =
      case outcome of
        NONE => false
      | SOME (SMT_Solver.Counterexample _) => false
      | SOME SMT_Solver.Time_Out => false
      | SOME SMT_Solver.Out_Of_Memory => true
      | SOME _ => true
  in
    if too_many_facts_perhaps andalso iter < smt_filter_max_iter andalso
       not (null facts) then
      let val facts = take (length facts div smt_filter_fact_divisor) facts in
        smt_filter_loop (iter + 1) outcome0 msecs_so_far remote
                        (Time.- (timeout, Timer.checkRealTimer timer)) state
                        facts i
      end
    else
      {outcome = if is_none outcome then NONE else the outcome0,
       used_facts = used_facts, run_time_in_msecs = msecs_so_far}
  end

fun run_smt_solver auto remote ({timeout, ...} : params) minimize_command
                   ({state, subgoal, subgoal_count, facts, ...}
                    : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val {outcome, used_facts, run_time_in_msecs} =
      smt_filter_loop 1 NONE (SOME 0) remote timeout state
                      (map_filter (try dest_Untranslated) facts) subgoal
    val message =
      case outcome of
        NONE =>
        try_command_line (proof_banner auto)
                         (apply_on_subgoal subgoal subgoal_count ^
                          command_call smtN (map fst used_facts)) ^
        minimize_line minimize_command (map fst used_facts)
      | SOME SMT_Solver.Time_Out => "Timed out."
      | SOME (SMT_Solver.Counterexample _) => "The SMT problem is unprovable."
      | SOME failure =>
        SMT_Solver.string_of_failure ctxt "The SMT solver" failure
    val outcome = outcome |> Option.map failure_from_smt_failure (* FIXME *)
  in
    {outcome = outcome, used_facts = used_facts,
     run_time_in_msecs = run_time_in_msecs, message = message}
  end

fun get_prover thy auto name =
  if is_smt_prover name then
    run_smt_solver auto (String.isPrefix remote_prefix name)
  else
    run_atp auto name (get_atp thy name)

fun run_prover (params as {blocking, debug, max_relevant, timeout, expect, ...})
               auto minimize_command
               (problem as {state, goal, subgoal, subgoal_count, facts, ...})
               name =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val max_relevant =
      the_default (default_max_relevant_for_prover thy name) max_relevant
    val num_facts = Int.min (length facts, max_relevant)
    val desc =
      prover_description ctxt params name num_facts subgoal subgoal_count goal
    fun go () =
      let
        fun really_go () =
          get_prover thy auto name params (minimize_command name) problem
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
        List.app Output.urgent_message
                 (Async_Manager.break_into_chunks [desc ^ "\n" ^ message]);
        (success, state)
      end
    else
      (Async_Manager.launch das_Tool birth_time death_time desc (snd o go);
       (false, state))
  end

fun run_sledgehammer (params as {blocking, debug, provers, full_types,
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
      val thy = Proof.theory_of state
      val ctxt = Proof.context_of state
      val {facts = chained_ths, goal, ...} = Proof.goal state
      val (_, hyp_ts, concl_t) = strip_subgoal goal i
      val _ = () |> not blocking ? kill_provers
      val _ = if auto then () else Output.urgent_message "Sledgehammering..."
      val (smts, atps) = provers |> List.partition is_smt_prover
      fun run_provers label full_types relevance_fudge maybe_translate provers
                      (res as (success, state)) =
        if success orelse null provers then
          res
        else
          let
            val max_max_relevant =
              case max_relevant of
                SOME n => n
              | NONE =>
                0 |> fold (Integer.max o default_max_relevant_for_prover thy)
                          provers
                  |> auto ? (fn n => n div auto_max_relevant_divisor)
            val is_built_in_const =
              is_built_in_const_for_prover ctxt (hd provers)
            val facts =
              relevant_facts ctxt full_types relevance_thresholds
                             max_max_relevant is_built_in_const relevance_fudge
                             relevance_override chained_ths hyp_ts concl_t
              |> map maybe_translate
            val problem =
              {state = state, goal = goal, subgoal = i, subgoal_count = n,
               facts = facts, only = only}
            val run_prover = run_prover params auto minimize_command
          in
            if debug then
              Output.urgent_message (label ^ plural_s (length provers) ^ ": " ^
                  (if null facts then
                     "Found no relevant facts."
                   else
                     "Including (up to) " ^ string_of_int (length facts) ^
                     " relevant fact" ^ plural_s (length facts) ^ ":\n" ^
                     (facts |> map_filter fact_name
                            |> space_implode " ") ^ "."))
            else
              ();
            if auto then
              fold (fn prover => fn (true, state) => (true, state)
                                  | (false, _) => run_prover problem prover)
                   provers (false, state)
            else
              provers |> (if blocking then Par_List.map else map)
                             (run_prover problem)
                      |> exists fst |> rpair state
          end
      val run_atps =
        run_provers "ATP" full_types atp_relevance_fudge
                    (Translated o translate_fact ctxt) atps
      val run_smts =
        run_provers "SMT solver" true smt_relevance_fudge Untranslated smts
      fun run_atps_and_smt_solvers () =
        [run_atps, run_smts] |> Par_List.map (fn f => f (false, state) |> K ())
    in
      (false, state)
      |> (if blocking then run_atps #> not auto ? run_smts
          else (fn p => Future.fork (tap run_atps_and_smt_solvers) |> K p))
    end

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_run_time_setup

end;
