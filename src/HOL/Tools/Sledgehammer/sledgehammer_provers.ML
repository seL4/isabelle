(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_provers.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Generic prover abstraction for Sledgehammer.
*)

signature SLEDGEHAMMER_PROVERS =
sig
  type failure = ATP_Proof.failure
  type locality = Sledgehammer_Filter.locality
  type relevance_fudge = Sledgehammer_Filter.relevance_fudge
  type translated_formula = Sledgehammer_ATP_Translate.translated_formula
  type type_system = Sledgehammer_ATP_Translate.type_system
  type minimize_command = Sledgehammer_ATP_Reconstruct.minimize_command

  type params =
    {debug: bool,
     verbose: bool,
     overlord: bool,
     blocking: bool,
     provers: string list,
     type_sys: type_system,
     explicit_apply: bool,
     relevance_thresholds: real * real,
     max_relevant: int option,
     isar_proof: bool,
     isar_shrink_factor: int,
     timeout: Time.time,
     expect: string}

  datatype prover_fact =
    Untranslated_Fact of (string * locality) * thm |
    ATP_Translated_Fact of
      translated_formula option * ((string * locality) * thm) |
    SMT_Weighted_Fact of (string * locality) * (int option * thm)

  type prover_problem =
    {state: Proof.state,
     goal: thm,
     subgoal: int,
     subgoal_count: int,
     facts: prover_fact list,
     smt_head: (string * locality) SMT_Solver.smt_filter_head_result option}

  type prover_result =
    {outcome: failure option,
     used_facts: (string * locality) list,
     run_time_in_msecs: int option,
     message: string}

  type prover = params -> minimize_command -> prover_problem -> prover_result

  (* for experimentation purposes -- do not use in production code *)
  val atp_run_twice_threshold : int Unsynchronized.ref
  val atp_first_iter_time_frac : real Unsynchronized.ref
  val smt_triggers : bool Unsynchronized.ref
  val smt_weights : bool Unsynchronized.ref
  val smt_weight_min_facts : int Unsynchronized.ref
  val smt_min_weight : int Unsynchronized.ref
  val smt_max_weight : int Unsynchronized.ref
  val smt_max_weight_index : int Unsynchronized.ref
  val smt_weight_curve : (int -> int) Unsynchronized.ref
  val smt_max_iters : int Unsynchronized.ref
  val smt_iter_fact_frac : real Unsynchronized.ref
  val smt_iter_time_frac : real Unsynchronized.ref
  val smt_iter_min_msecs : int Unsynchronized.ref
  val smt_monomorphize_limit : int Unsynchronized.ref

  val das_Tool : string
  val select_smt_solver : string -> Proof.context -> Proof.context
  val is_smt_prover : Proof.context -> string -> bool
  val is_prover_available : Proof.context -> string -> bool
  val is_prover_installed : Proof.context -> string -> bool
  val default_max_relevant_for_prover : Proof.context -> string -> int
  val is_built_in_const_for_prover :
    Proof.context -> string -> string * typ -> term list -> bool * term list
  val atp_relevance_fudge : relevance_fudge
  val smt_relevance_fudge : relevance_fudge
  val relevance_fudge_for_prover : Proof.context -> string -> relevance_fudge
  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_run_time : bool Config.T
  val weight_smt_fact :
    theory -> int -> ((string * locality) * thm) * int
    -> (string * locality) * (int option * thm)
  val untranslated_fact : prover_fact -> (string * locality) * thm
  val smt_weighted_fact :
    theory -> int -> prover_fact * int
    -> (string * locality) * (int option * thm)
  val available_provers : Proof.context -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
  val get_prover : Proof.context -> bool -> string -> prover
  val setup : theory -> theory
end;

structure Sledgehammer_Provers : SLEDGEHAMMER_PROVERS =
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

val unremotify = perhaps (try (unprefix remote_prefix))

val select_smt_solver =
  Context.proof_map o SMT_Config.select_solver o unremotify

fun is_smt_prover ctxt name =
  let val smts = SMT_Solver.available_solvers_of ctxt in
    case try (unprefix remote_prefix) name of
      SOME base => member (op =) smts base andalso
                   SMT_Solver.is_remotely_available ctxt base
    | NONE => member (op =) smts name
  end

fun is_prover_available ctxt name =
  let val thy = ProofContext.theory_of ctxt in
    is_smt_prover ctxt name orelse member (op =) (available_atps thy) name
  end

fun is_prover_installed ctxt name =
  let val thy = ProofContext.theory_of ctxt in
    if is_smt_prover ctxt name then
      String.isPrefix remote_prefix name orelse
      SMT_Solver.is_locally_installed ctxt name
    else
      is_atp_installed thy name
  end

fun available_smt_solvers ctxt =
  let val smts = SMT_Solver.available_solvers_of ctxt in
    smts @ map (prefix remote_prefix)
               (filter (SMT_Solver.is_remotely_available ctxt) smts)
  end

fun default_max_relevant_for_prover ctxt name =
  let val thy = ProofContext.theory_of ctxt in
    if is_smt_prover ctxt name then
      SMT_Solver.default_max_relevant ctxt (unremotify name)
    else
      #default_max_relevant (get_atp thy name)
  end

(* These are either simplified away by "Meson.presimplify" (most of the time) or
   handled specially via "fFalse", "fTrue", ..., "fequal". *)
val atp_irrelevant_consts =
  [@{const_name False}, @{const_name True}, @{const_name Not},
   @{const_name conj}, @{const_name disj}, @{const_name implies},
   @{const_name HOL.eq}, @{const_name If}, @{const_name Let}]

fun is_built_in_const_for_prover ctxt name =
  if is_smt_prover ctxt name then
    let val ctxt = ctxt |> select_smt_solver name in
      fn x => fn ts =>
         if SMT_Builtin.is_builtin_num_ext ctxt (list_comb (Const x, ts)) then
           (true, [])
         else if SMT_Builtin.is_builtin_fun_ext ctxt x ts then
           (true, ts)
         else
           (false, ts)
    end
  else
    fn (s, _) => fn ts => (member (op =) atp_irrelevant_consts s, ts)

(* FUDGE *)
val atp_relevance_fudge =
  {allow_ext = true,
   worse_irrel_freq = 100.0,
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
   ridiculous_threshold = 0.01}

(* FUDGE (FIXME) *)
val smt_relevance_fudge =
  {allow_ext = false,
   worse_irrel_freq = #worse_irrel_freq atp_relevance_fudge,
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

fun relevance_fudge_for_prover ctxt name =
  if is_smt_prover ctxt name then smt_relevance_fudge else atp_relevance_fudge

fun available_provers ctxt =
  let
    val thy = ProofContext.theory_of ctxt
    val (remote_provers, local_provers) =
      sort_strings (available_atps thy) @
      sort_strings (available_smt_solvers ctxt)
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
  {debug: bool,
   verbose: bool,
   overlord: bool,
   blocking: bool,
   provers: string list,
   type_sys: type_system,
   explicit_apply: bool,
   relevance_thresholds: real * real,
   max_relevant: int option,
   isar_proof: bool,
   isar_shrink_factor: int,
   timeout: Time.time,
   expect: string}

datatype prover_fact =
  Untranslated_Fact of (string * locality) * thm |
  ATP_Translated_Fact of
    translated_formula option * ((string * locality) * thm) |
  SMT_Weighted_Fact of (string * locality) * (int option * thm)

type prover_problem =
  {state: Proof.state,
   goal: thm,
   subgoal: int,
   subgoal_count: int,
   facts: prover_fact list,
   smt_head: (string * locality) SMT_Solver.smt_filter_head_result option}

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

fun proof_banner auto =
  if auto then "Auto Sledgehammer found a proof" else "Try this command"

val smt_triggers = Unsynchronized.ref false
val smt_weights = Unsynchronized.ref false
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

fun weight_smt_fact thy num_facts ((info, th), j) =
  (info, (smt_fact_weight j num_facts, th |> Thm.transfer thy))

fun untranslated_fact (Untranslated_Fact p) = p
  | untranslated_fact (ATP_Translated_Fact (_, p)) = p
  | untranslated_fact (SMT_Weighted_Fact (info, (_, th))) = (info, th)
fun atp_translated_fact _ (ATP_Translated_Fact p) = p
  | atp_translated_fact ctxt fact =
    translate_atp_fact ctxt (untranslated_fact fact)
fun smt_weighted_fact _ _ (SMT_Weighted_Fact p, _) = p
  | smt_weighted_fact thy num_facts (fact, j) =
    (untranslated_fact fact, j) |> weight_smt_fact thy num_facts

fun overlord_file_location_for_prover prover =
  (getenv "ISABELLE_HOME_USER", "prob_" ^ prover)


(* generic TPTP-based ATPs *)

fun int_opt_add (SOME m) (SOME n) = SOME (m + n)
  | int_opt_add _ _ = NONE

val atp_run_twice_threshold = Unsynchronized.ref 50
val atp_first_iter_time_frac = Unsynchronized.ref 0.67

(* Important messages are important but not so important that users want to see
   them each time. *)
val important_message_keep_factor = 0.1

fun run_atp auto name
        ({exec, required_execs, arguments, has_incomplete_mode, proof_delims,
          known_failures, explicit_forall, use_conjecture_for_hypotheses, ...}
          : atp_config)
        ({debug, verbose, overlord, type_sys, explicit_apply, isar_proof,
          isar_shrink_factor, timeout, ...} : params)
        minimize_command ({state, goal, subgoal, facts, ...} : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val (_, hyp_ts, concl_t) = strip_subgoal goal subgoal
    val facts = facts |> map (atp_translated_fact ctxt)
    val (dest_dir, problem_prefix) =
      if overlord then overlord_file_location_for_prover name
      else (Config.get ctxt dest_dir, Config.get ctxt problem_prefix)
    val problem_file_name =
      Path.basic (problem_prefix ^ (if overlord then "" else serial_string ()) ^
                  "_" ^ string_of_int subgoal)
    val problem_path_name =
      if dest_dir = "" then
        File.tmp_path problem_file_name
      else if File.exists (Path.explode dest_dir) then
        Path.append (Path.explode dest_dir) problem_file_name
      else
        error ("No such directory: " ^ quote dest_dir ^ ".")
    val measure_run_time = verbose orelse Config.get ctxt measure_run_time
    val command = Path.explode (getenv (fst exec) ^ "/" ^ snd exec)
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n");
        val (output, t) = s |> split |> split_last |> apfst cat_lines;
        fun as_num f = f >> (fst o read_int);
        val num = as_num (Scan.many1 Symbol.is_ascii_digit);
        val digit = Scan.one Symbol.is_ascii_digit;
        val num3 = as_num (digit ::: digit ::: (digit >> single));
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b);
        val as_time = Scan.read Symbol.stopper time o raw_explode
      in (output, as_time t) end;
    fun run_on prob_file =
      case filter (curry (op =) "" o getenv o fst) (exec :: required_execs) of
        (home_var, _) :: _ =>
        error ("The environment variable " ^ quote home_var ^ " is not set.")
      | [] =>
        if File.exists command then
          let
            val readable_names = debug andalso overlord
            val (atp_problem, pool, conjecture_offset, fact_names) =
              prepare_atp_problem ctxt readable_names explicit_forall type_sys
                                  explicit_apply hyp_ts concl_t facts
            val ss = tptp_strings_for_atp_problem use_conjecture_for_hypotheses
                                                  atp_problem
            val _ = File.write_list prob_file ss
            val conjecture_shape =
              conjecture_offset + 1 upto conjecture_offset + length hyp_ts + 1
              |> map single
            fun run complete timeout =
              let
                fun weights () = atp_problem_weights atp_problem
                val core =
                  File.shell_path command ^ " " ^
                  arguments complete timeout weights ^ " " ^
                  File.shell_path prob_file
                val command =
                  (if measure_run_time then
                     "TIMEFORMAT='%3R'; { time " ^ core ^ " ; }"
                   else
                     "exec " ^ core) ^ " 2>&1"
                val ((output, msecs), res_code) =
                  bash_output command
                  |>> (if overlord then
                         prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n")
                       else
                         I)
                  |>> (if measure_run_time then split_time else rpair NONE)
                val (tstplike_proof, outcome) =
                  extract_tstplike_proof_and_outcome verbose complete res_code
                      proof_delims known_failures output
              in (output, msecs, tstplike_proof, outcome) end
            val run_twice =
              has_incomplete_mode andalso not auto andalso
              length facts >= !atp_run_twice_threshold
            val timer = Timer.startRealTimer ()
            val result =
              run (not run_twice)
                 (if run_twice then
                    seconds (0.001 * !atp_first_iter_time_frac
                             * Real.fromInt (Time.toMilliseconds timeout))
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
    fun cleanup prob_file =
      if dest_dir = "" then try File.rm prob_file else NONE
    fun export prob_file (_, (output, _, _, _)) =
      if dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode prob_file ^ "_proof")) output
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
            (proof_banner auto, type_sys, minimize_command, tstplike_proof,
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
      | SOME failure => (string_for_failure "ATP" failure, [])
  in
    {outcome = outcome, message = message, used_facts = used_facts,
     run_time_in_msecs = msecs}
  end

(* "SMT_Failure.Abnormal_Termination" carries the solver's return code. Until
   these are sorted out properly in the SMT module, we have to interpret these
   ourselves. *)
val perl_failures =
  [(127, NoPerl)]
val remote_smt_failures =
  [(22, CantConnect),
   (2, NoLibwwwPerl)]
val z3_wrapper_failures =
  [(10, NoRealZ3),
   (11, InternalError),
   (12, InternalError),
   (13, InternalError)]
val z3_failures =
  [(101, OutOfResources),
   (103, MalformedInput),
   (110, MalformedInput)]
val unix_failures =
  [(139, Crashed)]
val smt_failures =
  perl_failures @ remote_smt_failures @ z3_wrapper_failures @ z3_failures @
  unix_failures

val internal_error_prefix = "Internal error: "

fun failure_from_smt_failure (SMT_Failure.Counterexample _) = Unprovable
  | failure_from_smt_failure SMT_Failure.Time_Out = TimedOut
  | failure_from_smt_failure (SMT_Failure.Abnormal_Termination code) =
    (case AList.lookup (op =) smt_failures code of
       SOME failure => failure
     | NONE => UnknownError ("Abnormal termination with exit code " ^
                             string_of_int code ^ "."))
  | failure_from_smt_failure SMT_Failure.Out_Of_Memory = OutOfResources
  | failure_from_smt_failure (SMT_Failure.Other_Failure msg) =
    if String.isPrefix internal_error_prefix msg then InternalError
    else UnknownError msg

(* FUDGE *)
val smt_max_iters = Unsynchronized.ref 8
val smt_iter_fact_frac = Unsynchronized.ref 0.5
val smt_iter_time_frac = Unsynchronized.ref 0.5
val smt_iter_min_msecs = Unsynchronized.ref 5000
val smt_monomorphize_limit = Unsynchronized.ref 4

fun smt_filter_loop name ({debug, verbose, overlord, timeout, ...} : params)
                    state i smt_head =
  let
    val ctxt = Proof.context_of state
    val (remote, base) =
      case try (unprefix remote_prefix) name of
        SOME base => (true, base)
      | NONE => (false, name)
    val repair_context =
      select_smt_solver base
      #> Config.put SMT_Config.verbose debug
      #> (if overlord then
            Config.put SMT_Config.debug_files
                       (overlord_file_location_for_prover name
                        |> (fn (path, base) => path ^ "/" ^ base))
          else
            I)
      #> Config.put SMT_Config.infer_triggers (!smt_triggers)
      #> Config.put SMT_Config.monomorph_limit (!smt_monomorphize_limit)
    val state = state |> Proof.map_context repair_context

    fun iter timeout iter_num outcome0 time_so_far facts =
      let
        val timer = Timer.startRealTimer ()
        val ms = timeout |> Time.toMilliseconds
        val iter_timeout =
          if iter_num < !smt_max_iters then
            Int.min (ms,
                Int.max (!smt_iter_min_msecs,
                    Real.ceil (!smt_iter_time_frac * Real.fromInt ms)))
            |> Time.fromMilliseconds
          else
            timeout
        val num_facts = length facts
        val _ =
          if verbose then
            "SMT iteration with " ^ string_of_int num_facts ^ " fact" ^
            plural_s num_facts ^ " for " ^ string_from_time iter_timeout ^ "..."
            |> Output.urgent_message
          else
            ()
        val birth = Timer.checkRealTimer timer
        val _ =
          if debug then Output.urgent_message "Invoking SMT solver..." else ()
        val (outcome, used_facts) =
          (case (iter_num, smt_head) of
             (1, SOME head) => head |> apsnd (apfst (apsnd repair_context))
           | _ => SMT_Solver.smt_filter_head state facts i)
          |> SMT_Solver.smt_filter_tail iter_timeout remote
          |> (fn {outcome, used_facts} => (outcome, used_facts))
          handle exn => if Exn.is_interrupt exn then
                          reraise exn
                        else
                          (internal_error_prefix ^ ML_Compiler.exn_message exn
                           |> SMT_Failure.Other_Failure |> SOME, [])
        val death = Timer.checkRealTimer timer
        val _ =
          if verbose andalso is_some outcome then
            "SMT outcome: " ^ SMT_Failure.string_of_failure ctxt (the outcome)
            |> Output.urgent_message
          else if debug then
            Output.urgent_message "SMT solver returned."
          else
            ()
        val outcome0 = if is_none outcome0 then SOME outcome else outcome0
        val time_so_far = Time.+ (time_so_far, Time.- (death, birth))
        val too_many_facts_perhaps =
          case outcome of
            NONE => false
          | SOME (SMT_Failure.Counterexample _) => false
          | SOME SMT_Failure.Time_Out => iter_timeout <> timeout
          | SOME (SMT_Failure.Abnormal_Termination code) =>
            (if verbose then
               "The SMT solver invoked with " ^ string_of_int num_facts ^
               " fact" ^ plural_s num_facts ^ " terminated abnormally with \
               \exit code " ^ string_of_int code ^ "."
               |> warning
             else
               ();
             true (* kind of *))
          | SOME SMT_Failure.Out_Of_Memory => true
          | SOME (SMT_Failure.Other_Failure _) => true
        val timeout = Time.- (timeout, Timer.checkRealTimer timer)
      in
        if too_many_facts_perhaps andalso iter_num < !smt_max_iters andalso
           num_facts > 0 andalso Time.> (timeout, Time.zeroTime) then
          let
            val n = Real.ceil (!smt_iter_fact_frac * Real.fromInt num_facts)
          in iter timeout (iter_num + 1) outcome0 time_so_far (take n facts) end
        else
          {outcome = if is_none outcome then NONE else the outcome0,
           used_facts = used_facts,
           run_time_in_msecs = SOME (Time.toMilliseconds time_so_far)}
      end
  in iter timeout 1 NONE Time.zeroTime end

(* taken from "Mirabelle" and generalized *)
fun can_apply timeout tac state i =
  let
    val {context = ctxt, facts, goal} = Proof.goal state
    val full_tac = Method.insert_tac facts i THEN tac ctxt i
  in
    case try (TimeLimit.timeLimit timeout (Seq.pull o full_tac)) goal of
      SOME (SOME _) => true
    | _ => false
  end

val smt_metis_timeout = seconds 1.0

fun can_apply_metis debug state i ths =
  can_apply smt_metis_timeout
            (Config.put Metis_Tactics.verbose debug
             #> (fn ctxt => Metis_Tactics.metis_tac ctxt ths)) state i

fun run_smt_solver auto name (params as {debug, verbose, ...}) minimize_command
        ({state, subgoal, subgoal_count, facts, smt_head, ...}
         : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val thy = Proof.theory_of state
    val num_facts = length facts
    val facts = facts ~~ (0 upto num_facts - 1)
                |> map (smt_weighted_fact thy num_facts)
    val {outcome, used_facts, run_time_in_msecs} =
      smt_filter_loop name params state subgoal smt_head facts
    val (chained_lemmas, other_lemmas) = split_used_facts (map fst used_facts)
    val outcome = outcome |> Option.map failure_from_smt_failure
    val message =
      case outcome of
        NONE =>
        let
          val (method, settings) =
            if can_apply_metis debug state subgoal (map snd used_facts) then
              ("metis", "")
            else
              let val base = unremotify name in
                ("smt", if base = SMT_Config.solver_of ctxt then ""
                        else "smt_solver = " ^ maybe_quote base)
              end
        in
          try_command_line (proof_banner auto)
              (apply_on_subgoal settings subgoal subgoal_count ^
               command_call method (map fst other_lemmas)) ^
          minimize_line minimize_command
                        (map fst (other_lemmas @ chained_lemmas)) ^
          (if verbose then
             "\nSMT solver real CPU time: " ^
             string_from_time (Time.fromMilliseconds (the run_time_in_msecs)) ^
             "."
           else
             "")
        end
      | SOME failure => string_for_failure "SMT solver" failure
  in
    {outcome = outcome, used_facts = map fst used_facts,
     run_time_in_msecs = run_time_in_msecs, message = message}
  end

fun get_prover ctxt auto name =
  let val thy = ProofContext.theory_of ctxt in
    if is_smt_prover ctxt name then
      run_smt_solver auto name
    else if member (op =) (available_atps thy) name then
      run_atp auto name (get_atp thy name)
    else
      error ("No such prover: " ^ name ^ ".")
  end

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_run_time_setup

end;
