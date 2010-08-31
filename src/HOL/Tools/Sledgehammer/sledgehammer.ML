(*  Title:      HOL/Tools/Sledgehammer/sledgehammer.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER =
sig
  type failure = ATP_Systems.failure
  type locality = Sledgehammer_Fact_Filter.locality
  type relevance_override = Sledgehammer_Fact_Filter.relevance_override
  type minimize_command = Sledgehammer_Proof_Reconstruct.minimize_command
  type params =
    {blocking: bool,
     debug: bool,
     verbose: bool,
     overlord: bool,
     atps: string list,
     full_types: bool,
     explicit_apply: bool,
     relevance_thresholds: real * real,
     max_relevant: int option,
     theory_relevant: bool option,
     isar_proof: bool,
     isar_shrink_factor: int,
     timeout: Time.time}
  type problem =
    {subgoal: int,
     goal: Proof.context * (thm list * thm),
     relevance_override: relevance_override,
     axioms: ((string * locality) * thm) list option}
  type prover_result =
    {outcome: failure option,
     message: string,
     pool: string Symtab.table,
     used_thm_names: (string * locality) list,
     atp_run_time_in_msecs: int,
     output: string,
     proof: string,
     axiom_names: (string * locality) list vector,
     conjecture_shape: int list list}
  type prover = params -> minimize_command -> problem -> prover_result

  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_runtime : bool Config.T
  val kill_atps: unit -> unit
  val running_atps: unit -> unit
  val messages: int option -> unit
  val get_prover_fun : theory -> string -> prover
  val run_sledgehammer :
    params -> int -> relevance_override -> (string -> minimize_command)
    -> Proof.state -> unit
  val setup : theory -> theory
end;

structure Sledgehammer : SLEDGEHAMMER =
struct

open ATP_Problem
open ATP_Systems
open Metis_Clauses
open Sledgehammer_Util
open Sledgehammer_Fact_Filter
open Sledgehammer_Translate
open Sledgehammer_Proof_Reconstruct


(** The Sledgehammer **)

(* Identifier to distinguish Sledgehammer from other tools using
   "Async_Manager". *)
val das_Tool = "Sledgehammer"

fun kill_atps () = Async_Manager.kill_threads das_Tool "ATPs"
fun running_atps () = Async_Manager.running_threads das_Tool "ATPs"
val messages = Async_Manager.thread_messages das_Tool "ATP"

(** problems, results, provers, etc. **)

type params =
  {blocking: bool,
   debug: bool,
   verbose: bool,
   overlord: bool,
   atps: string list,
   full_types: bool,
   explicit_apply: bool,
   relevance_thresholds: real * real,
   max_relevant: int option,
   theory_relevant: bool option,
   isar_proof: bool,
   isar_shrink_factor: int,
   timeout: Time.time}

type problem =
  {subgoal: int,
   goal: Proof.context * (thm list * thm),
   relevance_override: relevance_override,
   axioms: ((string * locality) * thm) list option}

type prover_result =
  {outcome: failure option,
   message: string,
   pool: string Symtab.table,
   used_thm_names: (string * locality) list,
   atp_run_time_in_msecs: int,
   output: string,
   proof: string,
   axiom_names: (string * locality) list vector,
   conjecture_shape: int list list}

type prover = params -> minimize_command -> problem -> prover_result

(* configuration attributes *)

val (dest_dir, dest_dir_setup) = Attrib.config_string "atp_dest_dir" (K "");
  (*Empty string means create files in Isabelle's temporary files directory.*)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "atp_problem_prefix" (K "prob");

val (measure_runtime, measure_runtime_setup) =
  Attrib.config_bool "atp_measure_runtime" (K false);

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path)

(* Splits by the first possible of a list of delimiters. *)
fun extract_proof delims output =
  case pairself (find_first (fn s => String.isSubstring s output))
                (ListPair.unzip delims) of
    (SOME begin_delim, SOME end_delim) =>
    (output |> first_field begin_delim |> the |> snd
            |> first_field end_delim |> the |> fst
            |> first_field "\n" |> the |> snd
     handle Option.Option => "")
  | _ => ""

fun extract_proof_and_outcome complete res_code proof_delims known_failures
                              output =
  case known_failure_in_output output known_failures of
    NONE => (case extract_proof proof_delims output of
             "" => ("", SOME MalformedOutput)
           | proof => if res_code = 0 then (proof, NONE)
                      else ("", SOME UnknownError))
  | SOME failure =>
    ("", SOME (if failure = IncompleteUnprovable andalso complete then
                 Unprovable
               else
                 failure))

fun extract_clause_sequence output =
  let
    val tokens_of = String.tokens (not o Char.isAlphaNum)
    fun extract_num ("clause" :: (ss as _ :: _)) =
    Int.fromString (List.last ss)
      | extract_num _ = NONE
  in output |> split_lines |> map_filter (extract_num o tokens_of) end

val set_ClauseFormulaRelationN = "set_ClauseFormulaRelation"

val parse_clause_formula_pair =
  $$ "(" |-- scan_integer --| $$ ","
  -- (Symbol.scan_id ::: Scan.repeat ($$ "," |-- Symbol.scan_id)) --| $$ ")"
  --| Scan.option ($$ ",")
val parse_clause_formula_relation =
  Scan.this_string set_ClauseFormulaRelationN |-- $$ "("
  |-- Scan.repeat parse_clause_formula_pair
val extract_clause_formula_relation =
  Substring.full #> Substring.position set_ClauseFormulaRelationN
  #> snd #> Substring.string #> strip_spaces_except_between_ident_chars
  #> explode #> parse_clause_formula_relation #> fst

(* TODO: move to "Sledgehammer_Proof_Reconstruct.ML" *)
fun repair_conjecture_shape_and_theorem_names output conjecture_shape
                                              axiom_names =
  if String.isSubstring set_ClauseFormulaRelationN output then
    (* This is a hack required for keeping track of axioms after they have been
       clausified by SPASS's Flotter tool. The "ATP/scripts/spass" script is
       also part of this hack. *)
    let
      val j0 = hd (hd conjecture_shape)
      val seq = extract_clause_sequence output
      val name_map = extract_clause_formula_relation output
      fun renumber_conjecture j =
        conjecture_prefix ^ string_of_int (j - j0)
        |> AList.find (fn (s, ss) => member (op =) ss s) name_map
        |> map (fn s => find_index (curry (op =) s) seq + 1)
      fun names_for_number j =
        j |> AList.lookup (op =) name_map |> these
          |> map_filter (try (unprefix axiom_prefix)) |> map unascii_of
          |> map (fn name =>
                     (name, name |> find_first_in_list_vector axiom_names
                                 |> the)
                     handle Option.Option =>
                            error ("No such fact: " ^ quote name ^ "."))
    in
      (conjecture_shape |> map (maps renumber_conjecture),
       seq |> map names_for_number |> Vector.fromList)
    end
  else
    (conjecture_shape, axiom_names)


(* generic TPTP-based provers *)

fun prover_fun atp_name
        {exec, required_execs, arguments, has_incomplete_mode, proof_delims,
         known_failures, default_max_relevant, default_theory_relevant,
         explicit_forall, use_conjecture_for_hypotheses}
        ({debug, verbose, overlord, full_types, explicit_apply,
          relevance_thresholds, max_relevant, theory_relevant, isar_proof,
          isar_shrink_factor, timeout, ...} : params)
        minimize_command
        ({subgoal, goal = (ctxt, (chained_ths, th)), relevance_override,
          axioms} : problem) =
  let
    val (_, hyp_ts, concl_t) = strip_subgoal th subgoal

    val print = priority
    fun print_v f = () |> verbose ? print o f
    fun print_d f = () |> debug ? print o f

    val the_axioms =
      case axioms of
        SOME axioms => axioms
      | NONE =>
        (relevant_facts ctxt full_types relevance_thresholds
                        (the_default default_max_relevant max_relevant)
                        (the_default default_theory_relevant theory_relevant)
                        relevance_override chained_ths hyp_ts concl_t
         |> tap ((fn n => print_v (fn () =>
                          "Selected " ^ string_of_int n ^ " fact" ^ plural_s n ^
                          " for " ^ quote atp_name ^ ".")) o length))

    (* path to unique problem file *)
    val the_dest_dir = if overlord then getenv "ISABELLE_HOME_USER"
                       else Config.get ctxt dest_dir;
    val the_problem_prefix = Config.get ctxt problem_prefix;
    fun prob_pathname nr =
      let
        val probfile =
          Path.basic ((if overlord then "prob_" ^ atp_name
                       else the_problem_prefix ^ serial_string ())
                      ^ "_" ^ string_of_int nr)
      in
        if the_dest_dir = "" then File.tmp_path probfile
        else if File.exists (Path.explode the_dest_dir)
        then Path.append (Path.explode the_dest_dir) probfile
        else error ("No such directory: " ^ quote the_dest_dir ^ ".")
      end;

    val measure_run_time = verbose orelse Config.get ctxt measure_runtime
    val command = Path.explode (getenv (fst exec) ^ "/" ^ snd exec)
    (* write out problem file and call prover *)
    fun command_line complete timeout probfile =
      let
        val core = File.shell_path command ^ " " ^ arguments complete timeout ^
                   " " ^ File.shell_path probfile
      in
        (if measure_run_time then "TIMEFORMAT='%3U'; { time " ^ core ^ " ; }"
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
        val as_time = the_default 0 o Scan.read Symbol.stopper time o explode;
      in (output, as_time t) end;
    fun run_on probfile =
      case filter (curry (op =) "" o getenv o fst) (exec :: required_execs) of
        (home_var, _) :: _ =>
        error ("The environment variable " ^ quote home_var ^ " is not set.")
      | [] =>
        if File.exists command then
          let
            fun do_run complete timeout =
              let
                val command = command_line complete timeout probfile
                val ((output, msecs), res_code) =
                  bash_output command
                  |>> (if overlord then
                         prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n")
                       else
                         I)
                  |>> (if measure_run_time then split_time else rpair 0)
                val (proof, outcome) =
                  extract_proof_and_outcome complete res_code proof_delims
                                            known_failures output
              in (output, msecs, proof, outcome) end
            val readable_names = debug andalso overlord
            val (problem, pool, conjecture_offset, axiom_names) =
              prepare_problem ctxt readable_names explicit_forall full_types
                              explicit_apply hyp_ts concl_t the_axioms
            val ss = strings_for_tptp_problem use_conjecture_for_hypotheses
                                              problem
            val _ = File.write_list probfile ss
            val conjecture_shape =
              conjecture_offset + 1 upto conjecture_offset + length hyp_ts + 1
              |> map single
            val _ = print_d (fn () => "Running " ^ quote atp_name ^ "...")
            val timer = Timer.startRealTimer ()
            val result =
              do_run false (if has_incomplete_mode then
                              Time.fromMilliseconds
                                         (2 * Time.toMilliseconds timeout div 3)
                            else
                              timeout)
              |> has_incomplete_mode
                 ? (fn (_, msecs0, _, SOME _) =>
                       do_run true
                              (Time.- (timeout, Timer.checkRealTimer timer))
                       |> (fn (output, msecs, proof, outcome) =>
                              (output, msecs0 + msecs, proof, outcome))
                     | result => result)
          in ((pool, conjecture_shape, axiom_names), result) end
        else
          error ("Bad executable: " ^ Path.implode command ^ ".")

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup probfile =
      if the_dest_dir = "" then try File.rm probfile else NONE
    fun export probfile (_, (output, _, _, _)) =
      if the_dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode probfile ^ "_proof")) output
    val ((pool, conjecture_shape, axiom_names),
         (output, msecs, proof, outcome)) =
      with_path cleanup export run_on (prob_pathname subgoal)
    val (conjecture_shape, axiom_names) =
      repair_conjecture_shape_and_theorem_names output conjecture_shape
                                                axiom_names
    val (message, used_thm_names) =
      case outcome of
        NONE =>
        proof_text isar_proof
            (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
            (full_types, minimize_command, proof, axiom_names, th, subgoal)
        |>> (fn message =>
                message ^ (if verbose then
                             "\nATP CPU time: " ^ string_of_int msecs ^ " ms."
                           else
                             ""))
      | SOME failure => (string_for_failure failure, [])
  in
    {outcome = outcome, message = message, pool = pool,
     used_thm_names = used_thm_names, atp_run_time_in_msecs = msecs,
     output = output, proof = proof, axiom_names = axiom_names,
     conjecture_shape = conjecture_shape}
  end

fun get_prover_fun thy name = prover_fun name (get_prover thy name)

fun start_prover_thread (params as {blocking, verbose, full_types, timeout,
                                    ...})
                        i n relevance_override minimize_command proof_state
                        atp_name =
  let
    val thy = Proof.theory_of proof_state
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val prover = get_prover_fun thy atp_name
    val {context = ctxt, facts, goal} = Proof.goal proof_state;
    val desc =
      "ATP " ^ quote atp_name ^ " for subgoal " ^ string_of_int i ^ ":\n" ^
      Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i));
    fun run () =
      let
        val problem =
          {subgoal = i, goal = (ctxt, (facts, goal)),
           relevance_override = relevance_override, axioms = NONE}
      in
        prover params (minimize_command atp_name) problem |> #message
        handle ERROR message => "Error: " ^ message ^ "\n"
             | exn => "Internal error:\n" ^ ML_Compiler.exn_message exn ^ "\n"
      end
  in
    if blocking then
      priority (desc ^ "\n" ^ TimeLimit.timeLimit timeout run ())
    else
      Async_Manager.launch das_Tool verbose birth_time death_time desc run
  end

fun run_sledgehammer {atps = [], ...} _ _ _ _ = error "No ATP is set."
  | run_sledgehammer (params as {blocking, atps, ...}) i relevance_override
                     minimize_command state =
    case subgoal_count state of
      0 => priority "No subgoal!"
    | n =>
      let
        val _ = kill_atps ()
        val _ = priority "Sledgehammering..."
        val _ =
          (if blocking then Par_List.map else map)
              (start_prover_thread params i n relevance_override
                                   minimize_command state) atps
      in () end

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_runtime_setup

end;
