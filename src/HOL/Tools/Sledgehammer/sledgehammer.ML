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
     atps: string list,
     full_types: bool,
     explicit_apply: bool,
     relevance_thresholds: real * real,
     max_relevant: int option,
     isar_proof: bool,
     isar_shrink_factor: int,
     timeout: Time.time,
     expect: string}
  type problem =
    {ctxt: Proof.context,
     goal: thm,
     subgoal: int,
     axioms: (term * ((string * locality) * fol_formula) option) list}
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
  val measure_run_time : bool Config.T
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
open Sledgehammer_Filter
open Sledgehammer_Translate
open Sledgehammer_Reconstruct


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
   isar_proof: bool,
   isar_shrink_factor: int,
   timeout: Time.time,
   expect: string}

type problem =
  {ctxt: Proof.context,
   goal: thm,
   subgoal: int,
   axioms: (term * ((string * locality) * fol_formula) option) list}

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

fun extract_delimited (begin_delim, end_delim) output =
  output |> first_field begin_delim |> the |> snd
         |> first_field end_delim |> the |> fst
         |> first_field "\n" |> the |> snd
  handle Option.Option => ""

val tstp_important_message_delims =
  ("% SZS start RequiredInformation", "% SZS end RequiredInformation")

fun extract_important_message output =
  case extract_delimited tstp_important_message_delims output of
    "" => ""
  | s => s |> space_explode "\n" |> filter_out (curry (op =) "")
           |> map (perhaps (try (unprefix "%")))
           |> map (perhaps (try (unprefix " ")))
           |> space_implode "\n " |> quote

(* Splits by the first possible of a list of delimiters. *)
fun extract_proof delims output =
  case pairself (find_first (fn s => String.isSubstring s output))
                (ListPair.unzip delims) of
    (SOME begin_delim, SOME end_delim) =>
    extract_delimited (begin_delim, end_delim) output
  | _ => ""

fun extract_proof_and_outcome complete res_code proof_delims known_failures
                              output =
  case known_failure_in_output output known_failures of
    NONE => (case extract_proof proof_delims output of
             "" => ("", SOME (if res_code = 0 andalso output = "" then
                                Interrupted
                              else
                                 UnknownError))
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
  #> snd #> Substring.position "." #> fst #> Substring.string
  #> explode #> filter_out Symbol.is_blank #> parse_clause_formula_relation
  #> fst

(* TODO: move to "Sledgehammer_Reconstruct" *)
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
         known_failures, default_max_relevant, explicit_forall,
         use_conjecture_for_hypotheses}
        ({debug, verbose, overlord, full_types, explicit_apply,
          max_relevant, isar_proof, isar_shrink_factor, timeout, ...} : params)
        minimize_command ({ctxt, goal, subgoal, axioms} : problem) =
  let
    val (_, hyp_ts, concl_t) = strip_subgoal goal subgoal
    val max_relevant = the_default default_max_relevant max_relevant
    val axioms = take max_relevant axioms
    (* path to unique problem file *)
    val the_dest_dir = if overlord then getenv "ISABELLE_HOME_USER"
                       else Config.get ctxt dest_dir
    val the_problem_prefix = Config.get ctxt problem_prefix
    val problem_file_name =
      Path.basic ((if overlord then "prob_" ^ atp_name
                   else the_problem_prefix ^ serial_string ())
                  ^ "_" ^ string_of_int subgoal)
    val problem_path_name =
      if the_dest_dir = "" then
        File.tmp_path problem_file_name
      else if File.exists (Path.explode the_dest_dir) then
        Path.append (Path.explode the_dest_dir) problem_file_name
      else
        error ("No such directory: " ^ quote the_dest_dir ^ ".")
    val measure_run_time = verbose orelse Config.get ctxt measure_run_time
    val command = Path.explode (getenv (fst exec) ^ "/" ^ snd exec)
    (* write out problem file and call prover *)
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
                              explicit_apply hyp_ts concl_t axioms
            val ss = strings_for_tptp_problem use_conjecture_for_hypotheses
                                              problem
            val _ = File.write_list probfile ss
            val conjecture_shape =
              conjecture_offset + 1 upto conjecture_offset + length hyp_ts + 1
              |> map single
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
      with_path cleanup export run_on problem_path_name
    val (conjecture_shape, axiom_names) =
      repair_conjecture_shape_and_theorem_names output conjecture_shape
                                                axiom_names
    val important_message = extract_important_message output
    val (message, used_thm_names) =
      case outcome of
        NONE =>
        proof_text isar_proof
            (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
            (full_types, minimize_command, proof, axiom_names, goal, subgoal)
        |>> (fn message =>
                message ^ (if verbose then
                             "\nReal CPU time: " ^ string_of_int msecs ^ " ms."
                           else
                             "") ^
                (if important_message <> "" then
                   "\n\nImportant message from Dr. Geoff Sutcliffe:\n" ^
                   important_message
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

fun run_prover ctxt (params as {blocking, verbose, max_relevant, timeout,
                                expect, ...})
               i n relevance_override minimize_command
               (problem as {goal, axioms, ...})
               (prover as {default_max_relevant, ...}, atp_name) =
  let
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val max_relevant = the_default default_max_relevant max_relevant
    val num_axioms = Int.min (length axioms, max_relevant)
    val desc =
      "ATP " ^ quote atp_name ^
      (if verbose then
         " with " ^ string_of_int num_axioms ^ " fact" ^ plural_s num_axioms
       else
         "") ^
      " on " ^ (if n = 1 then "goal" else "subgoal " ^ string_of_int i) ^ ":" ^
      (if blocking then
         ""
       else
         "\n" ^ Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i)))
    fun run () =
      let
        val (outcome_code, message) =
          prover_fun atp_name prover params (minimize_command atp_name) problem
          |> (fn {outcome, message, ...} =>
                 (if is_some outcome then "none" else "some", message))
          handle ERROR message => ("unknown", "Error: " ^ message ^ "\n")
               | exn => ("unknown", "Internal error:\n" ^
                                    ML_Compiler.exn_message exn ^ "\n")
      in
        if expect = "" orelse outcome_code = expect then
          ()
        else if blocking then
          error ("Unexpected outcome: " ^ quote outcome_code ^ ".")
        else
          warning ("Unexpected outcome: " ^ quote outcome_code ^ ".");
        message
      end
  in
    if blocking then priority (desc ^ "\n" ^ TimeLimit.timeLimit timeout run ())
    else Async_Manager.launch das_Tool birth_time death_time desc run
  end

fun run_sledgehammer (params as {blocking, verbose, atps, full_types,
                                 relevance_thresholds, max_relevant, ...})
                     i relevance_override minimize_command state =
    if null atps then error "No ATP is set."
    else case subgoal_count state of
      0 => priority "No subgoal!"
    | n =>
      let
        val thy = Proof.theory_of state
        val timer = Timer.startRealTimer ()
        val _ = () |> not blocking ? kill_atps
        val _ = priority "Sledgehammering..."
        val provers = map (`(get_prover thy)) atps
        fun run () =
          let
            val {context = ctxt, facts = chained_ths, goal} = Proof.goal state
            val (_, hyp_ts, concl_t) = strip_subgoal goal i
            val max_max_relevant =
              case max_relevant of
                SOME n => n
              | NONE => fold (Integer.max o #default_max_relevant o fst)
                             provers 0
            val axioms =
              relevant_facts ctxt full_types relevance_thresholds
                             max_max_relevant relevance_override chained_ths
                             hyp_ts concl_t
            val problem =
              {ctxt = ctxt, goal = goal, subgoal = i,
               axioms = map (prepare_axiom ctxt) axioms}
            val num_axioms = length axioms
            val _ =
              (if blocking then Par_List.map else map)
                  (run_prover ctxt params i n relevance_override
                              minimize_command problem) provers
          in
            if verbose andalso blocking then
              priority ("Total time: " ^
                        signed_string_of_int (Time.toMilliseconds
                            (Timer.checkRealTimer timer)) ^ " ms.")
            else
              ()
          end
      in if blocking then run () else Future.fork run |> K () end

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_run_time_setup

end;
