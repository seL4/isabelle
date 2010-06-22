(*  Title:      HOL/Tools/ATP_Manager/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  type prover = ATP_Manager.prover

  (* hooks for problem files *)
  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_runtime : bool Config.T

  val refresh_systems_on_tptp : unit -> unit
  val default_atps_param_value : unit -> string
  val setup : theory -> theory
end;

structure ATP_Systems : ATP_SYSTEMS =
struct

open Sledgehammer_Util
open Sledgehammer_Fact_Preprocessor
open Sledgehammer_HOL_Clause
open Sledgehammer_Fact_Filter
open Sledgehammer_Proof_Reconstruct
open Sledgehammer_TPTP_Format
open ATP_Manager

(** generic ATP **)

(* external problem files *)

val (dest_dir, dest_dir_setup) = Attrib.config_string "atp_dest_dir" (K "");
  (*Empty string means create files in Isabelle's temporary files directory.*)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "atp_problem_prefix" (K "prob");

val (measure_runtime, measure_runtime_setup) =
  Attrib.config_bool "atp_measure_runtime" (K false);


(* prover configuration *)

type prover_config =
  {home_var: string,
   executable: string,
   arguments: Time.time -> string,
   proof_delims: (string * string) list,
   known_failures: (failure * string) list,
   max_axiom_clauses: int,
   prefers_theory_relevant: bool};


(* basic template *)

val remotify = prefix "remote_"

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

fun extract_proof_and_outcome res_code proof_delims known_failures output =
  case map_filter (fn (failure, pattern) =>
                      if String.isSubstring pattern output then SOME failure
                      else NONE) known_failures of
    [] => (case extract_proof proof_delims output of
             "" => ("", SOME UnknownError)
           | proof => if res_code = 0 then (proof, NONE)
                      else ("", SOME UnknownError))
  | (failure :: _) => ("", SOME failure)

fun string_for_failure Unprovable = "The ATP problem is unprovable."
  | string_for_failure IncompleteUnprovable =
    "The ATP cannot prove the problem."
  | string_for_failure TimedOut = "Timed out."
  | string_for_failure OutOfResources = "The ATP ran out of resources."
  | string_for_failure OldSpass =
    (* FIXME: Change the error message below to point to the Isabelle download
       page once the package is there (around the Isabelle2010 release). *)
    "Warning: Sledgehammer requires a more recent version of SPASS with \
    \support for the TPTP syntax. To install it, download and untar the \
    \package \"http://isabelle.in.tum.de/~blanchet/spass-3.7.tgz\" and add the \
    \\"spass-3.7\" directory's full path to \"" ^
    Path.implode (Path.expand (Path.appends
        (Path.variable "ISABELLE_HOME_USER" ::
         map Path.basic ["etc", "components"]))) ^
    "\" on a line of its own."
  | string_for_failure MalformedInput =
    "Internal Sledgehammer error: The ATP problem is malformed. Please report \
    \this to the Isabelle developers."
  | string_for_failure MalformedOutput = "Error: The ATP output is malformed."
  | string_for_failure UnknownError = "Error: An unknown ATP error occurred."

fun shape_of_clauses _ [] = []
  | shape_of_clauses j ([] :: clauses) = [] :: shape_of_clauses j clauses
  | shape_of_clauses j ((_ :: lits) :: clauses) =
    let val shape = shape_of_clauses (j + 1) (lits :: clauses) in
      (j :: hd shape) :: tl shape
    end

(* generic TPTP-based provers *)

fun generic_tptp_prover
        (name, {home_var, executable, arguments, proof_delims, known_failures,
                max_axiom_clauses, prefers_theory_relevant})
        ({debug, overlord, full_types, explicit_apply, respect_no_atp,
          relevance_threshold, relevance_convergence, theory_relevant,
          defs_relevant, isar_proof, isar_shrink_factor, ...} : params)
        minimize_command timeout
        ({subgoal, goal, relevance_override, axiom_clauses, filtered_clauses}
         : problem) =
  let
    (* get clauses and prepare them for writing *)
    val (ctxt, (_, th)) = goal;
    val thy = ProofContext.theory_of ctxt;
    val goal_clss = #1 (neg_conjecture_clauses ctxt th subgoal)
    val goal_cls = List.concat goal_clss
    val the_filtered_clauses =
      (case filtered_clauses of
        NONE => relevant_facts full_types respect_no_atp relevance_threshold
                    relevance_convergence defs_relevant max_axiom_clauses
                    (the_default prefers_theory_relevant theory_relevant)
                    relevance_override goal goal_cls
      | SOME fcls => fcls);
    val the_axiom_clauses = axiom_clauses |> the_default the_filtered_clauses
    val (internal_thm_names, clauses) =
      prepare_clauses full_types goal_cls the_axiom_clauses the_filtered_clauses
                      thy

    (* path to unique problem file *)
    val the_dest_dir = if overlord then getenv "ISABELLE_HOME_USER"
                       else Config.get ctxt dest_dir;
    val the_problem_prefix = Config.get ctxt problem_prefix;
    fun prob_pathname nr =
      let
        val probfile =
          Path.basic ((if overlord then "prob_" ^ name
                       else the_problem_prefix ^ serial_string ())
                      ^ "_" ^ string_of_int nr)
      in
        if the_dest_dir = "" then File.tmp_path probfile
        else if File.exists (Path.explode the_dest_dir)
        then Path.append (Path.explode the_dest_dir) probfile
        else error ("No such directory: " ^ the_dest_dir ^ ".")
      end;

    val home = getenv home_var
    val command = Path.explode (home ^ "/" ^ executable)
    (* write out problem file and call prover *)
    fun command_line probfile =
      (if Config.get ctxt measure_runtime then
         "TIMEFORMAT='%3U'; { time " ^
         space_implode " " [File.shell_path command, arguments timeout,
                            File.shell_path probfile] ^ " ; } 2>&1"
       else
         space_implode " " ["exec", File.shell_path command, arguments timeout,
                            File.shell_path probfile, "2>&1"]) ^
      (if overlord then
         " | sed 's/,/, /g' \
         \| sed 's/\\([^!=<]\\)\\([=|]\\)\\([^=>]\\)/\\1 \\2 \\3/g' \
         \| sed 's/  / /g' | sed 's/| |/||/g' \
         \| sed 's/ = = =/===/g' \
         \| sed 's/= = /== /g'"
       else
         "")
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
    val split_time' =
      if Config.get ctxt measure_runtime then split_time else rpair 0
    fun run_on probfile =
      if File.exists command then
        write_tptp_file (debug andalso overlord) full_types explicit_apply
                        probfile clauses
        |> pair (apfst split_time' (bash_output (command_line probfile)))
      else if home = "" then
        error ("The environment variable " ^ quote home_var ^ " is not set.")
      else
        error ("Bad executable: " ^ Path.implode command ^ ".");

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup probfile =
      if the_dest_dir = "" then try File.rm probfile else NONE
    fun export probfile (((output, _), _), _) =
      if the_dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode probfile ^ "_proof"))
                   ((if overlord then
                       "% " ^ command_line probfile ^ "\n% " ^ timestamp () ^
                       "\n"
                     else
                       "") ^ output)

    val (((output, atp_run_time_in_msecs), res_code),
         (pool, conjecture_offset)) =
      with_path cleanup export run_on (prob_pathname subgoal);
    val conjecture_shape = shape_of_clauses (conjecture_offset + 1) goal_clss
    (* Check for success and print out some information on failure. *)
    val (proof, outcome) =
      extract_proof_and_outcome res_code proof_delims known_failures output
    val (message, relevant_thm_names) =
      case outcome of
        NONE =>
        proof_text isar_proof
            (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
            (full_types, minimize_command, proof, internal_thm_names, th,
             subgoal)
      | SOME failure => (string_for_failure failure ^ "\n", [])
  in
    {outcome = outcome, message = message, pool = pool,
     relevant_thm_names = relevant_thm_names,
     atp_run_time_in_msecs = atp_run_time_in_msecs, output = output,
     proof = proof, internal_thm_names = internal_thm_names,
     conjecture_shape = conjecture_shape,
     filtered_clauses = the_filtered_clauses}
  end

fun tptp_prover name p = (name, generic_tptp_prover (name, p));

fun to_generous_secs time = (Time.toMilliseconds time + 999) div 1000

(* E prover *)

val tstp_proof_delims =
  ("# SZS output start CNFRefutation.", "# SZS output end CNFRefutation")

val e_config : prover_config =
  {home_var = "E_HOME",
   executable = "eproof",
   arguments = fn timeout =>
     "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent --cpu-limit=" ^
     string_of_int (to_generous_secs timeout),
   proof_delims = [tstp_proof_delims],
   known_failures =
     [(Unprovable, "SZS status: Satisfiable"),
      (Unprovable, "SZS status Satisfiable"),
      (TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded"),
      (OutOfResources,
       "# Cannot determine problem status within resource limit"),
      (OutOfResources, "SZS status: ResourceOut"),
      (OutOfResources, "SZS status ResourceOut")],
   max_axiom_clauses = 100,
   prefers_theory_relevant = false}
val e = tptp_prover "e" e_config


(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : prover_config =
  {home_var = "SPASS_HOME",
   executable = "SPASS",
   arguments = fn timeout =>
     "-TPTP -Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof \
     \-VarWeight=3 -TimeLimit=" ^ string_of_int (to_generous_secs timeout),
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     [(IncompleteUnprovable, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (OldSpass, "unrecognized option `-TPTP'"),
      (OldSpass, "Unrecognized option TPTP")],
   max_axiom_clauses = 40,
   prefers_theory_relevant = true}
val spass = tptp_prover "spass" spass_config

(* Vampire *)

val vampire_config : prover_config =
  {home_var = "VAMPIRE_HOME",
   executable = "vampire",
   arguments = fn timeout =>
     "--output_syntax tptp --mode casc -t " ^
     string_of_int (to_generous_secs timeout),
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation ======="),
      ("% SZS output start Refutation", "% SZS output end Refutation")],
   known_failures =
     [(Unprovable, "UNPROVABLE"),
      (IncompleteUnprovable, "CANNOT PROVE"),
      (Unprovable, "Satisfiability detected"),
      (OutOfResources, "Refutation not found")],
   max_axiom_clauses = 60,
   prefers_theory_relevant = false}
val vampire = tptp_prover "vampire" vampire_config

(* Remote prover invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([]: string list);

fun get_systems () =
  case bash_output "\"$ISABELLE_ATP_MANAGER/SystemOnTPTP\" -w" of
    (answer, 0) => split_lines answer
  | (answer, _) =>
    error ("Failed to get available systems at SystemOnTPTP:\n" ^ answer)

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ())

fun get_system prefix = Synchronized.change_result systems (fn systems =>
  (if null systems then get_systems () else systems)
  |> `(find_first (String.isPrefix prefix)));

fun the_system prefix =
  (case get_system prefix of
    NONE => error ("System " ^ quote prefix ^ " not available at SystemOnTPTP.")
  | SOME sys => sys);

val remote_known_failures =
  [(TimedOut, "says Timeout"),
   (MalformedOutput, "Remote script could not extract proof")]

fun remote_config atp_prefix args
        ({proof_delims, known_failures, max_axiom_clauses,
          prefers_theory_relevant, ...} : prover_config) : prover_config =
  {home_var = "ISABELLE_ATP_MANAGER",
   executable = "SystemOnTPTP",
   arguments = fn timeout =>
     args ^ " -t " ^ string_of_int (to_generous_secs timeout) ^ " -s " ^
     the_system atp_prefix,
   proof_delims = insert (op =) tstp_proof_delims proof_delims,
   known_failures = remote_known_failures @ known_failures,
   max_axiom_clauses = max_axiom_clauses,
   prefers_theory_relevant = prefers_theory_relevant}

fun remote_tptp_prover prover atp_prefix args config =
  tptp_prover (remotify (fst prover)) (remote_config atp_prefix args config)

val remote_e = remote_tptp_prover e "EP---" "" e_config
val remote_spass = remote_tptp_prover spass "SPASS---" "-x" spass_config
val remote_vampire = remote_tptp_prover vampire "Vampire---9" "" vampire_config

fun maybe_remote (name, _) ({home_var, ...} : prover_config) =
  name |> getenv home_var = "" ? remotify

fun default_atps_param_value () =
  space_implode " " [maybe_remote e e_config, maybe_remote spass spass_config,
                     remotify (fst vampire)]

val provers = [e, spass, vampire, remote_e, remote_spass, remote_vampire]
val prover_setup = fold add_prover provers

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_runtime_setup
  #> prover_setup

end;
