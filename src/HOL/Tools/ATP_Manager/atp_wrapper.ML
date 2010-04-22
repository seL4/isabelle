(*  Title:      HOL/Tools/ATP_Manager/atp_wrapper.ML
    Author:     Fabian Immler, TU Muenchen

Wrapper functions for external ATPs.
*)

signature ATP_WRAPPER =
sig
  type prover = ATP_Manager.prover

  (* hooks for problem files *)
  val destdir : string Config.T
  val problem_prefix : string Config.T
  val measure_runtime : bool Config.T

  val refresh_systems_on_tptp : unit -> unit
  val setup : theory -> theory
end;

structure ATP_Wrapper : ATP_WRAPPER =
struct

open Sledgehammer_Util
open Sledgehammer_Fact_Preprocessor
open Sledgehammer_HOL_Clause
open Sledgehammer_Fact_Filter
open Sledgehammer_Proof_Reconstruct
open ATP_Manager

(** generic ATP wrapper **)

(* external problem files *)

val (destdir, destdir_setup) = Attrib.config_string "atp_destdir" (K "");
  (*Empty string means create files in Isabelle's temporary files directory.*)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "atp_problem_prefix" (K "prob");

val (measure_runtime, measure_runtime_setup) =
  Attrib.config_bool "atp_measure_runtime" (K false);


(* prover configuration *)

type prover_config =
 {command: Path.T,
  arguments: Time.time -> string,
  known_failures: (string list * string) list,
  max_new_clauses: int,
  prefers_theory_relevant: bool,
  supports_isar_proofs: bool};


(* basic template *)

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path);

fun find_known_failure known_failures proof =
  case map_filter (fn (patterns, message) =>
                      if exists (fn pattern => String.isSubstring pattern proof)
                                patterns then
                        SOME message
                      else
                        NONE) known_failures of
    [] => if is_proof_well_formed proof then ""
          else "Error: The ATP output is ill-formed."
  | (message :: _) => message

fun generic_prover overlord get_facts prepare write_file cmd args known_failures
        proof_text name ({debug, full_types, explicit_apply, ...} : params)
        minimize_command
        ({subgoal, goal, relevance_override, axiom_clauses, filtered_clauses}
         : problem) =
  let
    (* get clauses and prepare them for writing *)
    val (ctxt, (chain_ths, th)) = goal;
    val thy = ProofContext.theory_of ctxt;
    val chain_ths = map (Thm.put_name_hint chained_hint) chain_ths;
    val goal_cls = #1 (neg_conjecture_clauses ctxt th subgoal);
    val the_filtered_clauses =
      (case filtered_clauses of
        NONE => get_facts relevance_override goal goal_cls
      | SOME fcls => fcls);
    val the_axiom_clauses =
      (case axiom_clauses of
        NONE => the_filtered_clauses
      | SOME axcls => axcls);
    val (internal_thm_names, clauses) =
      prepare goal_cls chain_ths the_axiom_clauses the_filtered_clauses thy;

    (* path to unique problem file *)
    val destdir' = if overlord then getenv "ISABELLE_HOME_USER"
                   else Config.get ctxt destdir;
    val problem_prefix' = Config.get ctxt problem_prefix;
    fun prob_pathname nr =
      let
        val probfile =
          Path.basic (problem_prefix' ^
                      (if overlord then "_" ^ name else serial_string ())
                      ^ "_" ^ string_of_int nr)
      in
        if destdir' = "" then File.tmp_path probfile
        else if File.exists (Path.explode destdir')
        then Path.append (Path.explode destdir') probfile
        else error ("No such directory: " ^ destdir' ^ ".")
      end;

    (* write out problem file and call prover *)
    fun cmd_line probfile =
      (if Config.get ctxt measure_runtime then
         "TIMEFORMAT='%3U'; { time " ^ space_implode " " [File.shell_path cmd,
         args, File.shell_path probfile] ^ " ; } 2>&1"
       else
         space_implode " " ["exec", File.shell_path cmd, args,
         File.shell_path probfile, "2>&1"]) ^
      (if overlord then
         " | sed 's/,/, /g' | sed 's/\\([=|]\\)/ \\1 /g' | sed 's/! =/ !=/g' \
         \| sed 's/  / /g'"
       else
         "")
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n");
        val (proof, t) = s |> split |> split_last |> apfst cat_lines;
        fun as_num f = f >> (fst o read_int);
        val num = as_num (Scan.many1 Symbol.is_ascii_digit);
        val digit = Scan.one Symbol.is_ascii_digit;
        val num3 = as_num (digit ::: digit ::: (digit >> single));
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b);
        val as_time = the_default 0 o Scan.read Symbol.stopper time o explode;
      in (proof, as_time t) end;
    fun split_time' s =
      if Config.get ctxt measure_runtime then split_time s else (s, 0)
    fun run_on probfile =
      if File.exists cmd then
        write_file full_types explicit_apply probfile clauses
        |> pair (apfst split_time' (bash_output (cmd_line probfile)))
      else error ("Bad executable: " ^ Path.implode cmd ^ ".");

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup probfile = if destdir' = "" then try File.rm probfile else NONE;
    fun export probfile (((proof, _), _), _) =
      if destdir' = "" then
        ()
      else
        File.write (Path.explode (Path.implode probfile ^ "_proof"))
                   ((if overlord then
                       "% " ^ cmd_line probfile ^ "\n% " ^ timestamp () ^ "\n"
                     else
                        "") ^ proof)

    val (((proof, atp_run_time_in_msecs), rc), _) =
      with_path cleanup export run_on (prob_pathname subgoal);

    (* Check for success and print out some information on failure. *)
    val failure = find_known_failure known_failures proof;
    val success = rc = 0 andalso failure = "";
    val (message, relevant_thm_names) =
      if success then
        proof_text ctxt minimize_command proof internal_thm_names th subgoal
      else if failure <> "" then
        (failure ^ "\n", [])
      else
        ("Unknown ATP error: " ^ proof ^ ".\n", [])
  in
    {success = success, message = message,
     relevant_thm_names = relevant_thm_names,
     atp_run_time_in_msecs = atp_run_time_in_msecs, proof = proof,
     internal_thm_names = internal_thm_names,
     filtered_clauses = the_filtered_clauses}
  end;


(* generic TPTP-based provers *)

fun generic_tptp_prover
        (name, {command, arguments, known_failures, max_new_clauses,
                prefers_theory_relevant, supports_isar_proofs})
        (params as {debug, overlord, respect_no_atp, relevance_threshold,
                    convergence, theory_relevant, higher_order, follow_defs,
                    isar_proof, modulus, sorts, ...})
        minimize_command timeout =
  generic_prover overlord
      (get_relevant_facts respect_no_atp relevance_threshold convergence
                          higher_order follow_defs max_new_clauses
                          (the_default prefers_theory_relevant theory_relevant))
      (prepare_clauses higher_order false)
      (write_tptp_file (debug andalso overlord andalso not isar_proof)) command
      (arguments timeout) known_failures
      (proof_text (supports_isar_proofs andalso isar_proof) debug modulus sorts)
      name params minimize_command

fun tptp_prover name p = (name, generic_tptp_prover (name, p));


(** common provers **)

fun generous_to_secs time = (Time.toMilliseconds time + 999) div 1000

(* Vampire *)

(* NB: Vampire does not work without explicit time limit. *)

val vampire_config : prover_config =
  {command = Path.explode "$VAMPIRE_HOME/vampire",
   arguments = (fn timeout => "--output_syntax tptp --mode casc -t " ^
                              string_of_int (generous_to_secs timeout)),
   known_failures =
     [(["Satisfiability detected", "CANNOT PROVE"],
       "The ATP problem is unprovable."),
      (["Refutation not found"],
       "The ATP failed to determine the problem's status.")],
   max_new_clauses = 60,
   prefers_theory_relevant = false,
   supports_isar_proofs = true}
val vampire = tptp_prover "vampire" vampire_config


(* E prover *)

val e_config : prover_config =
  {command = Path.explode "$E_HOME/eproof",
   arguments = (fn timeout => "--tstp-in --tstp-out -l5 -xAutoDev \
                              \-tAutoDev --silent --cpu-limit=" ^
                              string_of_int (generous_to_secs timeout)),
   known_failures =
       [(["SZS status: Satisfiable", "SZS status Satisfiable"],
         "The ATP problem is unprovable."),
        (["SZS status: ResourceOut", "SZS status ResourceOut"],
         "The ATP ran out of resources."),
        (["# Cannot determine problem status"],
         "The ATP failed to determine the problem's status.")],
   max_new_clauses = 100,
   prefers_theory_relevant = false,
   supports_isar_proofs = true}
val e = tptp_prover "e" e_config


(* SPASS *)

fun generic_dfg_prover
        (name, ({command, arguments, known_failures, max_new_clauses,
                 prefers_theory_relevant, ...} : prover_config))
        (params as {overlord, respect_no_atp, relevance_threshold, convergence,
                    theory_relevant, higher_order, follow_defs, ...})
        minimize_command timeout =
  generic_prover overlord
      (get_relevant_facts respect_no_atp relevance_threshold convergence
                          higher_order follow_defs max_new_clauses
                          (the_default prefers_theory_relevant theory_relevant))
      (prepare_clauses higher_order true) write_dfg_file command
      (arguments timeout) known_failures (K metis_proof_text)
      name params minimize_command

fun dfg_prover name p = (name, generic_dfg_prover (name, p))

(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : prover_config =
 {command = Path.explode "$SPASS_HOME/SPASS",
  arguments = (fn timeout => "-Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0" ^
    " -FullRed=0 -DocProof -VarWeight=3 -TimeLimit=" ^
    string_of_int (generous_to_secs timeout)),
  known_failures =
    [(["SPASS beiseite: Completion found."], "The ATP problem is unprovable."),
     (["SPASS beiseite: Ran out of time."], "The ATP timed out."),
     (["SPASS beiseite: Maximal number of loops exceeded."],
      "The ATP hit its loop limit.")],
  max_new_clauses = 40,
  prefers_theory_relevant = true,
  supports_isar_proofs = false}
val spass = dfg_prover "spass" spass_config

(* SPASS 3.7 supports both the DFG and the TPTP syntax, whereas SPASS 3.0
   supports only the DFG syntax. As soon as all Isabelle repository/snapshot
   users have upgraded to 3.7, we can kill "spass" (and all DFG support in
   Sledgehammer) and rename "spass_tptp" "spass". *)

(* FIXME: Change the error message below to point to the Isabelle download
   page once the package is there (around the Isabelle2010 release). *)

val spass_tptp_config =
  {command = #command spass_config,
   arguments = prefix "-TPTP " o #arguments spass_config,
   known_failures =
     #known_failures spass_config @
     [(["unrecognized option `-TPTP'", "Unrecognized option TPTP"],
       "Warning: Sledgehammer requires a more recent version of SPASS with \
       \support for the TPTP syntax. To install it, download and untar the \
       \package \"http://isabelle.in.tum.de/~blanchet/spass-3.7.tgz\" and add \
       \the \"spass-3.7\" directory's full path to \"" ^
       Path.implode (Path.expand (Path.appends
           (Path.variable "ISABELLE_HOME_USER" ::
            map Path.basic ["etc", "components"]))) ^
       "\" on a line of its own.")],
   max_new_clauses = #max_new_clauses spass_config,
   prefers_theory_relevant = #prefers_theory_relevant spass_config,
   supports_isar_proofs = #supports_isar_proofs spass_config}
val spass_tptp = tptp_prover "spass_tptp" spass_tptp_config

(* remote prover invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_wrapper_systems" ([]: string list);

fun get_systems () =
  let
    val (answer, rc) = bash_output "\"$ISABELLE_ATP_MANAGER/SystemOnTPTP\" -w"
  in
    if rc <> 0 then
      error ("Failed to get available systems at SystemOnTPTP:\n" ^ answer)
    else
      split_lines answer
  end;

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ());

fun get_system prefix = Synchronized.change_result systems (fn systems =>
  (if null systems then get_systems () else systems)
  |> `(find_first (String.isPrefix prefix)));

fun the_system prefix =
  (case get_system prefix of
    NONE => error ("System " ^ quote prefix ^ " not available at SystemOnTPTP")
  | SOME sys => sys);

val remote_known_failures =
  [(["Remote-script could not extract proof"],
    "Error: The remote ATP proof is ill-formed.")]

fun remote_prover_config prover_prefix args
        ({known_failures, max_new_clauses, prefers_theory_relevant, ...}
         : prover_config) : prover_config =
  {command = Path.explode "$ISABELLE_ATP_MANAGER/SystemOnTPTP",
   arguments = (fn timeout =>
     args ^ " -t " ^ string_of_int (generous_to_secs timeout) ^ " -s " ^
     the_system prover_prefix),
   known_failures = remote_known_failures @ known_failures,
   max_new_clauses = max_new_clauses,
   prefers_theory_relevant = prefers_theory_relevant,
   supports_isar_proofs = false}

val remote_vampire =
  tptp_prover "remote_vampire"
              (remote_prover_config "Vampire---9" "" vampire_config)

val remote_e =
  tptp_prover "remote_e" (remote_prover_config "EP---" "" e_config)

val remote_spass =
  tptp_prover "remote_spass" (remote_prover_config "SPASS---" "-x" spass_config)

val provers = [spass, spass_tptp, vampire, e, remote_vampire, remote_spass,
               remote_e]
val prover_setup = fold add_prover provers

val setup =
  destdir_setup
  #> problem_prefix_setup
  #> measure_runtime_setup
  #> prover_setup;

end;
