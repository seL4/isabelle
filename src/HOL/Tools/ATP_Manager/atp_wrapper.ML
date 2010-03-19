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

open Sledgehammer_HOL_Clause
open Sledgehammer_Fact_Filter
open Sledgehammer_Proof_Reconstruct
open ATP_Manager

(** generic ATP wrapper **)

(* external problem files *)

val (destdir, destdir_setup) = Attrib.config_string "atp_destdir" "";
  (*Empty string means create files in Isabelle's temporary files directory.*)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "atp_problem_prefix" "prob";

val (measure_runtime, measure_runtime_setup) =
  Attrib.config_bool "atp_measure_runtime" false;


(* prover configuration *)

type prover_config =
 {command: Path.T,
  arguments: int -> string,
  failure_strs: string list,
  max_new_clauses: int,
  insert_theory_const: bool,
  emit_structured_proof: bool};


(* basic template *)

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path);

fun find_failure strs proof =
  case filter (fn s => String.isSubstring s proof) strs of
    [] => if is_proof_well_formed proof then NONE
          else SOME "Ill-formed ATP output"
  | (failure :: _) => SOME failure

fun external_prover relevance_filter prepare write cmd args failure_strs
        produce_answer name ({with_full_types, subgoal, goal, axiom_clauses,
                              filtered_clauses}: problem) =
  let
    (* get clauses and prepare them for writing *)
    val (ctxt, (chain_ths, th)) = goal;
    val thy = ProofContext.theory_of ctxt;
    val chain_ths = map (Thm.put_name_hint chained_hint) chain_ths;
    val goal_cls = #1 (Sledgehammer_Fact_Preprocessor.neg_conjecture_clauses ctxt th subgoal);
    val the_filtered_clauses =
      (case filtered_clauses of
        NONE => relevance_filter goal goal_cls
      | SOME fcls => fcls);
    val the_axiom_clauses =
      (case axiom_clauses of
        NONE => the_filtered_clauses
      | SOME axcls => axcls);
    val (thm_names, clauses) =
      prepare goal_cls chain_ths the_axiom_clauses the_filtered_clauses thy;

    (* path to unique problem file *)
    val destdir' = Config.get ctxt destdir;
    val problem_prefix' = Config.get ctxt problem_prefix;
    fun prob_pathname nr =
      let val probfile =
        Path.basic (problem_prefix' ^ serial_string () ^ "_" ^ string_of_int nr)
      in
        if destdir' = "" then File.tmp_path probfile
        else if File.exists (Path.explode destdir')
        then Path.append  (Path.explode destdir') probfile
        else error ("No such directory: " ^ destdir')
      end;

    (* write out problem file and call prover *)
    fun cmd_line probfile =
      if Config.get ctxt measure_runtime
      then (* Warning: suppresses error messages of ATPs *)
        "TIMEFORMAT='%3U'; { time " ^ space_implode " " [File.shell_path cmd,
        args, File.shell_path probfile] ^ " 2> /dev/null" ^ " ; } 2>&1"
      else
        space_implode " " ["exec", File.shell_path cmd, args,
        File.shell_path probfile];
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
        write with_full_types probfile clauses
        |> pair (apfst split_time' (bash_output (cmd_line probfile)))
      else error ("Bad executable: " ^ Path.implode cmd);

    (* if problemfile has not been exported, delete problemfile; otherwise export proof, too *)
    fun cleanup probfile = if destdir' = "" then try File.rm probfile else NONE;
    fun export probfile (((proof, _), _), _) =
      if destdir' = "" then ()
      else File.write (Path.explode (Path.implode probfile ^ "_proof")) proof;

    val (((proof, time), rc), conj_pos) =
      with_path cleanup export run_on (prob_pathname subgoal);

    (* check for success and print out some information on failure *)
    val failure = find_failure failure_strs proof;
    val success = rc = 0 andalso is_none failure;
    val (message, real_thm_names) =
      if is_some failure then ("External prover failed.", [])
      else if rc <> 0 then ("External prover failed: " ^ proof, [])
      else apfst (fn s => "Try this command: " ^ s)
        (produce_answer name (proof, thm_names, conj_pos, ctxt, th, subgoal));
  in
    {success = success, message = message,
      theorem_names = real_thm_names, runtime = time, proof = proof,
      internal_thm_names = thm_names, filtered_clauses = the_filtered_clauses}
  end;


(* generic TPTP-based provers *)

fun generic_tptp_prover
        (name, {command, arguments, failure_strs, max_new_clauses,
                insert_theory_const, emit_structured_proof}) timeout =
  external_prover (get_relevant_facts max_new_clauses insert_theory_const)
      (prepare_clauses false) write_tptp_file command (arguments timeout)
      failure_strs
      (if emit_structured_proof then structured_isar_proof
       else metis_lemma_list false) name;

fun tptp_prover (name, p) = (name, generic_tptp_prover (name, p));


(** common provers **)

(* Vampire *)

(*NB: Vampire does not work without explicit timelimit*)

val vampire_failure_strs =
  ["Satisfiability detected", "Refutation not found", "CANNOT PROVE"];
val vampire_max_new_clauses = 60;
val vampire_insert_theory_const = false;

fun vampire_prover_config full : prover_config =
 {command = Path.explode "$VAMPIRE_HOME/vampire",
  arguments = (fn timeout => "--output_syntax tptp --mode casc" ^
    " -t " ^ string_of_int timeout),
  failure_strs = vampire_failure_strs,
  max_new_clauses = vampire_max_new_clauses,
  insert_theory_const = vampire_insert_theory_const,
  emit_structured_proof = full};

val vampire = tptp_prover ("vampire", vampire_prover_config false);
val vampire_isar = tptp_prover ("vampire_isar", vampire_prover_config true);


(* E prover *)

val eprover_failure_strs =
  ["SZS status: Satisfiable", "SZS status Satisfiable",
   "SZS status: ResourceOut", "SZS status ResourceOut",
   "# Cannot determine problem status"];
val eprover_max_new_clauses = 100;
val eprover_insert_theory_const = false;

fun eprover_config full : prover_config =
 {command = Path.explode "$E_HOME/eproof",
  arguments = (fn timeout => "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev" ^
    " --silent --cpu-limit=" ^ string_of_int timeout),
  failure_strs = eprover_failure_strs,
  max_new_clauses = eprover_max_new_clauses,
  insert_theory_const = eprover_insert_theory_const,
  emit_structured_proof = full};

val eprover = tptp_prover ("e", eprover_config false);
val eprover_isar = tptp_prover ("e_isar", eprover_config true);


(* SPASS *)

val spass_failure_strs =
  ["SPASS beiseite: Completion found.", "SPASS beiseite: Ran out of time.",
   "SPASS beiseite: Maximal number of loops exceeded."];
val spass_max_new_clauses = 40;
val spass_insert_theory_const = true;

fun spass_config insert_theory_const: prover_config =
 {command = Path.explode "$SPASS_HOME/SPASS",
  arguments = (fn timeout => "-Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0" ^
    " -FullRed=0 -DocProof -TimeLimit=" ^ string_of_int timeout),
  failure_strs = spass_failure_strs,
  max_new_clauses = spass_max_new_clauses,
  insert_theory_const = insert_theory_const,
  emit_structured_proof = false};

fun generic_dfg_prover
        (name, ({command, arguments, failure_strs, max_new_clauses,
                 insert_theory_const, ...} : prover_config)) timeout =
  external_prover
    (get_relevant_facts max_new_clauses insert_theory_const)
    (prepare_clauses true)
    write_dfg_file
    command
    (arguments timeout)
    failure_strs
    (metis_lemma_list true)
    name;

fun dfg_prover (name, p) = (name, generic_dfg_prover (name, p));

val spass = dfg_prover ("spass", spass_config spass_insert_theory_const);
val spass_no_tc = dfg_prover ("spass_no_tc", spass_config false);


(* remote prover invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_wrapper_systems" ([]: string list);

fun get_systems () =
  let
    val (answer, rc) = bash_output ("\"$ISABELLE_ATP_MANAGER/SystemOnTPTP\" -w")
  in
    if rc <> 0 then error ("Failed to get available systems at SystemOnTPTP:\n" ^ answer)
    else split_lines answer
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

val remote_failure_strs = ["Remote-script could not extract proof"];

fun remote_prover_config prover_prefix args max_new insert_tc: prover_config =
 {command = Path.explode "$ISABELLE_ATP_MANAGER/SystemOnTPTP",
  arguments = (fn timeout =>
    args ^ " -t " ^ string_of_int timeout ^ " -s " ^ the_system prover_prefix),
  failure_strs = remote_failure_strs,
  max_new_clauses = max_new,
  insert_theory_const = insert_tc,
  emit_structured_proof = false};

val remote_vampire = tptp_prover ("remote_vampire", remote_prover_config
  "Vampire---9" "" vampire_max_new_clauses vampire_insert_theory_const);

val remote_eprover = tptp_prover ("remote_e", remote_prover_config
  "EP---" "" eprover_max_new_clauses eprover_insert_theory_const);

val remote_spass = tptp_prover ("remote_spass", remote_prover_config
  "SPASS---" "-x" spass_max_new_clauses spass_insert_theory_const);

val provers =
  [spass, vampire, eprover, vampire_isar, eprover_isar, spass_no_tc,
   remote_vampire, remote_spass, remote_eprover]
val prover_setup = fold add_prover provers

val setup =
  destdir_setup
  #> problem_prefix_setup
  #> measure_runtime_setup
  #> prover_setup;

end;
