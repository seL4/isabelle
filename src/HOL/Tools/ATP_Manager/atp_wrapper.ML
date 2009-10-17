(*  Title:      HOL/Tools/ATP_Manager/atp_wrapper.ML
    Author:     Fabian Immler, TU Muenchen

Wrapper functions for external ATPs.
*)

signature ATP_WRAPPER =
sig
  (*hooks for problem files*)
  val destdir: string Config.T
  val problem_prefix: string Config.T
  val setup: theory -> theory

  (*prover configuration, problem format, and prover result*)
  type prover_config =
   {command: Path.T,
    arguments: int -> string,
    max_new_clauses: int,
    insert_theory_const: bool,
    emit_structured_proof: bool}
  type problem =
   {with_full_types: bool,
    subgoal: int,
    goal: Proof.context * (thm list * thm),
    axiom_clauses: (thm * (string * int)) list option,
    filtered_clauses: (thm * (string * int)) list option}
  val problem_of_goal: bool -> int -> Proof.context * (thm list * thm) -> problem
  type prover_result =
   {success: bool,
    message: string,
    theorem_names: string list,
    runtime: int,
    proof: string,
    internal_thm_names: string Vector.vector,
    filtered_clauses: (thm * (string * int)) list}
  type prover = int -> problem -> prover_result

  (*common provers*)
  val vampire: string * prover
  val vampire_full: string * prover
  val eprover: string * prover
  val eprover_full: string * prover
  val spass: string * prover
  val spass_no_tc: string * prover
  val remote_vampire: string * prover
  val remote_eprover: string * prover
  val remote_spass: string * prover
  val refresh_systems: unit -> unit
end;

structure ATP_Wrapper: ATP_WRAPPER =
struct

(** generic ATP wrapper **)

(* external problem files *)

val (destdir, destdir_setup) = Attrib.config_string "atp_destdir" "";
  (*Empty string means create files in Isabelle's temporary files directory.*)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "atp_problem_prefix" "prob";

val setup = destdir_setup #> problem_prefix_setup;


(* prover configuration, problem format, and prover result *)

type prover_config =
 {command: Path.T,
  arguments: int -> string,
  max_new_clauses: int,
  insert_theory_const: bool,
  emit_structured_proof: bool};

type problem =
 {with_full_types: bool,
  subgoal: int,
  goal: Proof.context * (thm list * thm),
  axiom_clauses: (thm * (string * int)) list option,
  filtered_clauses: (thm * (string * int)) list option};

fun problem_of_goal with_full_types subgoal goal : problem =
 {with_full_types = with_full_types,
  subgoal = subgoal,
  goal = goal,
  axiom_clauses = NONE,
  filtered_clauses = NONE};

type prover_result =
 {success: bool,
  message: string,
  theorem_names: string list,  (*relevant theorems*)
  runtime: int,  (*user time of the ATP, in milliseconds*)
  proof: string,
  internal_thm_names: string Vector.vector,
  filtered_clauses: (thm * (string * int)) list};

type prover = int -> problem -> prover_result;


(* basic template *)

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path);

fun external_prover relevance_filter prepare write cmd args find_failure produce_answer
    axiom_clauses filtered_clauses name subgoalno goal =
  let
    (* get clauses and prepare them for writing *)
    val (ctxt, (chain_ths, th)) = goal;
    val thy = ProofContext.theory_of ctxt;
    val chain_ths = map (Thm.put_name_hint ResReconstruct.chained_hint) chain_ths;
    val goal_cls = #1 (ResAxioms.neg_conjecture_clauses ctxt th subgoalno);
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
        else if File.exists (Path.explode (destdir'))
        then Path.append  (Path.explode (destdir')) probfile
        else error ("No such directory: " ^ destdir')
      end;

    (* write out problem file and call prover *)
    fun cmd_line probfile = "TIMEFORMAT='%3U'; { time " ^ space_implode " "
      [File.shell_path cmd, args, File.shell_path probfile] ^ " ; } 2>&1"
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
    fun run_on probfile =
      if File.exists cmd then
        write probfile clauses
        |> pair (apfst split_time (system_out (cmd_line probfile)))
      else error ("Bad executable: " ^ Path.implode cmd);

    (* if problemfile has not been exported, delete problemfile; otherwise export proof, too *)
    fun cleanup probfile = if destdir' = "" then try File.rm probfile else NONE;
    fun export probfile (((proof, _), _), _) =
      if destdir' = "" then ()
      else File.write (Path.explode (Path.implode probfile ^ "_proof")) proof;

    val (((proof, time), rc), conj_pos) =
      with_path cleanup export run_on (prob_pathname subgoalno);

    (* check for success and print out some information on failure *)
    val failure = find_failure proof;
    val success = rc = 0 andalso is_none failure;
    val (message, real_thm_names) =
      if is_some failure then ("External prover failed.", [])
      else if rc <> 0 then ("External prover failed: " ^ proof, [])
      else apfst (fn s => "Try this command: " ^ s)
        (produce_answer name (proof, thm_names, conj_pos, ctxt, th, subgoalno));
  in
    {success = success, message = message,
      theorem_names = real_thm_names, runtime = time, proof = proof,
      internal_thm_names = thm_names, filtered_clauses = the_filtered_clauses}
  end;


(* generic TPTP-based provers *)

fun gen_tptp_prover (name, prover_config) timeout problem =
  let
    val {max_new_clauses, insert_theory_const, emit_structured_proof, command, arguments} =
      prover_config;
    val {with_full_types, subgoal, goal, axiom_clauses, filtered_clauses} = problem;
  in
    external_prover
      (ResAtp.get_relevant max_new_clauses insert_theory_const)
      (ResAtp.prepare_clauses false)
      (ResHolClause.tptp_write_file with_full_types)
      command
      (arguments timeout)
      ResReconstruct.find_failure
      (if emit_structured_proof then ResReconstruct.structured_proof
       else ResReconstruct.lemma_list false)
      axiom_clauses
      filtered_clauses
      name
      subgoal
      goal
  end;

fun tptp_prover (name, config) = (name, gen_tptp_prover (name, config));



(** common provers **)

(* Vampire *)

(*NB: Vampire does not work without explicit timelimit*)

val vampire_max_new_clauses = 60;
val vampire_insert_theory_const = false;

fun vampire_prover_config full : prover_config =
 {command = Path.explode "$VAMPIRE_HOME/vampire",
  arguments = (fn timeout => "--output_syntax tptp --mode casc" ^
    " -t " ^ string_of_int timeout),
  max_new_clauses = vampire_max_new_clauses,
  insert_theory_const = vampire_insert_theory_const,
  emit_structured_proof = full};

val vampire = tptp_prover ("vampire", vampire_prover_config false);
val vampire_full = tptp_prover ("vampire_full", vampire_prover_config true);


(* E prover *)

val eprover_max_new_clauses = 100;
val eprover_insert_theory_const = false;

fun eprover_config full : prover_config =
 {command = Path.explode "$E_HOME/eproof",
  arguments = (fn timeout => "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev" ^
    " --silent --cpu-limit=" ^ string_of_int timeout),
  max_new_clauses = eprover_max_new_clauses,
  insert_theory_const = eprover_insert_theory_const,
  emit_structured_proof = full};

val eprover = tptp_prover ("e", eprover_config false);
val eprover_full = tptp_prover ("e_full", eprover_config true);


(* SPASS *)

val spass_max_new_clauses = 40;
val spass_insert_theory_const = true;

fun spass_config insert_theory_const: prover_config =
 {command = Path.explode "$SPASS_HOME/SPASS",
  arguments = (fn timeout => "-Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0" ^
    " -FullRed=0 -DocProof -TimeLimit=" ^ string_of_int timeout),
  max_new_clauses = spass_max_new_clauses,
  insert_theory_const = insert_theory_const,
  emit_structured_proof = false};

fun gen_dfg_prover (name, prover_config: prover_config) timeout problem =
  let
    val {max_new_clauses, insert_theory_const, command, arguments, ...} = prover_config
    val {with_full_types, subgoal, goal, axiom_clauses, filtered_clauses} = problem
  in
    external_prover
      (ResAtp.get_relevant max_new_clauses insert_theory_const)
      (ResAtp.prepare_clauses true)
      (ResHolClause.dfg_write_file with_full_types)
      command
      (arguments timeout)
      ResReconstruct.find_failure
      (ResReconstruct.lemma_list true)
      axiom_clauses
      filtered_clauses
      name
      subgoal
      goal
  end;

fun dfg_prover (name, config) = (name, gen_dfg_prover (name, config));

val spass = dfg_prover ("spass", spass_config spass_insert_theory_const);
val spass_no_tc = dfg_prover ("spass_no_tc", spass_config false);


(* remote prover invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_wrapper_systems" ([]: string list);

fun get_systems () =
  let
    val (answer, rc) = system_out ("\"$ISABELLE_ATP_MANAGER/SystemOnTPTP\" -w")
  in
    if rc <> 0 then error ("Failed to get available systems from SystemOnTPTP:\n" ^ answer)
    else split_lines answer
  end;

fun refresh_systems () = Synchronized.change systems (fn _ => get_systems ());

fun get_system prefix = Synchronized.change_result systems (fn systems =>
  (if null systems then get_systems () else systems)
  |> `(find_first (String.isPrefix prefix)));

fun the_system prefix =
  (case get_system prefix of
    NONE => error ("No system like " ^ quote prefix ^ " at SystemOnTPTP")
  | SOME sys => sys);

fun remote_prover_config prover_prefix args max_new insert_tc: prover_config =
 {command = Path.explode "$ISABELLE_ATP_MANAGER/SystemOnTPTP",
  arguments =
    (fn timeout => args ^ " -t " ^ string_of_int timeout ^ " -s " ^ the_system prover_prefix),
  max_new_clauses = max_new,
  insert_theory_const = insert_tc,
  emit_structured_proof = false};

val remote_vampire = tptp_prover ("remote_vampire", remote_prover_config
  "Vampire---9" "" vampire_max_new_clauses vampire_insert_theory_const);

val remote_eprover = tptp_prover ("remote_e", remote_prover_config
  "EP---" "" eprover_max_new_clauses eprover_insert_theory_const);

val remote_spass = tptp_prover ("remote_spass", remote_prover_config
  "SPASS---" "-x" spass_max_new_clauses spass_insert_theory_const);

end;
