(*  Title:      HOL/Tools/ATP_Manager/atp_wrapper.ML
    Author:     Fabian Immler, TU Muenchen

Wrapper functions for external ATPs.
*)

signature ATP_WRAPPER =
sig
  val destdir: string ref
  val problem_name: string ref
  val tptp_prover_opts_full: int -> bool -> bool -> Path.T * string -> AtpManager.prover
  val tptp_prover_opts: int -> bool -> Path.T * string -> AtpManager.prover
  val tptp_prover: Path.T * string -> AtpManager.prover
  val full_prover_opts: int -> bool -> Path.T * string -> AtpManager.prover
  val full_prover: Path.T * string  -> AtpManager.prover
  val vampire_opts: int -> bool -> AtpManager.prover
  val vampire: AtpManager.prover
  val vampire_opts_full: int -> bool -> AtpManager.prover
  val vampire_full: AtpManager.prover
  val eprover_opts: int -> bool  -> AtpManager.prover
  val eprover: AtpManager.prover
  val eprover_opts_full: int -> bool -> AtpManager.prover
  val eprover_full: AtpManager.prover
  val spass_opts: int -> bool  -> AtpManager.prover
  val spass: AtpManager.prover
  val remote_prover_opts: int -> bool -> string -> string -> AtpManager.prover
  val remote_prover: string -> string -> AtpManager.prover
  val refresh_systems: unit -> unit
end;

structure AtpWrapper: ATP_WRAPPER =
struct

(** generic ATP wrapper **)

(* global hooks for writing problemfiles *)

val destdir = ref "";   (*Empty means write files to /tmp*)
val problem_name = ref "prob";


(* basic template *)

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path)

fun external_prover relevance_filter preparer writer (cmd, args) find_failure produce_answer
  timeout axiom_clauses filtered_clauses name subgoalno goal =
  let
    (* path to unique problem file *)
    val destdir' = ! destdir
    val problem_name' = ! problem_name
    fun prob_pathname nr =
      let val probfile = Path.basic (problem_name' ^ serial_string () ^ "_" ^ string_of_int nr)
      in if destdir' = "" then File.tmp_path probfile
        else if File.exists (Path.explode (destdir'))
        then Path.append  (Path.explode (destdir')) probfile
        else error ("No such directory: " ^ destdir')
      end

    (* get clauses and prepare them for writing *)
    val (ctxt, (chain_ths, th)) = goal
    val thy = ProofContext.theory_of ctxt
    val chain_ths = map (Thm.put_name_hint ResReconstruct.chained_hint) chain_ths
    val goal_cls = #1 (ResAxioms.neg_conjecture_clauses ctxt th subgoalno)
    val _ = app (fn th => Output.debug (fn _ => Display.string_of_thm ctxt th)) goal_cls
    val the_filtered_clauses =
      case filtered_clauses of
          NONE => relevance_filter goal goal_cls
        | SOME fcls => fcls
    val the_axiom_clauses =
      case axiom_clauses of
          NONE => the_filtered_clauses
        | SOME axcls => axcls
    val (thm_names, clauses) =
      preparer goal_cls chain_ths the_axiom_clauses the_filtered_clauses thy

    (* write out problem file and call prover *)
    fun cmd_line probfile = "TIMEFORMAT='%3U'; ((time " ^ space_implode " "
      [File.shell_path cmd, args, File.platform_path probfile] ^ ") 2>&1)"
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n")
        val (proof, t) = s |> split |> split_last |> apfst cat_lines
        val num = Scan.many1 Symbol.is_ascii_digit >> (fst o read_int)
        val time = num --| Scan.$$ "." -- num >> (fn (a, b) => a * 1000 + b)
        val as_time = the_default 0 o Scan.read Symbol.stopper time o explode
      in (proof, as_time t) end
    fun run_on probfile =
      if File.exists cmd
      then
        writer probfile clauses
        |> pair (apfst split_time (system_out (cmd_line probfile)))
      else error ("Bad executable: " ^ Path.implode cmd)

    (* if problemfile has not been exported, delete problemfile; otherwise export proof, too *)
    fun cleanup probfile = if destdir' = "" then File.rm probfile else ()
    fun export probfile (((proof, _), _), _) = if destdir' = "" then ()
      else File.write (Path.explode (Path.implode probfile ^ "_proof")) proof

    val (((proof, time), rc), conj_pos) = with_path cleanup export run_on
      (prob_pathname subgoalno)

    (* check for success and print out some information on failure *)
    val failure = find_failure proof
    val success = rc = 0 andalso is_none failure
    val message =
      if is_some failure then ("External prover failed.", [])
      else if rc <> 0 then ("External prover failed: " ^ proof, [])
      else apfst (fn s => "Try this command: " ^ s)
        (produce_answer name (proof, thm_names, conj_pos, ctxt, th, subgoalno))
    val _ = Output.debug (fn () => "Sledgehammer response (rc = " ^ string_of_int rc ^ "):\n" ^ proof)
  in (success, message, time, proof, thm_names, the_filtered_clauses) end;



(** common provers **)

(* generic TPTP-based provers *)

fun tptp_prover_opts_full max_new theory_const full command timeout ax_clauses fcls name n goal =
  external_prover
  (ResAtp.get_relevant max_new theory_const)
  (ResAtp.prepare_clauses false)
  (ResHolClause.tptp_write_file (AtpManager.get_full_types()))
  command
  ResReconstruct.find_failure
  (if full then ResReconstruct.structured_proof else ResReconstruct.lemma_list false)
  timeout ax_clauses fcls name n goal;

(*arbitrary ATP with TPTP input/output and problemfile as last argument*)
fun tptp_prover_opts max_new theory_const =
  tptp_prover_opts_full max_new theory_const false;

fun tptp_prover x = tptp_prover_opts 60 true x;

(*for structured proofs: prover must support TSTP*)
fun full_prover_opts max_new theory_const =
  tptp_prover_opts_full max_new theory_const true;

fun full_prover x = full_prover_opts 60 true x;


(* Vampire *)

(*NB: Vampire does not work without explicit timelimit*)

fun vampire_opts max_new theory_const timeout = tptp_prover_opts
  max_new theory_const
  (Path.explode "$VAMPIRE_HOME/vampire",
    ("--output_syntax tptp --mode casc -t " ^ string_of_int timeout))
  timeout;

val vampire = vampire_opts 60 false;

fun vampire_opts_full max_new theory_const timeout = full_prover_opts
  max_new theory_const
  (Path.explode "$VAMPIRE_HOME/vampire",
    ("--output_syntax tptp --mode casc -t " ^ string_of_int timeout))
  timeout;

val vampire_full = vampire_opts_full 60 false;


(* E prover *)

fun eprover_opts max_new theory_const timeout = tptp_prover_opts
  max_new theory_const
  (Path.explode "$E_HOME/eproof",
    "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent --cpu-limit=" ^ string_of_int timeout)
  timeout;

val eprover = eprover_opts 100 false;

fun eprover_opts_full max_new theory_const timeout = full_prover_opts
  max_new theory_const
  (Path.explode "$E_HOME/eproof",
    "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent --cpu-limit=" ^ string_of_int timeout)
  timeout;

val eprover_full = eprover_opts_full 100 false;


(* SPASS *)

fun spass_opts max_new theory_const timeout ax_clauses fcls name n goal = external_prover
  (ResAtp.get_relevant max_new theory_const)
  (ResAtp.prepare_clauses true)
  (ResHolClause.dfg_write_file (AtpManager.get_full_types()))
  (Path.explode "$SPASS_HOME/SPASS",
    "-Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof -TimeLimit=" ^
      string_of_int timeout)
  ResReconstruct.find_failure
  (ResReconstruct.lemma_list true)
  timeout ax_clauses fcls name n goal;

val spass = spass_opts 40 true;


(* remote prover invocation via SystemOnTPTP *)

val systems =
  Synchronized.var "atp_wrapper_systems" ([]: string list);

fun get_systems () =
  let
    val (answer, rc) = system_out ("\"$ISABELLE_ATP_MANAGER/SystemOnTPTP\" -w")
  in
    if rc <> 0 then error ("Failed to get available systems from SystemOnTPTP:\n" ^ answer)
    else split_lines answer
  end;

fun refresh_systems () = Synchronized.change systems (fn _ =>
  get_systems ());

fun get_system prefix = Synchronized.change_result systems (fn systems =>
  let val systems = if null systems then get_systems() else systems
  in (find_first (String.isPrefix prefix) systems, systems) end);

fun remote_prover_opts max_new theory_const args prover_prefix timeout =
  let val sys =
    case get_system prover_prefix of
      NONE => error ("No system like " ^ quote prover_prefix ^ " at SystemOnTPTP")
    | SOME sys => sys
  in tptp_prover_opts max_new theory_const
    (Path.explode "$ISABELLE_ATP_MANAGER/SystemOnTPTP",
      args ^ " -t " ^ string_of_int timeout ^ " -s " ^ sys) timeout
  end;

val remote_prover = remote_prover_opts 60 false;

end;

