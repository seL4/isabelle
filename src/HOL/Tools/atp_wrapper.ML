(*  Title:      HOL/Tools/atp_wrapper.ML
    ID:         $Id$
    Author:     Fabian Immler, TU Muenchen

Wrapper functions for external ATPs.
*)

signature ATP_WRAPPER =
sig
  val destdir: string ref
  val problem_name: string ref
  val external_prover:
    ((int -> Path.T) -> Proof.context * thm list * thm -> string list * ResHolClause.axiom_name Vector.vector list) ->
    Path.T * string ->
    (string -> string option) ->
    (string * string vector * Proof.context * thm * int -> string) ->
    AtpManager.prover
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
  val remote_prover_opts: int -> bool -> string -> AtpManager.prover
  val remote_prover: string -> AtpManager.prover
end;

structure AtpWrapper: ATP_WRAPPER =
struct

(** generic ATP wrapper **)

(* global hooks for writing problemfiles *)

val destdir = ref "";   (*Empty means write files to /tmp*)
val problem_name = ref "prob";


(* basic template *)

fun external_prover write_problem_files (cmd, args) find_failure produce_answer timeout subgoalno state =
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

    (* write out problem file and call prover *)
    val (ctxt, (chain_ths, goal)) = Proof.get_goal state
    val chain_ths = map (Thm.put_name_hint ResReconstruct.chained_hint) chain_ths
    val (filenames, thm_names_list) = write_problem_files prob_pathname (ctxt, chain_ths, goal)
    val thm_names = nth thm_names_list (subgoalno - 1)

    val cmdline =
      if File.exists cmd then File.shell_path cmd ^ " " ^ args
      else error ("Bad executable: " ^ Path.implode cmd)
    val (proof, rc) = system_out (cmdline ^ " " ^ nth filenames (subgoalno - 1))

    (* remove *temporary* files *)
    val _ = if destdir' = "" then List.app OS.FileSys.remove filenames else ()
    
    (* check for success and print out some information on failure *)
    val failure = find_failure proof
    val success = rc = 0 andalso is_none failure
    val message =
      if success then "Try this command: " ^ produce_answer (proof, thm_names, ctxt, goal, subgoalno)
      else "Could not prove."
    val _ = if isSome failure
      then Output.debug (fn () => "Sledgehammer failure: " ^ the failure ^ "\nOutput: " ^ proof)
      else ()
    val _ = if rc <> 0
      then Output.debug (fn () => "Sledgehammer exited with return code " ^ string_of_int rc ^ ":\n" ^ proof)
      else ()
  in (success, message) end;



(** common provers **)

(* generic TPTP-based provers *)

fun tptp_prover_opts_full max_new theory_const full command =
  external_prover
    (ResAtp.write_problem_files ResHolClause.tptp_write_file max_new theory_const)
    command
    ResReconstruct.find_failure_e_vamp_spass
    (if full then ResReconstruct.structured_proof else ResReconstruct.lemma_list_tstp);

(*arbitrary ATP with TPTP input/output and problemfile as last argument*)
fun tptp_prover_opts max_new theory_const =
  tptp_prover_opts_full max_new theory_const false;

val tptp_prover = tptp_prover_opts 60 true;

(*for structured proofs: prover must support TSTP*)
fun full_prover_opts max_new theory_const =
  tptp_prover_opts_full max_new theory_const true;

val full_prover = full_prover_opts 60 true;


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

val vampire_full = vampire_opts 60 false;


(* E prover *)

fun eprover_opts max_new theory_const = tptp_prover_opts
  max_new theory_const
  (Path.explode "$E_HOME/eproof", "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent");

val eprover = eprover_opts 100 false;

fun eprover_opts_full max_new theory_const = full_prover_opts
  max_new theory_const
  (Path.explode "$E_HOME/eproof", "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent");

val eprover_full = eprover_opts_full 100 false;


(* SPASS *)

fun spass_opts max_new theory_const = external_prover
  (ResAtp.write_problem_files ResHolClause.dfg_write_file max_new theory_const)
  (Path.explode "$SPASS_HOME/SPASS", "-Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof")
  ResReconstruct.find_failure_e_vamp_spass
  ResReconstruct.lemma_list_dfg;

val spass = spass_opts 40 true;


(* remote prover invocation via SystemOnTPTP *)

fun remote_prover_opts max_new theory_const args timeout =
  tptp_prover_opts max_new theory_const
  (Path.explode "$ISABELLE_HOME/contrib/SystemOnTPTP/remote", args ^ " -t " ^ string_of_int timeout)
  timeout;

val remote_prover = remote_prover_opts 60 false;

end;
