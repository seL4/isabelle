(*  Title:      HOL/Tools/atp_thread.ML
    ID:         $Id$
    Author:     Fabian Immler, TU Muenchen

Automatic provers as managed threads.
*)

signature ATP_THREAD =
sig
  (* hooks for writing problemfiles *)
  val destdir: string ref
  val problem_name: string ref
  (* basic template *)
  val external_prover:
    ((int -> Path.T) -> Proof.context * Thm.thm list * Thm.thm -> string list * ResHolClause.axiom_name Vector.vector list) ->
    Path.T * string ->
    (string * int -> bool) ->
    (string * string vector * Proof.context * Thm.thm * int -> string) ->
    int -> Proof.state -> Thread.thread
  (* provers as functions returning threads *)
  val tptp_prover_filter_opts_full: int -> bool -> bool -> Path.T * string -> int -> Proof.state -> Thread.thread
  val tptp_prover_filter_opts: int -> bool -> Path.T * string -> int -> Proof.state -> Thread.thread
  val remote_prover_filter_opts: int -> bool -> string -> string -> int -> Proof.state -> Thread.thread
  val full_prover_filter_opts: int -> bool -> Path.T * string -> int -> Proof.state -> Thread.thread
  val tptp_prover: Path.T * string -> int -> Proof.state -> Thread.thread
  val remote_prover: string -> string -> int -> Proof.state -> Thread.thread
  val full_prover: Path.T * string  -> int -> Proof.state -> Thread.thread
  val spass_filter_opts: int -> bool  -> int -> Proof.state -> Thread.thread
  val eprover_filter_opts: int -> bool  -> int -> Proof.state -> Thread.thread
  val eprover_filter_opts_full: int -> bool -> int -> Proof.state -> Thread.thread
  val vampire_filter_opts: int -> bool -> int -> Proof.state -> Thread.thread
  val vampire_filter_opts_full: int -> bool -> int -> Proof.state -> Thread.thread
  val spass: int -> Proof.state -> Thread.thread
  val eprover: int -> Proof.state -> Thread.thread
  val eprover_full: int -> Proof.state -> Thread.thread
  val vampire: int -> Proof.state -> Thread.thread
  val vampire_full: int -> Proof.state -> Thread.thread
end;

structure AtpThread : ATP_THREAD =
struct
  
  (* preferences for path and filename to problemfiles *)
  val destdir = ref "";   (*Empty means write files to /tmp*)
  val problem_name = ref "prob";
      
  (*Setting up a Thread for an external prover*)
  fun external_prover write_problem_files (cmd, args) check_success produce_answer subgoalno state =
    let
    val destdir' = ! destdir
    val problem_name' = ! problem_name
    val (ctxt, (chain_ths, goal)) = Proof.get_goal state
    (* path to unique problem file *)
    fun prob_pathname nr =
      let val probfile = Path.basic (problem_name' ^ serial_string () ^ "_" ^ Int.toString nr)
      in if destdir' = "" then File.tmp_path probfile
        else if File.exists (Path.explode (destdir'))
        then (Path.append  (Path.explode (destdir')) probfile)
        else error ("No such directory: " ^ destdir')
      end
    (* write out problem file and call prover *)
    fun call_prover () =
      let
      val chain_ths = map (Thm.put_name_hint ResReconstruct.chained_hint) chain_ths
      val (filenames, thm_names_list) =
        write_problem_files prob_pathname (ctxt, chain_ths, goal)
      val thm_names = List.nth (thm_names_list, subgoalno - 1); (*(i-1)th element for i-th subgoal*)

      val cmdline =
        if File.exists cmd then File.shell_path cmd ^ " " ^ args
        else error ("Bad executable: " ^ Path.implode cmd);
      val (proof, rc) = system_out (cmdline ^ " " ^ List.nth (filenames, subgoalno - 1))
      val _ =
        if rc <> 0
        then warning ("Sledgehammer with command " ^ quote cmdline ^ " exited with " ^ Int.toString rc)
        else ()
      (* remove *temporary* files *)
      val _ = if destdir' = "" then app (fn file => OS.FileSys.remove file) filenames else ()
      in
        if check_success (proof, rc) then SOME (proof, thm_names, ctxt, goal, subgoalno)
        else NONE
      end
    in
      AtpManager.atp_thread call_prover produce_answer
    end;

    
  (*=========== TEMPLATES FOR AUTOMATIC PROVERS =================*)

  fun tptp_prover_filter_opts_full max_new theory_const full command sg =
    external_prover
    (ResAtp.write_problem_files ResHolClause.tptp_write_file max_new theory_const)
    command
    ResReconstruct.check_success_e_vamp_spass
    (if full then ResReconstruct.structured_proof else ResReconstruct.lemma_list_tstp)
    sg
    
  (* arbitrary atp with tptp input/output and problemfile as last argument*)
  fun tptp_prover_filter_opts max_new theory_const =
    tptp_prover_filter_opts_full max_new theory_const false;
  (* default settings*)  
  val tptp_prover = tptp_prover_filter_opts 60 true;

  (* for structured proofs: prover must support TSTP *)
  fun full_prover_filter_opts max_new theory_const =
    tptp_prover_filter_opts_full max_new theory_const true;
  (* default settings*)
  val full_prover = full_prover_filter_opts 60 true;

  fun vampire_filter_opts max_new theory_const = tptp_prover_filter_opts
    max_new theory_const
    (Path.explode "$VAMPIRE_HOME/vampire", "--output_syntax tptp --mode casc -t 3600") (* vampire does not work without timelimit*)
  (* default settings*)
  val vampire = vampire_filter_opts 60 false;
    
  (* a vampire for full proof output *)
  fun vampire_filter_opts_full max_new theory_const = full_prover_filter_opts
    max_new theory_const
    (Path.explode "$VAMPIRE_HOME/vampire", "--output_syntax tptp --mode casc -t 3600") (* vampire does not work without timelimit*)
  (* default settings*)
  val vampire_full = vampire_filter_opts 60 false;

  fun eprover_filter_opts max_new theory_const = tptp_prover_filter_opts
    max_new theory_const
    (Path.explode "$E_HOME/eproof", "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent")
  (* default settings *)
  val eprover = eprover_filter_opts 100 false;
    
  (* an E for full proof output*)
  fun eprover_filter_opts_full max_new theory_const = full_prover_filter_opts
    max_new theory_const
    (Path.explode "$E_HOME/eproof", "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent")
  (* default settings *)
  val eprover_full = eprover_filter_opts_full 100 false;

  fun spass_filter_opts max_new theory_const = external_prover
    (ResAtp.write_problem_files ResHolClause.dfg_write_file max_new theory_const)
    (Path.explode "$SPASS_HOME/SPASS", "-Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof")
    ResReconstruct.check_success_e_vamp_spass
    ResReconstruct.lemma_list_dfg
  (* default settings*)
  val spass = spass_filter_opts 40 true;
    
  (* remote prover invocation via SystemOnTPTP *)
  fun remote_prover_filter_opts max_new theory_const name command =
    tptp_prover_filter_opts max_new theory_const
    (Path.explode "$ISABELLE_HOME/contrib/SystemOnTPTP/remote", name ^ " " ^ command)
  val remote_prover = remote_prover_filter_opts 60 false

end;
