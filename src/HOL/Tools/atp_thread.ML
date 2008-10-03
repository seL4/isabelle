(*  Title:      HOL/Tools/atp_thread.ML
    ID:         $Id$
    Author:     Fabian Immler, TU Muenchen

Automatic provers as managed threads.
*)

signature ATP_THREAD =
sig
  (* basic templates *)
  val atp_thread: (unit -> 'a option) -> ('a -> unit) -> string -> Thread.thread * string
  val external_prover:int ->
    ((int -> Path.T) -> Proof.context * Thm.thm list * Thm.thm -> string list * ResHolClause.axiom_name Vector.vector list) ->
    string ->
    (string * int -> bool) ->
    (string * string vector * Proof.context * Thm.thm * int -> string) ->
    Toplevel.state -> Thread.thread * string
  (* settings for writing problemfiles *)
  val destdir: string ref
  val problem_name: string ref
  (* provers as functions returning threads *)
  val tptp_prover_filter_opts_full: int -> bool -> bool -> string -> Toplevel.state -> (Thread.thread * string)
  val tptp_prover_filter_opts: int -> bool -> string -> Toplevel.state -> (Thread.thread * string)
  val full_prover_filter_opts: int -> bool -> string -> Toplevel.state -> (Thread.thread * string)
  val tptp_prover: string -> Toplevel.state -> (Thread.thread * string)
  val full_prover: string -> Toplevel.state -> (Thread.thread * string)  val spass_filter_opts: int -> bool -> Toplevel.state -> (Thread.thread * string)
  val eprover_filter_opts: int -> bool -> Toplevel.state -> (Thread.thread * string)
  val eprover_filter_opts_full: int -> bool -> Toplevel.state -> (Thread.thread * string)
  val vampire_filter_opts: int -> bool -> Toplevel.state -> (Thread.thread * string)
  val vampire_filter_opts_full: int -> bool -> Toplevel.state -> (Thread.thread * string)
  val spass: Toplevel.state -> (Thread.thread * string)
  val eprover: Toplevel.state -> (Thread.thread * string)
  val eprover_full: Toplevel.state -> (Thread.thread * string)
  val vampire: Toplevel.state -> (Thread.thread * string)
  val vampire_full: Toplevel.state -> (Thread.thread * string)
  val setup: theory -> theory
end;

structure AtpThread : ATP_THREAD =
struct

  structure Recon = ResReconstruct

  (* if a thread calls priority while PG works on a ML{**}-block, PG will not leave the block *)
  fun delayed_priority s = (OS.Process.sleep (Time.fromMilliseconds 100); priority s);

  (* -------- AUTOMATIC THEOREM PROVERS AS THREADS ----------*)

  (* create an automatic-prover thread, registering has to be done by sledgehammer
    or manual via AtpManager.register;
    unregistering is done by thread.
  *)
  fun atp_thread call_prover action_success description =
    let val thread = Thread.fork(fn () =>
      let
      val answer = call_prover ()
      val _ = if isSome answer then action_success (valOf answer)
        else delayed_priority ("Sledgehammer: " ^ description ^ "\n  failed.")
      in AtpManager.unregister (isSome answer)
      end
      handle Interrupt => delayed_priority ("Sledgehammer: " ^ description ^ "\n  interrupted.")
    ,[Thread.EnableBroadcastInterrupt true,
     Thread.InterruptState Thread.InterruptAsynch])
    in (thread, description) end

  (* Settings for path and filename to problemfiles *)
  val destdir = ref "";   (*Empty means write files to /tmp*)
  val problem_name = ref "prob";

  (*Setting up a Thread for an external prover*)
  fun external_prover subgoalno write_problem_files command check_success produce_answer state =
    let
      (*creating description from provername and subgoal*)
    val call::path = rev (String.tokens (fn c => c = #"/") command)
    val name::options = String.tokens (fn c => c = #" ") call
    val (ctxt, (chain_ths, goal)) = Proof.get_goal (Toplevel.proof_of state)
    val description = "External prover '" ^ name ^ "' for Subgoal " ^ Int.toString subgoalno
      ^ ":\n" ^ Display.string_of_cterm (List.nth(cprems_of goal, subgoalno-1))
      (* path to unique problemfile *)
    fun prob_pathname nr =
      let val probfile = Path.basic (!problem_name ^ serial_string () ^ "_" ^ Int.toString nr)
      in if !destdir = "" then File.tmp_path probfile
        else if File.exists (Path.explode (!destdir))
        then (Path.append  (Path.explode (!destdir)) probfile)
        else error ("No such directory: " ^ !destdir)
      end
      (* write out problem file and call prover *)
    fun call_prover () =
      let
      val chain_ths = map (Thm.put_name_hint Recon.chained_hint) chain_ths
      val (filenames, thm_names_list) =
        write_problem_files prob_pathname (ctxt, chain_ths, goal)
      val thm_names = List.nth(thm_names_list, subgoalno - 1);(*(i-1)th element for i-th subgoal*)
      val (proof, rc) = system_out (command ^ " " ^ List.nth(filenames, subgoalno - 1))
      val _ = map (fn file => OS.FileSys.remove file) filenames
      in
        if check_success (proof, rc) then SOME (proof, thm_names, ctxt, goal, subgoalno)
        else NONE
      end
      (* output answer of res_reconstruct with description of subgoal *)
    fun action_success result =
      let
      val answer = produce_answer result
      val _ = priority ("Sledgehammer: " ^ description ^ "\n    Try this command: " ^ answer)
      in () end
    in
      atp_thread call_prover action_success description
    end;

  (*=========== TEMPLATES FOR AUTOMATIC PROVERS =================*)

  fun tptp_prover_filter_opts_full max_new theory_const full command state =
    external_prover 1
    (ResAtp.write_problem_files ResHolClause.tptp_write_file max_new theory_const)
    command
    Recon.check_success_e_vamp_spass
    (if full then Recon.structured_proof else Recon.lemma_list_tstp)
    state;

  (* arbitrary atp with tptp input/output and problemfile as last argument*)
  fun tptp_prover_filter_opts max_new theory_const =
    tptp_prover_filter_opts_full max_new theory_const false;
  (* default settings*)
  val tptp_prover = tptp_prover_filter_opts 60 true;

  (* for structured proofs: prover must support tstp! *)
  fun full_prover_filter_opts max_new theory_const =
    tptp_prover_filter_opts_full max_new theory_const true;
  (* default settings*)
  val full_prover = full_prover_filter_opts 60 true;

    (* Return the path to a "helper" like SPASS, E or Vampire, first checking that
  it exists. *)
  fun prover_command path =
    if File.exists path then File.shell_path path
    else error ("Could not find the file '" ^ (Path.implode o Path.expand) path ^ "'")

  (* a vampire for first subgoal *)
  fun vampire_filter_opts max_new theory_const state = tptp_prover_filter_opts
    max_new theory_const
    (prover_command (Path.explode "$VAMPIRE_HOME/vampire")
    ^ " --output_syntax tptp --mode casc -t 3600") (* vampire does not work without timelimit*)
    state;
  (* default settings*)
  val vampire = vampire_filter_opts 60 false;
  (* a vampire for full proof output *)
  fun vampire_filter_opts_full max_new theory_const state = full_prover_filter_opts
    max_new theory_const
    (prover_command (Path.explode "$VAMPIRE_HOME/vampire")
    ^ " --output_syntax tptp --mode casc -t 3600") (* vampire does not work without timelimit*)
    state;
  (* default settings*)
  val vampire_full = vampire_filter_opts 60 false;

  (* an E for first subgoal *)
  fun eprover_filter_opts max_new theory_const state = tptp_prover_filter_opts
    max_new theory_const
    (prover_command (Path.explode "$E_HOME/eproof")
    ^ " --tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent")
    state;
  (* default settings *)
  val eprover = eprover_filter_opts 100 false;
  (* an E for full proof output*)
  fun eprover_filter_opts_full max_new theory_const state = full_prover_filter_opts
    max_new theory_const
    (prover_command (Path.explode "$E_HOME/eproof")
    ^ " --tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent")
    state;
  (* default settings *)
  val eprover_full = eprover_filter_opts_full 100 false;

  (* SPASS for first subgoal *)
  fun spass_filter_opts max_new theory_const state = external_prover 1
    (ResAtp.write_problem_files ResHolClause.dfg_write_file max_new theory_const)
    (prover_command (Path.explode "$SPASS_HOME/SPASS")
    ^ " -Auto -SOS=1 -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof")
    Recon.check_success_e_vamp_spass
    Recon.lemma_list_dfg
    state;
  (* default settings*)
  val spass = spass_filter_opts 40 true;

  (*TODO: Thread running some selected or recommended provers of "System On TPTP" *)



  fun add_prover name prover_fun = AtpManager.Provers.map (Symtab.update (name, prover_fun))

    (* include 'original' provers and provers with structured output *)
  val setup =
    (* original setups *)
    add_prover "spass" spass #>
    add_prover "vampire" vampire #>
    add_prover "e" eprover #>
    (* provers with stuctured output *)
    add_prover "vampire_full" vampire_full #>
    add_prover "e_full" eprover_full #>
    (* on some problems better results *)
    add_prover "spass_no_tc" (spass_filter_opts 40 false);

end;
