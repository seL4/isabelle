(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Generic prover abstraction for Sledgehammer.
*)

signature SLEDGEHAMMER_PROVER =
sig
  type atp_failure = ATP_Proof.atp_failure
  type stature = ATP_Problem_Generate.stature
  type type_enc = ATP_Problem_Generate.type_enc
  type fact = Sledgehammer_Fact.fact
  type proof_method = Sledgehammer_Proof_Methods.proof_method
  type play_outcome = Sledgehammer_Proof_Methods.play_outcome
  type minimize_command = Sledgehammer_Proof_Methods.minimize_command

  datatype mode = Auto_Try | Try | Normal | MaSh | Auto_Minimize | Minimize

  type params =
    {debug : bool,
     verbose : bool,
     overlord : bool,
     spy : bool,
     blocking : bool,
     provers : string list,
     type_enc : string option,
     strict : bool,
     lam_trans : string option,
     uncurried_aliases : bool option,
     learn : bool,
     fact_filter : string option,
     max_facts : int option,
     fact_thresholds : real * real,
     max_mono_iters : int option,
     max_new_mono_instances : int option,
     isar_proofs : bool option,
     compress_isar : real,
     try0_isar : bool,
     smt_proofs : bool option,
     slice : bool,
     minimize : bool option,
     timeout : Time.time,
     preplay_timeout : Time.time,
     expect : string}

  type prover_problem =
    {comment : string,
     state : Proof.state,
     goal : thm,
     subgoal : int,
     subgoal_count : int,
     factss : (string * fact list) list}

  type prover_result =
    {outcome : atp_failure option,
     used_facts : (string * stature) list,
     used_from : fact list,
     run_time : Time.time,
     preplay : (proof_method * play_outcome) Lazy.lazy,
     message : proof_method * play_outcome -> string,
     message_tail : string}

  type prover =
    params -> ((string * string list) list -> string -> minimize_command)
    -> prover_problem -> prover_result

  val SledgehammerN : string
  val str_of_mode : mode -> string
  val smtN : string
  val overlord_file_location_of_prover : string -> string * string
  val proof_banner : mode -> string -> string
  val extract_proof_method : params -> proof_method -> string * (string * string list) list
  val is_proof_method : string -> bool
  val is_atp : theory -> string -> bool
  val bunch_of_proof_methods : bool -> bool -> string -> proof_method list
  val is_fact_chained : (('a * stature) * 'b) -> bool
  val filter_used_facts :
    bool -> (''a * stature) list -> ((''a * stature) * 'b) list ->
    ((''a * stature) * 'b) list
  val play_one_line_proof : mode -> bool -> Time.time -> ((string * 'a) * thm) list ->
    Proof.state -> int -> proof_method -> proof_method list -> proof_method * play_outcome
  val isar_supported_prover_of : theory -> string -> string
  val choose_minimize_command : theory -> params -> ((string * string list) list -> string -> 'a) ->
    string -> proof_method * play_outcome -> 'a
  val repair_monomorph_context : int option -> int -> int option -> int -> Proof.context ->
    Proof.context

  val supported_provers : Proof.context -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
end;

structure Sledgehammer_Prover : SLEDGEHAMMER_PROVER =
struct

open ATP_Util
open ATP_Problem
open ATP_Systems
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Tactic
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods

(* Identifier that distinguishes Sledgehammer from other tools that could use
   "Async_Manager". *)
val SledgehammerN = "Sledgehammer"

datatype mode = Auto_Try | Try | Normal | MaSh | Auto_Minimize | Minimize

fun str_of_mode Auto_Try = "Auto Try"
  | str_of_mode Try = "Try"
  | str_of_mode Normal = "Normal"
  | str_of_mode MaSh = "MaSh"
  | str_of_mode Auto_Minimize = "Auto_Minimize"
  | str_of_mode Minimize = "Minimize"

val smtN = "smt"

val proof_method_names = [metisN, smtN]
val is_proof_method = member (op =) proof_method_names

val is_atp = member (op =) o supported_atps

type params =
  {debug : bool,
   verbose : bool,
   overlord : bool,
   spy : bool,
   blocking : bool,
   provers : string list,
   type_enc : string option,
   strict : bool,
   lam_trans : string option,
   uncurried_aliases : bool option,
   learn : bool,
   fact_filter : string option,
   max_facts : int option,
   fact_thresholds : real * real,
   max_mono_iters : int option,
   max_new_mono_instances : int option,
   isar_proofs : bool option,
   compress_isar : real,
   try0_isar : bool,
   smt_proofs : bool option,
   slice : bool,
   minimize : bool option,
   timeout : Time.time,
   preplay_timeout : Time.time,
   expect : string}

type prover_problem =
  {comment : string,
   state : Proof.state,
   goal : thm,
   subgoal : int,
   subgoal_count : int,
   factss : (string * fact list) list}

type prover_result =
  {outcome : atp_failure option,
   used_facts : (string * stature) list,
   used_from : fact list,
   run_time : Time.time,
   preplay : (proof_method * play_outcome) Lazy.lazy,
   message : proof_method * play_outcome -> string,
   message_tail : string}

type prover =
  params -> ((string * string list) list -> string -> minimize_command)
  -> prover_problem -> prover_result

fun overlord_file_location_of_prover prover = (getenv "ISABELLE_HOME_USER", "prob_" ^ prover)

fun proof_banner mode name =
  (case mode of
    Auto_Try => "Auto Sledgehammer (" ^ quote name ^ ") found a proof"
  | Try => "Sledgehammer (" ^ quote name ^ ") found a proof"
  | _ => "Try this")

fun bunch_of_proof_methods smt_proofs needs_full_types desperate_lam_trans =
  (if needs_full_types then
     [Metis_Method (SOME full_typesN, NONE),
      Metis_Method (SOME really_full_type_enc, NONE),
      Metis_Method (SOME full_typesN, SOME desperate_lam_trans),
      Metis_Method (SOME really_full_type_enc, SOME desperate_lam_trans)]
   else
     [Metis_Method (NONE, NONE),
      Metis_Method (SOME full_typesN, NONE),
      Metis_Method (SOME no_typesN, SOME desperate_lam_trans),
      Metis_Method (SOME really_full_type_enc, SOME desperate_lam_trans)]) @
  (if smt_proofs then [SMT2_Method] else [])

fun extract_proof_method ({type_enc, lam_trans, ...} : params)
      (Metis_Method (type_enc', lam_trans')) =
    let
      val override_params =
        (if is_none type_enc' andalso is_none type_enc then []
         else [("type_enc", [hd (unalias_type_enc (type_enc' |> the_default partial_typesN))])]) @
        (if is_none lam_trans' andalso is_none lam_trans then []
         else [("lam_trans", [lam_trans' |> the_default default_metis_lam_trans])])
    in (metisN, override_params) end
  | extract_proof_method _ SMT2_Method = (smtN, [])

(* based on "Mirabelle.can_apply" and generalized *)
fun timed_apply timeout tac state i =
  let
    val {context = ctxt, facts, goal} = Proof.goal state
    val full_tac = Method.insert_tac facts i THEN tac ctxt i
  in
    TimeLimit.timeLimit timeout (try (Seq.pull o full_tac)) goal
  end

fun timed_proof_method timeout ths meth =
  timed_apply timeout (fn ctxt => tac_of_proof_method ctxt ([], ths) meth)

fun is_fact_chained ((_, (sc, _)), _) = sc = Chained

fun filter_used_facts keep_chained used =
  filter ((member (op =) used o fst) orf (if keep_chained then is_fact_chained else K false))

fun play_one_line_proof mode verbose timeout pairs state i preferred (meths as meth :: _) =
  let
    val ctxt = Proof.context_of state

    fun get_preferred meths = if member (op =) meths preferred then preferred else meth
  in
    if timeout = Time.zeroTime then
      (get_preferred meths, Play_Timed_Out Time.zeroTime)
    else
      let
        val _ = if mode = Minimize then Output.urgent_message "Preplaying proof..." else ()
        val ths = pairs |> sort_wrt (fst o fst) |> map snd
        fun play [] [] = (get_preferred meths, Play_Failed)
          | play timed_outs [] = (get_preferred timed_outs, Play_Timed_Out timeout)
          | play timed_out (meth :: meths) =
            let
              val _ =
                if verbose then
                  Output.urgent_message ("Trying \"" ^ string_of_proof_method ctxt [] meth ^
                    "\" for " ^ string_of_time timeout ^ "...")
                else
                  ()
              val timer = Timer.startRealTimer ()
            in
              (case timed_proof_method timeout ths meth state i of
                SOME (SOME _) => (meth, Played (Timer.checkRealTimer timer))
              | _ => play timed_out meths)
            end
            handle TimeLimit.TimeOut => play (meth :: timed_out) meths
      in
        play [] meths
      end
  end

val canonical_isar_supported_prover = eN
val z3_newN = "z3_new"

fun isar_supported_prover_of thy name =
  if is_atp thy name orelse name = z3_newN then name
  else if is_atp_installed thy canonical_isar_supported_prover then canonical_isar_supported_prover
  else name

(* FIXME: See the analogous logic in the function "maybe_minimize" in
   "sledgehammer_prover_minimize.ML". *)
fun choose_minimize_command thy (params as {isar_proofs, ...}) minimize_command name preplay =
  let
    val maybe_isar_name = name |> isar_proofs = SOME true ? isar_supported_prover_of thy
    val (min_name, override_params) =
      (case preplay of
        (meth as Metis_Method _, Played _) =>
        if isar_proofs = SOME true then (maybe_isar_name, []) else extract_proof_method params meth
      | _ => (maybe_isar_name, []))
  in minimize_command override_params min_name end

val max_fact_instances = 10 (* FUDGE *)

fun repair_monomorph_context max_iters best_max_iters max_new_instances best_max_new_instances =
  Config.put Monomorph.max_rounds (max_iters |> the_default best_max_iters)
  #> Config.put Monomorph.max_new_instances
       (max_new_instances |> the_default best_max_new_instances)
  #> Config.put Monomorph.max_thm_instances max_fact_instances

fun supported_provers ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val (remote_provers, local_provers) =
      proof_method_names @
      sort_strings (supported_atps thy) @
      sort_strings (SMT_Solver.available_solvers_of ctxt) @
      sort_strings (SMT2_Config.available_solvers_of ctxt)
      |> List.partition (String.isPrefix remote_prefix)
  in
    Output.urgent_message ("Supported provers: " ^
                           commas (local_provers @ remote_provers) ^ ".")
  end

fun kill_provers () = Async_Manager.kill_threads SledgehammerN "prover"
fun running_provers () = Async_Manager.running_threads SledgehammerN "prover"
val messages = Async_Manager.thread_messages SledgehammerN "prover"

end;
