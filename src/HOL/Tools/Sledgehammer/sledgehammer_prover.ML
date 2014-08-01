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
     compress : real,
     try0 : bool,
     smt_proofs : bool option,
     slice : bool,
     minimize : bool,
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
    params -> ((string * string list) list -> string -> minimize_command) -> prover_problem ->
    prover_result

  val SledgehammerN : string
  val str_of_mode : mode -> string
  val overlord_file_location_of_prover : string -> string * string
  val proof_banner : mode -> string -> string
  val is_atp : theory -> string -> bool
  val bunch_of_proof_methods : bool -> bool -> string -> proof_method list
  val is_fact_chained : (('a * stature) * 'b) -> bool
  val filter_used_facts : bool -> (''a * stature) list -> ((''a * stature) * 'b) list ->
    ((''a * stature) * 'b) list
  val play_one_line_proof : mode -> Time.time -> ((string * 'a) * thm) list -> Proof.state -> int ->
    proof_method -> proof_method list -> proof_method * play_outcome
  val repair_monomorph_context : int option -> int -> int option -> int -> Proof.context ->
    Proof.context

  val supported_provers : Proof.context -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
end;

structure Sledgehammer_Prover : SLEDGEHAMMER_PROVER =
struct

open ATP_Proof
open ATP_Util
open ATP_Systems
open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Tactic
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

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
   compress : real,
   try0 : bool,
   smt_proofs : bool option,
   slice : bool,
   minimize : bool,
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
  [Simp_Method, Auto_Method, Fastforce_Method, Blast_Method, Meson_Method,
   Metis_Method (if needs_full_types then SOME full_typesN else NONE, NONE),
   Force_Method, Linarith_Method, Presburger_Method] @
  (if needs_full_types then
     [Metis_Method (SOME really_full_type_enc, NONE),
      Metis_Method (SOME full_typesN, SOME desperate_lam_trans),
      Metis_Method (SOME really_full_type_enc, SOME desperate_lam_trans)]
   else
     [Metis_Method (SOME full_typesN, NONE),
      Metis_Method (SOME no_typesN, SOME desperate_lam_trans),
      Metis_Method (SOME really_full_type_enc, SOME desperate_lam_trans)]) @
  (if smt_proofs then [SMT2_Method] else [])

fun preplay_methods timeout facts meths state i =
  let
    val {context = ctxt, facts = chained, goal} = Proof.goal state
    val (_, hyp_ts, concl_t) = strip_subgoal goal i ctxt
    val step =
      Prove ([], [], ("", 0), Logic.list_implies (map prop_of chained @ hyp_ts, concl_t), [],
        ([], facts), meths, "")
  in
    preplay_isar_step ctxt timeout [] step
  end

fun is_fact_chained ((_, (sc, _)), _) = sc = Chained

fun filter_used_facts keep_chained used =
  filter ((member (op =) used o fst) orf (if keep_chained then is_fact_chained else K false))

fun play_one_line_proof mode timeout used_facts state i preferred (meths as meth :: _) =
  let
    fun dont_know () =
      (if member (op =) meths preferred then preferred else meth, Play_Timed_Out Time.zeroTime)
  in
    if timeout = Time.zeroTime then
      dont_know ()
    else
      let
        val _ = if mode = Minimize then Output.urgent_message "Preplaying proof..." else ()
        val gfs = used_facts |> map (fst o fst) |> sort string_ord
      in
        (case preplay_methods timeout gfs meths state i of
          res :: _ => res
        | [] => dont_know ())
      end
  end

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
      sort_strings (supported_atps thy) @
      sort_strings (SMT2_Config.available_solvers_of ctxt)
      |> List.partition (String.isPrefix remote_prefix)
  in
    Output.urgent_message ("Supported provers: " ^ commas (local_provers @ remote_provers) ^ ".")
  end

fun kill_provers () = Async_Manager.kill_threads SledgehammerN "prover"
fun running_provers () = Async_Manager.running_threads SledgehammerN "prover"
val messages = Async_Manager.thread_messages SledgehammerN "prover"

end;
