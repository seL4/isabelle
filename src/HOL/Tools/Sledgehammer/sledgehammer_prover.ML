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
  type induction_rules = Sledgehammer_Fact.induction_rules
  type proof_method = Sledgehammer_Proof_Methods.proof_method
  type play_outcome = Sledgehammer_Proof_Methods.play_outcome

  datatype mode = Auto_Try | Try | Normal | Minimize | MaSh

  type params =
    {debug : bool,
     verbose : bool,
     overlord : bool,
     spy : bool,
     provers : string list,
     type_enc : string option,
     strict : bool,
     lam_trans : string option,
     uncurried_aliases : bool option,
     learn : bool,
     fact_filter : string option,
     induction_rules : induction_rules option,
     max_facts : int option,
     fact_thresholds : real * real,
     max_mono_iters : int option,
     max_new_mono_instances : int option,
     isar_proofs : bool option,
     compress : real option,
     try0 : bool,
     smt_proofs : bool,
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
     factss : (string * fact list) list,
     found_proof : unit -> unit}

  type prover_result =
    {outcome : atp_failure option,
     used_facts : (string * stature) list,
     used_from : fact list,
     preferred_methss : proof_method * proof_method list list,
     run_time : Time.time,
     message : (unit -> (string * stature) list * (proof_method * play_outcome)) -> string}

  type prover = params -> prover_problem -> prover_result

  val SledgehammerN : string
  val str_of_mode : mode -> string
  val overlord_file_location_of_prover : string -> string * string
  val proof_banner : mode -> string -> string
  val is_atp : theory -> string -> bool
  val bunches_of_proof_methods : Proof.context -> bool -> bool -> bool -> string ->
    proof_method list list
  val is_fact_chained : (('a * stature) * 'b) -> bool
  val filter_used_facts : bool -> (''a * stature) list -> ((''a * stature) * 'b) list ->
    ((''a * stature) * 'b) list
  val repair_monomorph_context : int option -> int -> int option -> int -> Proof.context ->
    Proof.context
  val supported_provers : Proof.context -> unit
end;

structure Sledgehammer_Prover : SLEDGEHAMMER_PROVER =
struct

open ATP_Proof
open ATP_Util
open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Tactic
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
open Sledgehammer_ATP_Systems

(* Identifier that distinguishes Sledgehammer from other tools that could use "Async_Manager". *)
val SledgehammerN = "Sledgehammer"

datatype mode = Auto_Try | Try | Normal | Minimize | MaSh

fun str_of_mode Auto_Try = "Auto Try"
  | str_of_mode Try = "Try"
  | str_of_mode Normal = "Normal"
  | str_of_mode Minimize = "Minimize"
  | str_of_mode MaSh = "MaSh"

val is_atp = member (op =) o supported_atps

type params =
  {debug : bool,
   verbose : bool,
   overlord : bool,
   spy : bool,
   provers : string list,
   type_enc : string option,
   strict : bool,
   lam_trans : string option,
   uncurried_aliases : bool option,
   learn : bool,
   fact_filter : string option,
   induction_rules : induction_rules option,
   max_facts : int option,
   fact_thresholds : real * real,
   max_mono_iters : int option,
   max_new_mono_instances : int option,
   isar_proofs : bool option,
   compress : real option,
   try0 : bool,
   smt_proofs : bool,
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
   factss : (string * fact list) list,
   found_proof : unit -> unit}

type prover_result =
  {outcome : atp_failure option,
   used_facts : (string * stature) list,
   used_from : fact list,
   preferred_methss : proof_method * proof_method list list,
   run_time : Time.time,
   message : (unit -> (string * stature) list * (proof_method * play_outcome)) -> string}

type prover = params -> prover_problem -> prover_result

fun overlord_file_location_of_prover prover = (getenv "ISABELLE_HOME_USER", "prob_" ^ prover)

fun proof_banner mode name =
  (case mode of
    Auto_Try => "Auto Sledgehammer (" ^ quote name ^ ") found a proof"
  | Try => "Sledgehammer (" ^ quote name ^ ") found a proof"
  | _ => "Try this")

fun bunches_of_proof_methods ctxt try0 smt_proofs needs_full_types desperate_lam_trans =
  let
    val try0_methodss =
      if try0 then
        [[Simp_Method, Auto_Method, Blast_Method, Linarith_Method, Meson_Method,
          Metis_Method (NONE, NONE), Fastforce_Method, Force_Method, Presburger_Method]]
      else
        []

    val metis_methods =
      (if try0 then [] else [Metis_Method (NONE, NONE)]) @
      Metis_Method (SOME full_typesN, NONE) ::
      Metis_Method (SOME really_full_type_enc, SOME desperate_lam_trans) ::
      (if needs_full_types then
         [Metis_Method (SOME really_full_type_enc, NONE),
          Metis_Method (SOME full_typesN, SOME desperate_lam_trans)]
       else
         [Metis_Method (SOME no_typesN, SOME desperate_lam_trans)])

    val smt_methodss =
      if smt_proofs then
        [SMT_Method SMT_Z3 ::
         map (fn strategy => SMT_Method (SMT_Verit strategy))
           (Verit_Proof.all_veriT_stgies (Context.Proof ctxt))]
      else
        []
  in
    try0_methodss @ [metis_methods] @ smt_methodss
  end

fun is_fact_chained ((_, (sc, _)), _) = sc = Chained

fun filter_used_facts keep_chained used =
  filter ((member (eq_fst (op =)) used o fst) orf
    (if keep_chained then is_fact_chained else K false))

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
      sort_strings (supported_atps thy) @ sort_strings (SMT_Config.available_solvers_of ctxt)
      |> List.partition (String.isPrefix remote_prefix)
  in
    writeln ("Supported provers: " ^ commas (local_provers @ remote_provers))
  end

end;
