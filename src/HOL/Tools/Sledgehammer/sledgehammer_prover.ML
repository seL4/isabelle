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
  type base_slice = Sledgehammer_ATP_Systems.base_slice
  type atp_slice = Sledgehammer_ATP_Systems.atp_slice

  datatype mode = Auto_Try | Try | Normal | Minimize | MaSh

  datatype induction_rules = Include | Exclude | Instantiate
  val induction_rules_of_string : string -> induction_rules option
  val maybe_filter_out_induction_rules : induction_rules -> fact list -> fact list

  type params =
    {debug : bool,
     verbose : bool,
     overlord : bool,
     spy : bool,
     provers : string list,
     abduce : int option,
     falsify : bool option,
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
     max_proofs : int,
     isar_proofs : bool option,
     compress : real option,
     try0 : bool,
     smt_proofs : bool,
     minimize : bool,
     slices : int,
     timeout : Time.time,
     preplay_timeout : Time.time,
     expect : string}

  val string_of_params : params -> string
  val slice_timeout : int -> int -> Time.time -> Time.time

  type prover_problem =
    {comment : string,
     state : Proof.state,
     goal : thm,
     subgoal : int,
     subgoal_count : int,
     factss : (string * fact list) list,
     has_already_found_something : unit -> bool,
     found_something : string -> unit}

  datatype prover_slice_extra =
    ATP_Slice of atp_slice
  | SMT_Slice of string list

  type prover_slice = base_slice * prover_slice_extra

  type prover_result =
    {outcome : atp_failure option,
     used_facts : (string * stature) list,
     used_from : fact list,
     preferred_methss : proof_method * proof_method list list,
     run_time : Time.time,
     message : (unit -> (string * stature) list * (proof_method * play_outcome)) -> string}

  type prover = params -> prover_problem -> prover_slice -> prover_result

  val SledgehammerN : string
  val default_abduce_max_candidates : int
  val str_of_mode : mode -> string
  val overlord_file_location_of_prover : string -> string * string
  val proof_banner : mode -> string -> string
  val is_atp : string -> bool
  val bunches_of_proof_methods : Proof.context -> bool -> bool -> string -> proof_method list list
  val facts_of_filter : string -> (string * fact list) list -> fact list
  val facts_of_basic_slice : base_slice -> (string * fact list) list -> fact list
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

val default_abduce_max_candidates = 1

datatype mode = Auto_Try | Try | Normal | Minimize | MaSh

fun str_of_mode Auto_Try = "Auto Try"
  | str_of_mode Try = "Try"
  | str_of_mode Normal = "Normal"
  | str_of_mode Minimize = "Minimize"
  | str_of_mode MaSh = "MaSh"

datatype induction_rules = Include | Exclude | Instantiate

fun induction_rules_of_string "include" = SOME Include
  | induction_rules_of_string "exclude" = SOME Exclude
  | induction_rules_of_string "instantiate" = SOME Instantiate
  | induction_rules_of_string _ = NONE

val is_atp = member (op =) all_atps

type params =
  {debug : bool,
   verbose : bool,
   overlord : bool,
   spy : bool,
   provers : string list,
   abduce : int option,
   falsify : bool option,
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
   max_proofs : int,
   isar_proofs : bool option,
   compress : real option,
   try0 : bool,
   smt_proofs : bool,
   minimize : bool,
   slices : int,
   timeout : Time.time,
   preplay_timeout : Time.time,
   expect : string}

fun string_of_params (params : params) =
  YXML.content_of (ML_Pretty.string_of (ML_system_pretty (params, 100)))

fun maybe_filter_out_induction_rules induction_rules : fact list -> fact list =
  induction_rules = Exclude ?
    filter_out (fn ((_, (_, ATP_Problem_Generate.Induction)), _) => true | _ => false)

fun slice_timeout slice_size slices timeout =
  let
    val max_threads = Multithreading.max_threads ()
    val batches = (slices + max_threads - 1) div max_threads
  in
    seconds (Real.fromInt slice_size * Time.toReal timeout / Real.fromInt batches)
  end

type prover_problem =
  {comment : string,
   state : Proof.state,
   goal : thm,
   subgoal : int,
   subgoal_count : int,
   factss : (string * fact list) list,
   has_already_found_something : unit -> bool,
   found_something : string -> unit}

datatype prover_slice_extra =
  ATP_Slice of atp_slice
| SMT_Slice of string list

type prover_slice = base_slice * prover_slice_extra

type prover_result =
  {outcome : atp_failure option,
   used_facts : (string * stature) list,
   used_from : fact list,
   preferred_methss : proof_method * proof_method list list,
   run_time : Time.time,
   message : (unit -> (string * stature) list * (proof_method * play_outcome)) -> string}

type prover = params -> prover_problem -> prover_slice -> prover_result

fun overlord_file_location_of_prover prover = (getenv "ISABELLE_HOME_USER", "prob_" ^ prover)

fun proof_banner mode prover_name =
  (case mode of
    Auto_Try => "Auto Sledgehammer (" ^ prover_name ^ ") found a proof: "
  | Try => "Sledgehammer (" ^ prover_name ^ ") found a proof: "
  | _ => "Try this: ")

fun bunches_of_proof_methods ctxt smt_proofs needs_full_types desperate_lam_trans =
  let
    val misc_methodss =
      [[Simp_Method, Auto_Method, Blast_Method, Linarith_Method, Meson_Method,
        Metis_Method (NONE, NONE), Fastforce_Method, Force_Method, Presburger_Method,
        Argo_Method, Order_Method]]

    val metis_methodss =
      [Metis_Method (SOME full_typesN, NONE) ::
       Metis_Method (SOME really_full_type_enc, SOME desperate_lam_trans) ::
       (if needs_full_types then
          [Metis_Method (SOME really_full_type_enc, NONE),
           Metis_Method (SOME full_typesN, SOME desperate_lam_trans)]
        else
          [Metis_Method (SOME no_typesN, SOME desperate_lam_trans)])]

    val smt_methodss =
      if smt_proofs then
        [map (SMT_Method o SMT_Verit) (Verit_Strategies.all_veriT_stgies (Context.Proof ctxt)),
         [SMT_Method SMT_Z3]]
      else
        []
  in
    misc_methodss @ metis_methodss @ smt_methodss
  end

fun facts_of_filter fact_filter factss =
  (case AList.lookup (op =) factss fact_filter of
    SOME facts => facts
  | NONE => snd (hd factss))

fun facts_of_basic_slice (_, _, _, num_facts, fact_filter) factss =
  let
    val facts = facts_of_filter fact_filter factss
    val (goal_facts, nongoal_facts) =
      List.partition (equal sledgehammer_goal_as_fact o fst o fst) facts
  in
    goal_facts @ take num_facts nongoal_facts
  end

fun is_fact_chained ((_, (sc, _)), _) = sc = Chained

fun filter_used_facts keep_chained used =
  filter ((member (eq_fst (op =)) used o fst) orf
    (if keep_chained then is_fact_chained else K false))

val max_fact_instances = 10 (* FUDGE *)
val max_schematics = 20 (* FUDGE *)

fun repair_monomorph_context max_iters best_max_iters max_new_instances best_max_new_instances =
  Config.put Monomorph.max_rounds (max_iters |> the_default best_max_iters)
  #> Config.put Monomorph.max_new_instances
       (max_new_instances |> the_default best_max_new_instances)
  #> Config.put Monomorph.max_thm_instances max_fact_instances
  #> Config.put Monomorph.max_schematics max_schematics

fun supported_provers ctxt =
  let
    val local_provers = sort_strings (local_atps @ SMT_Config.available_solvers_of ctxt)
    val remote_provers = sort_strings remote_atps
  in
    writeln ("Supported provers: " ^ commas (local_provers @ remote_provers))
  end

end;
