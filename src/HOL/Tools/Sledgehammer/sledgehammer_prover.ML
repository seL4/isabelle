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
  type reconstructor = Sledgehammer_Reconstructor.reconstructor
  type play_outcome = Sledgehammer_Reconstructor.play_outcome
  type minimize_command = Sledgehammer_Reconstructor.minimize_command

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
     preplay : (reconstructor * play_outcome) Lazy.lazy,
     message : reconstructor * play_outcome -> string,
     message_tail : string}

  type prover =
    params -> ((string * string list) list -> string -> minimize_command)
    -> prover_problem -> prover_result

  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val completish : bool Config.T
  val atp_full_names : bool Config.T
  val SledgehammerN : string
  val plain_metis : reconstructor
  val overlord_file_location_of_prover : string -> string * string
  val proof_banner : mode -> string -> string
  val extract_reconstructor : params -> reconstructor -> string * (string * string list) list
  val is_reconstructor : string -> bool
  val is_atp : theory -> string -> bool
  val is_ho_atp: Proof.context -> string -> bool
  val is_unit_equational_atp : Proof.context -> string -> bool
  val is_unit_equality : term -> bool
  val is_appropriate_prop_of_prover : Proof.context -> string -> term -> bool
  val supported_provers : Proof.context -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
  val is_fact_chained : (('a * stature) * 'b) -> bool
  val bunch_of_reconstructors : bool -> (bool -> string) -> reconstructor list
  val filter_used_facts :
    bool -> (''a * stature) list -> ((''a * stature) * 'b) list ->
    ((''a * stature) * 'b) list
  val play_one_line_proof : mode -> bool -> bool -> Time.time -> ((string * 'a) * thm) list ->
    Proof.state -> int -> reconstructor -> reconstructor list -> reconstructor * play_outcome
  val remotify_atp_if_not_installed : theory -> string -> string option
  val isar_supported_prover_of : theory -> string -> string
  val choose_minimize_command : theory -> params -> ((string * string list) list -> string -> 'a) ->
    string -> reconstructor * play_outcome -> 'a
  val repair_monomorph_context : int option -> int -> int option -> int -> Proof.context ->
    Proof.context
  val run_reconstructor : mode -> string -> prover
end;

structure Sledgehammer_Prover : SLEDGEHAMMER_PROVER =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Systems
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Tactic
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Print
open Sledgehammer_Isar

(* Empty string means create files in Isabelle's temporary files directory. *)
val dest_dir = Attrib.setup_config_string @{binding sledgehammer_dest_dir} (K "")
val problem_prefix = Attrib.setup_config_string @{binding sledgehammer_problem_prefix} (K "prob")
val completish = Attrib.setup_config_bool @{binding sledgehammer_completish} (K false)

(* In addition to being easier to read, readable names are often much shorter,
   especially if types are mangled in names. This makes a difference for some
   provers (e.g., E). For these reason, short names are enabled by default. *)
val atp_full_names = Attrib.setup_config_bool @{binding sledgehammer_atp_full_names} (K false)

datatype mode = Auto_Try | Try | Normal | MaSh | Auto_Minimize | Minimize

(* Identifier that distinguishes Sledgehammer from other tools that could use
   "Async_Manager". *)
val SledgehammerN = "Sledgehammer"

val reconstructor_names = [metisN, smtN]
val plain_metis = Metis (hd partial_type_encs, combsN)
val is_reconstructor = member (op =) reconstructor_names

val is_atp = member (op =) o supported_atps

fun is_atp_of_format is_format ctxt name =
  let val thy = Proof_Context.theory_of ctxt in
    (case try (get_atp thy) name of
      SOME config =>
      exists (fn (_, ((_, format, _, _, _), _)) => is_format format) (#best_slices (config ()) ctxt)
    | NONE => false)
  end

val is_unit_equational_atp = is_atp_of_format (curry (op =) CNF_UEQ)
val is_ho_atp = is_atp_of_format is_format_higher_order

fun remotify_atp_if_supported_and_not_already_remote thy name =
  if String.isPrefix remote_prefix name then
    SOME name
  else
    let val remote_name = remote_prefix ^ name in
      if is_atp thy remote_name then SOME remote_name else NONE
    end

fun remotify_atp_if_not_installed thy name =
  if is_atp thy name andalso is_atp_installed thy name then SOME name
  else remotify_atp_if_supported_and_not_already_remote thy name

fun is_if (@{const_name If}, _) = true
  | is_if _ = false

(* Beware of "if and only if" (which is translated as such) and "If" (which is
   translated to conditional equations). *)
fun is_good_unit_equality T t u =
  T <> @{typ bool} andalso not (exists (exists_Const is_if) [t, u])

fun is_unit_equality (@{const Trueprop} $ t) = is_unit_equality t
  | is_unit_equality (Const (@{const_name all}, _) $ Abs (_, _, t)) =
    is_unit_equality t
  | is_unit_equality (Const (@{const_name All}, _) $ Abs (_, _, t)) =
    is_unit_equality t
  | is_unit_equality (Const (@{const_name "=="}, Type (_, [T, _])) $ t $ u) =
    is_good_unit_equality T t u
  | is_unit_equality (Const (@{const_name HOL.eq}, Type (_ , [T, _])) $ t $ u) =
    is_good_unit_equality T t u
  | is_unit_equality _ = false

fun is_appropriate_prop_of_prover ctxt name =
  if is_unit_equational_atp ctxt name then is_unit_equality else K true

fun supported_provers ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val (remote_provers, local_provers) =
      reconstructor_names @
      sort_strings (supported_atps thy) @
      sort_strings (SMT_Solver.available_solvers_of ctxt)
      |> List.partition (String.isPrefix remote_prefix)
  in
    Output.urgent_message ("Supported provers: " ^
                           commas (local_provers @ remote_provers) ^ ".")
  end

fun kill_provers () = Async_Manager.kill_threads SledgehammerN "prover"
fun running_provers () = Async_Manager.running_threads SledgehammerN "prover"
val messages = Async_Manager.thread_messages SledgehammerN "prover"

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
   preplay : (reconstructor * play_outcome) Lazy.lazy,
   message : reconstructor * play_outcome -> string,
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

fun bunch_of_reconstructors needs_full_types lam_trans =
  if needs_full_types then
    [Metis (full_type_enc, lam_trans false),
     Metis (really_full_type_enc, lam_trans false),
     Metis (full_type_enc, lam_trans true),
     Metis (really_full_type_enc, lam_trans true),
     SMT]
  else
    [Metis (partial_type_enc, lam_trans false),
     Metis (full_type_enc, lam_trans false),
     Metis (no_typesN, lam_trans true),
     Metis (really_full_type_enc, lam_trans true),
     SMT]

fun extract_reconstructor ({type_enc, lam_trans, ...} : params) (Metis (type_enc', lam_trans')) =
    let
      val override_params =
        (if is_none type_enc andalso type_enc' = hd partial_type_encs then []
         else [("type_enc", [hd (unalias_type_enc type_enc')])]) @
        (if is_none lam_trans andalso lam_trans' = default_metis_lam_trans then []
         else [("lam_trans", [lam_trans'])])
    in (metisN, override_params) end
  | extract_reconstructor _ SMT = (smtN, [])

(* based on "Mirabelle.can_apply" and generalized *)
fun timed_apply timeout tac state i =
  let
    val {context = ctxt, facts, goal} = Proof.goal state
    val full_tac = Method.insert_tac facts i THEN tac ctxt i
  in
    TimeLimit.timeLimit timeout (try (Seq.pull o full_tac)) goal
  end

fun tac_of_reconstructor (Metis (type_enc, lam_trans)) = metis_tac [type_enc] lam_trans
  | tac_of_reconstructor SMT = SMT_Solver.smt_tac

fun timed_reconstructor reconstr debug timeout ths =
  timed_apply timeout (silence_reconstructors debug
    #> (fn ctxt => tac_of_reconstructor reconstr ctxt ths))

fun is_fact_chained ((_, (sc, _)), _) = sc = Chained

fun filter_used_facts keep_chained used =
  filter ((member (op =) used o fst) orf (if keep_chained then is_fact_chained else K false))

fun play_one_line_proof mode debug verbose timeout pairs state i preferred reconstrs =
  let
    fun get_preferred reconstrs =
      if member (op =) reconstrs preferred then preferred
      else List.last reconstrs
  in
    if timeout = Time.zeroTime then
      (get_preferred reconstrs, Not_Played)
    else
      let
        val _ = if mode = Minimize then Output.urgent_message "Preplaying proof..." else ()
        val ths = pairs |> sort_wrt (fst o fst) |> map snd
        fun play [] [] = (get_preferred reconstrs, Play_Failed)
          | play timed_outs [] = (get_preferred timed_outs, Play_Timed_Out timeout)
          | play timed_out (reconstr :: reconstrs) =
            let
              val _ =
                if verbose then
                  Output.urgent_message ("Trying \"" ^ string_of_reconstructor reconstr ^
                    "\" for " ^ string_of_time timeout ^ "...")
                else
                  ()
              val timer = Timer.startRealTimer ()
            in
              case timed_reconstructor reconstr debug timeout ths state i of
                SOME (SOME _) => (reconstr, Played (Timer.checkRealTimer timer))
              | _ => play timed_out reconstrs
            end
            handle TimeLimit.TimeOut => play (reconstr :: timed_out) reconstrs
      in
        play [] reconstrs
      end
  end

val canonical_isar_supported_prover = eN

fun isar_supported_prover_of thy name =
  if is_atp thy name then name
  else the_default name (remotify_atp_if_not_installed thy canonical_isar_supported_prover)

(* FIXME: See the analogous logic in the function "maybe_minimize" in
   "sledgehammer_prover_minimize.ML". *)
fun choose_minimize_command thy (params as {isar_proofs, ...}) minimize_command name preplay =
  let
    val maybe_isar_name = name |> isar_proofs = SOME true ? isar_supported_prover_of thy
    val (min_name, override_params) =
      (case preplay of
        (reconstr, Played _) =>
        if isar_proofs = SOME true then (maybe_isar_name, [])
        else extract_reconstructor params reconstr
      | _ => (maybe_isar_name, []))
  in minimize_command override_params min_name end

val max_fact_instances = 10 (* FUDGE *)

fun repair_monomorph_context max_iters best_max_iters max_new_instances best_max_new_instances =
  Config.put Monomorph.max_rounds (max_iters |> the_default best_max_iters)
  #> Config.put Monomorph.max_new_instances
       (max_new_instances |> the_default best_max_new_instances)
  #> Config.put Monomorph.max_thm_instances max_fact_instances

fun run_reconstructor mode name (params as {debug, verbose, timeout, type_enc, lam_trans, ...})
    minimize_command
    ({state, subgoal, subgoal_count, factss = (_, facts) :: _, ...} : prover_problem) =
  let
    val reconstr =
      if name = metisN then
        Metis (type_enc |> the_default (hd partial_type_encs),
               lam_trans |> the_default default_metis_lam_trans)
      else if name = smtN then
        SMT
      else
        raise Fail ("unknown reconstructor: " ^ quote name)
    val used_facts = facts |> map fst
  in
    (case play_one_line_proof (if mode = Minimize then Normal else mode) debug verbose timeout facts
       state subgoal reconstr [reconstr] of
      play as (_, Played time) =>
      {outcome = NONE, used_facts = used_facts, used_from = facts, run_time = time,
       preplay = Lazy.value play,
       message =
         fn play =>
            let
              val (_, override_params) = extract_reconstructor params reconstr
              val one_line_params =
                (play, proof_banner mode name, used_facts, minimize_command override_params name,
                 subgoal, subgoal_count)
              val num_chained = length (#facts (Proof.goal state))
            in
              one_line_proof_text num_chained one_line_params
            end,
       message_tail = ""}
    | play =>
      let
        val failure = (case play of (_, Play_Failed) => GaveUp | _ => TimedOut)
      in
        {outcome = SOME failure, used_facts = [], used_from = [],
         run_time = Time.zeroTime, preplay = Lazy.value play,
         message = fn _ => string_of_atp_failure failure, message_tail = ""}
      end)
  end

end;
