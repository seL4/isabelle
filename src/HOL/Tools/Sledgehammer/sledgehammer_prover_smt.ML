(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_smt.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

SMT solvers as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_SMT =
sig
  type stature = ATP_Problem_Generate.stature
  type mode = Sledgehammer_Prover.mode
  type prover = Sledgehammer_Prover.prover

  val smt_builtins : bool Config.T
  val smt_triggers : bool Config.T
  val smt_weights : bool Config.T
  val smt_weight_min_facts : int Config.T
  val smt_min_weight : int Config.T
  val smt_max_weight : int Config.T
  val smt_max_weight_index : int Config.T
  val smt_weight_curve : (int -> int) Unsynchronized.ref
  val smt_max_slices : int Config.T
  val smt_slice_fact_frac : real Config.T
  val smt_slice_time_frac : real Config.T
  val smt_slice_min_secs : int Config.T

  val is_smt_prover : Proof.context -> string -> bool
  val run_smt_solver : mode -> string -> prover
end;

structure Sledgehammer_Prover_SMT : SLEDGEHAMMER_PROVER_SMT =
struct

open ATP_Util
open ATP_Proof
open ATP_Systems
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Prover

val smt_builtins = Attrib.setup_config_bool @{binding sledgehammer_smt_builtins} (K true)
val smt_triggers = Attrib.setup_config_bool @{binding sledgehammer_smt_triggers} (K true)
val smt_weights = Attrib.setup_config_bool @{binding sledgehammer_smt_weights} (K true)
val smt_weight_min_facts =
  Attrib.setup_config_int @{binding sledgehammer_smt_weight_min_facts} (K 20)

fun is_smt_prover ctxt = member (op =) (SMT_Solver.available_solvers_of ctxt)

(* FUDGE *)
val smt_min_weight = Attrib.setup_config_int @{binding sledgehammer_smt_min_weight} (K 0)
val smt_max_weight = Attrib.setup_config_int @{binding sledgehammer_smt_max_weight} (K 10)
val smt_max_weight_index =
  Attrib.setup_config_int @{binding sledgehammer_smt_max_weight_index} (K 200)
val smt_weight_curve = Unsynchronized.ref (fn x : int => x * x)

fun smt_fact_weight ctxt j num_facts =
  if Config.get ctxt smt_weights andalso num_facts >= Config.get ctxt smt_weight_min_facts then
    let
      val min = Config.get ctxt smt_min_weight
      val max = Config.get ctxt smt_max_weight
      val max_index = Config.get ctxt smt_max_weight_index
      val curve = !smt_weight_curve
    in
      SOME (max - (max - min + 1) * curve (Int.max (0, max_index - j - 1)) div curve max_index)
    end
  else
    NONE

fun weight_smt_fact ctxt num_facts ((info, th), j) =
  let val thy = Proof_Context.theory_of ctxt in
    (info, (smt_fact_weight ctxt j num_facts, Thm.transfer thy th (* TODO: needed? *)))
  end

(* "SMT_Failure.Abnormal_Termination" carries the solver's return code. Until these are sorted out
   properly in the SMT module, we must interpret these here. *)
val z3_failures =
  [(101, OutOfResources),
   (103, MalformedInput),
   (110, MalformedInput),
   (112, TimedOut)]
val unix_failures =
  [(138, Crashed),
   (139, Crashed)]
val smt_failures = z3_failures @ unix_failures

fun failure_of_smt_failure (SMT_Failure.Counterexample {is_real_cex, ...}) =
    if is_real_cex then Unprovable else GaveUp
  | failure_of_smt_failure SMT_Failure.Time_Out = TimedOut
  | failure_of_smt_failure (SMT_Failure.Abnormal_Termination code) =
    (case AList.lookup (op =) smt_failures code of
      SOME failure => failure
    | NONE => UnknownError ("Abnormal termination with exit code " ^ string_of_int code ^ "."))
  | failure_of_smt_failure SMT_Failure.Out_Of_Memory = OutOfResources
  | failure_of_smt_failure (SMT_Failure.Other_Failure s) = UnknownError s

(* FUDGE *)
val smt_max_slices = Attrib.setup_config_int @{binding sledgehammer_smt_max_slices} (K 8)
val smt_slice_fact_frac =
  Attrib.setup_config_real @{binding sledgehammer_smt_slice_fact_frac} (K 0.667)
val smt_slice_time_frac =
  Attrib.setup_config_real @{binding sledgehammer_smt_slice_time_frac} (K 0.333)
val smt_slice_min_secs = Attrib.setup_config_int @{binding sledgehammer_smt_slice_min_secs} (K 3)

val is_boring_builtin_typ =
  not o exists_subtype (member (op =) [@{typ nat}, @{typ int}, HOLogic.realT])

fun smt_filter_loop name ({debug, overlord, max_mono_iters, max_new_mono_instances, timeout, slice,
      ...} : params) state goal i =
  let
    fun repair_context ctxt =
      ctxt |> Context.proof_map (SMT_Config.select_solver name)
           |> Config.put SMT_Config.verbose debug
           |> (if overlord then
                 Config.put SMT_Config.debug_files
                   (overlord_file_location_of_prover name |> (fn (path, name) => path ^ "/" ^ name))
               else
                 I)
           |> Config.put SMT_Config.infer_triggers (Config.get ctxt smt_triggers)
           |> not (Config.get ctxt smt_builtins)
              ? (SMT_Builtin.filter_builtins is_boring_builtin_typ
                 #> Config.put SMT_Config.datatypes false)
           |> repair_monomorph_context max_mono_iters default_max_mono_iters max_new_mono_instances
                default_max_new_mono_instances

    val state = Proof.map_context (repair_context) state
    val ctxt = Proof.context_of state
    val max_slices = if slice then Config.get ctxt smt_max_slices else 1

    fun do_slice timeout slice outcome0 time_so_far
        (weighted_factss as (fact_filter, weighted_facts) :: _) =
      let
        val timer = Timer.startRealTimer ()
        val slice_timeout =
          if slice < max_slices then
            let val ms = Time.toMilliseconds timeout in
              Int.min (ms, Int.max (1000 * Config.get ctxt smt_slice_min_secs,
                Real.ceil (Config.get ctxt smt_slice_time_frac * Real.fromInt ms)))
              |> Time.fromMilliseconds
            end
          else
            timeout
        val num_facts = length weighted_facts
        val _ =
          if debug then
            quote name ^ " slice " ^ string_of_int slice ^ " with " ^ string_of_int num_facts ^
            " fact" ^ plural_s num_facts ^ " for " ^ string_of_time slice_timeout
            |> Output.urgent_message
          else
            ()
        val birth = Timer.checkRealTimer timer

        val (outcome, used_facts) =
          SMT_Solver.smt_filter_preprocess ctxt [] goal weighted_facts i
          |> SMT_Solver.smt_filter_apply slice_timeout
          |> (fn {outcome, used_facts} => (outcome, used_facts))
          handle exn =>
            if Exn.is_interrupt exn then reraise exn
            else (Runtime.exn_message exn |> SMT_Failure.Other_Failure |> SOME, [])

        val death = Timer.checkRealTimer timer
        val outcome0 = if is_none outcome0 then SOME outcome else outcome0
        val time_so_far = Time.+ (time_so_far, Time.- (death, birth))

        val too_many_facts_perhaps =
          (case outcome of
            NONE => false
          | SOME (SMT_Failure.Counterexample _) => false
          | SOME SMT_Failure.Time_Out => slice_timeout <> timeout
          | SOME (SMT_Failure.Abnormal_Termination _) => true (* kind of *)
          | SOME SMT_Failure.Out_Of_Memory => true
          | SOME (SMT_Failure.Other_Failure _) => true)

        val timeout = Time.- (timeout, Timer.checkRealTimer timer)
      in
        if too_many_facts_perhaps andalso slice < max_slices andalso num_facts > 0 andalso
           Time.> (timeout, Time.zeroTime) then
          let
            val new_num_facts =
              Real.ceil (Config.get ctxt smt_slice_fact_frac * Real.fromInt num_facts)
            val weighted_factss as (new_fact_filter, _) :: _ =
              weighted_factss
              |> (fn (x :: xs) => xs @ [x])
              |> app_hd (apsnd (take new_num_facts))
            val show_filter = fact_filter <> new_fact_filter

            fun num_of_facts fact_filter num_facts =
              string_of_int num_facts ^ (if show_filter then " " ^ quote fact_filter else "") ^
              " fact" ^ plural_s num_facts

            val _ =
              if debug then
                quote name ^ " invoked with " ^
                num_of_facts fact_filter num_facts ^ ": " ^
                string_of_atp_failure (failure_of_smt_failure (the outcome)) ^
                " Retrying with " ^ num_of_facts new_fact_filter new_num_facts ^
                "..."
                |> Output.urgent_message
              else
                ()
          in
            do_slice timeout (slice + 1) outcome0 time_so_far weighted_factss
          end
        else
          {outcome = if is_none outcome then NONE else the outcome0, used_facts = used_facts,
           used_from = map (apsnd snd) weighted_facts, run_time = time_so_far}
      end
  in
    do_slice timeout 1 NONE Time.zeroTime
  end

fun run_smt_solver mode name (params as {verbose, smt_proofs, preplay_timeout, ...})
    minimize_command ({state, goal, subgoal, subgoal_count, factss, ...} : prover_problem) =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    fun weight_facts facts =
      let val num_facts = length facts in
        map (weight_smt_fact ctxt num_facts) (facts ~~ (0 upto num_facts - 1))
      end

    val weighted_factss = factss |> map (apsnd weight_facts)
    val {outcome, used_facts = used_pairs, used_from, run_time} =
      smt_filter_loop name params state goal subgoal weighted_factss
    val used_facts = used_pairs |> map fst
    val outcome = outcome |> Option.map failure_of_smt_failure

    val (preplay, message, message_tail) =
      (case outcome of
        NONE =>
        (Lazy.lazy (fn () =>
           play_one_line_proof mode verbose preplay_timeout used_pairs state subgoal
             SMT2_Method (bunch_of_proof_methods (smt_proofs <> SOME false) false liftingN)),
         fn preplay =>
            let
              val one_line_params =
                (preplay, proof_banner mode name, used_facts,
                 choose_minimize_command thy params minimize_command name preplay, subgoal,
                 subgoal_count)
              val num_chained = length (#facts (Proof.goal state))
            in
              one_line_proof_text ctxt num_chained one_line_params
            end,
         if verbose then "\nSMT solver real CPU time: " ^ string_of_time run_time ^ "." else "")
      | SOME failure =>
        (Lazy.value (Metis_Method (NONE, NONE), Play_Failed),
         fn _ => string_of_atp_failure failure, ""))
  in
    {outcome = outcome, used_facts = used_facts, used_from = used_from, run_time = run_time,
     preplay = preplay, message = message, message_tail = message_tail}
  end

end;
