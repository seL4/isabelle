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
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover

val smt_builtins = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_smt_builtins\<close> (K true)
val smt_triggers = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_smt_triggers\<close> (K true)

val is_smt_prover = member (op =) o SMT_Config.available_solvers_of

(* "SMT_Failure.Abnormal_Termination" carries the solver's return code. Until these are sorted out
   properly in the SMT module, we must interpret these here. *)
val z3_failures =
  [(101, OutOfResources),
   (103, MalformedInput),
   (110, MalformedInput),
   (112, TimedOut)]
val unix_failures =
  [(134, Crashed),
   (138, Crashed),
   (139, Crashed)]
val smt_failures = z3_failures @ unix_failures

fun failure_of_smt_failure (SMT_Failure.Counterexample genuine) =
    if genuine then Unprovable else GaveUp
  | failure_of_smt_failure SMT_Failure.Time_Out = TimedOut
  | failure_of_smt_failure (SMT_Failure.Abnormal_Termination code) =
    (case AList.lookup (op =) smt_failures code of
      SOME failure => failure
    | NONE => UnknownError ("Abnormal termination with exit code " ^ string_of_int code))
  | failure_of_smt_failure SMT_Failure.Out_Of_Memory = OutOfResources
  | failure_of_smt_failure (SMT_Failure.Other_Failure s) = UnknownError s

(* FUDGE *)
val smt_max_slices = Attrib.setup_config_int \<^binding>\<open>sledgehammer_smt_max_slices\<close> (K 8)
val smt_slice_fact_frac =
  Attrib.setup_config_real \<^binding>\<open>sledgehammer_smt_slice_fact_frac\<close> (K 0.667)
val smt_slice_time_frac =
  Attrib.setup_config_real \<^binding>\<open>sledgehammer_smt_slice_time_frac\<close> (K 0.333)
val smt_slice_min_secs = Attrib.setup_config_int \<^binding>\<open>sledgehammer_smt_slice_min_secs\<close> (K 3)

val is_boring_builtin_typ =
  not o exists_subtype (member (op =) [\<^typ>\<open>nat\<close>, \<^typ>\<open>int\<close>, HOLogic.realT])

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
                 #> Config.put SMT_Systems.z3_extensions false)
           |> repair_monomorph_context max_mono_iters default_max_mono_iters max_new_mono_instances
                default_max_new_mono_instances

    val state = Proof.map_context (repair_context) state
    val ctxt = Proof.context_of state
    val max_slices = if slice then Config.get ctxt smt_max_slices else 1

    fun do_slice timeout slice outcome0 time_so_far (factss as (fact_filter, facts) :: _) =
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
        val num_facts = length facts
        val _ =
          if debug then
            quote name ^ " slice " ^ string_of_int slice ^ " with " ^ string_of_int num_facts ^
            " fact" ^ plural_s num_facts ^ " for " ^ string_of_time slice_timeout
            |> writeln
          else
            ()
        val birth = Timer.checkRealTimer timer

        val filter_result as {outcome, ...} =
          SMT_Solver.smt_filter ctxt goal facts i slice_timeout
          handle exn =>
            if Exn.is_interrupt exn orelse debug then
              Exn.reraise exn
            else
              {outcome = SOME (SMT_Failure.Other_Failure (Runtime.exn_message exn)),
               fact_ids = NONE, atp_proof = K []}

        val death = Timer.checkRealTimer timer
        val outcome0 = if is_none outcome0 then SOME outcome else outcome0
        val time_so_far = time_so_far + (death - birth)
        val timeout = timeout - Timer.checkRealTimer timer

        val too_many_facts_perhaps =
          (case outcome of
            NONE => false
          | SOME (SMT_Failure.Counterexample _) => false
          | SOME SMT_Failure.Time_Out => slice_timeout <> timeout
          | SOME (SMT_Failure.Abnormal_Termination _) => true (* kind of *)
          | SOME SMT_Failure.Out_Of_Memory => true
          | SOME (SMT_Failure.Other_Failure _) => true)
      in
        if too_many_facts_perhaps andalso slice < max_slices andalso num_facts > 0 andalso
           timeout > Time.zeroTime then
          let
            val new_num_facts =
              Real.ceil (Config.get ctxt smt_slice_fact_frac * Real.fromInt num_facts)
            val factss as (new_fact_filter, _) :: _ =
              factss
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
                |> writeln
              else
                ()
          in
            do_slice timeout (slice + 1) outcome0 time_so_far factss
          end
        else
          {outcome = if is_none outcome then NONE else the outcome0, filter_result = filter_result,
           used_from = facts, run_time = time_so_far}
      end
  in
    do_slice timeout 1 NONE Time.zeroTime
  end

fun run_smt_solver mode name (params as {debug, verbose, isar_proofs, compress, try0, smt_proofs,
      minimize, preplay_timeout, ...})
    ({state, goal, subgoal, subgoal_count, factss, found_proof, ...} : prover_problem) =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val factss = map (apsnd (map (apsnd (Thm.transfer thy)))) factss

    val {outcome, filter_result = {fact_ids, atp_proof, ...}, used_from, run_time} =
      smt_filter_loop name params state goal subgoal factss
    val used_facts =
      (case fact_ids of
        NONE => map fst used_from
      | SOME ids => sort_by fst (map (fst o snd) ids))
    val outcome = Option.map failure_of_smt_failure outcome

    val (preferred_methss, message) =
      (case outcome of
        NONE =>
        let
          val _ = found_proof ();
          val preferred =
            if smt_proofs then
              SMT_Method (if name = "verit" then SMT_Verit "default" else SMT_Default)
            else
              Metis_Method (NONE, NONE);
          val methss = bunches_of_proof_methods ctxt try0 smt_proofs false liftingN;
        in
          ((preferred, methss),
           fn preplay =>
             let
               val _ = if verbose then writeln "Generating proof text..." else ()

               fun isar_params () =
                 (verbose, (NONE, NONE), preplay_timeout, compress, try0, minimize, atp_proof (),
                  goal)

               val one_line_params = (preplay (), proof_banner mode name, subgoal, subgoal_count)
               val num_chained = length (#facts (Proof.goal state))
             in
               proof_text ctxt debug isar_proofs smt_proofs isar_params num_chained one_line_params
             end)
        end
      | SOME failure => ((Auto_Method (* dummy *), []), fn _ => string_of_atp_failure failure))
  in
    {outcome = outcome, used_facts = used_facts, used_from = used_from,
     preferred_methss = preferred_methss, run_time = run_time, message = message}
  end

end;
