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

  val is_smt_prover : Proof.context -> string -> bool
  val is_smt_prover_installed : Proof.context -> string -> bool
  val run_smt_solver : mode -> string -> prover

  val smts : Proof.context -> string list
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

val smts = sort_strings o SMT_Config.all_solvers_of

val is_smt_prover = member (op =) o smts
val is_smt_prover_installed = member (op =) o SMT_Config.available_solvers_of

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

val is_boring_builtin_typ =
  not o exists_subtype (member (op =) [\<^typ>\<open>nat\<close>, \<^typ>\<open>int\<close>, HOLogic.realT])

fun smt_filter name ({debug, overlord, max_mono_iters, max_new_mono_instances, type_enc, slices,
    timeout, ...} : params) memoize_fun_call state goal i slice_size facts options =
  let
    val run_timeout = slice_timeout slice_size slices timeout
    val (higher_order, nat_as_int) =
      (case type_enc of
        SOME s => (SOME (String.isSubstring "native_higher" s), SOME (String.isSubstring "arith" s))
      | NONE => (NONE, NONE))
    fun repair_context ctxt = ctxt
      |> Context.proof_map (SMT_Config.select_solver name)
      |> (case higher_order of
           SOME higher_order => Config.put SMT_Config.higher_order higher_order
         | NONE => I)
      |> (case nat_as_int of
           SOME nat_as_int => Config.put SMT_Config.nat_as_int nat_as_int
         | NONE => I)
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

    val timer = Timer.startRealTimer ()
    val birth = Timer.checkRealTimer timer

    val filter_result as {outcome, ...} =
      \<^try>\<open>SMT_Solver.smt_filter ctxt goal facts i run_timeout memoize_fun_call options
        catch exn =>
          {outcome = SOME (SMT_Failure.Other_Failure (Runtime.exn_message exn)), fact_ids = NONE,
           atp_proof = K []}\<close>

    val death = Timer.checkRealTimer timer
    val run_time = death - birth
  in
    {outcome = outcome, filter_result = filter_result, used_from = facts, run_time = run_time}
  end

fun run_smt_solver mode name
    (params as {debug, verbose, isar_proofs, compress, try0, smt_proofs, minimize, preplay_timeout,
      ...} : params)
    ({state, goal, subgoal, subgoal_count, factss, found_something, memoize_fun_call,
      ...} : prover_problem)
    slice =
  let
    val (basic_slice as (slice_size, _, _, _, _), SMT_Slice options) = slice
    val facts = facts_of_basic_slice basic_slice factss
    val ctxt = Proof.context_of state

    val {outcome, filter_result = {fact_ids, atp_proof, ...}, used_from, run_time} =
      smt_filter name params memoize_fun_call state goal subgoal slice_size facts options
    val used_facts =
      (case fact_ids of
        NONE => map fst used_from
      | SOME ids => sort_by fst (map (fst o snd) ids))
    val outcome = Option.map failure_of_smt_failure outcome

    val (preferred_methss, message) =
      (case outcome of
        NONE =>
        let
          val _ = found_something name;
          val preferred =
            if smt_proofs then
              SMT_Method (if name = "z3" then SMT_Z3 else SMT_Verit "default")
            else
              Metis_Method (NONE, NONE, []);
          val methss =
            if try0 then
              bunches_of_proof_methods ctxt smt_proofs false true
            else if smt_proofs then
              bunches_of_smt_methods ctxt
            else
              bunches_of_metis_methods ctxt false true
        in
          ((preferred, methss),
           fn preplay =>
             let
               val _ = if verbose then writeln "Generating proof text..." else ()

               fun isar_params () =
                 (verbose, (NONE, NONE, []), preplay_timeout, compress, try0, minimize,
                  atp_proof (), goal)

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
