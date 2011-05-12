(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_provers.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Generic prover abstraction for Sledgehammer.
*)

signature SLEDGEHAMMER_PROVERS =
sig
  type failure = ATP_Proof.failure
  type locality = Sledgehammer_Filter.locality
  type relevance_fudge = Sledgehammer_Filter.relevance_fudge
  type translated_formula = Sledgehammer_ATP_Translate.translated_formula
  type type_system = Sledgehammer_ATP_Translate.type_system
  type minimize_command = Sledgehammer_ATP_Reconstruct.minimize_command

  datatype rich_type_system =
    Dumb_Type_Sys of type_system |
    Smart_Type_Sys of bool

  type params =
    {debug: bool,
     verbose: bool,
     overlord: bool,
     blocking: bool,
     provers: string list,
     type_sys: rich_type_system,
     relevance_thresholds: real * real,
     max_relevant: int option,
     max_mono_iters: int,
     max_mono_instances: int,
     explicit_apply: bool,
     isar_proof: bool,
     isar_shrink_factor: int,
     slicing: bool,
     timeout: Time.time,
     expect: string}

  datatype prover_fact =
    Untranslated_Fact of (string * locality) * thm |
    SMT_Weighted_Fact of (string * locality) * (int option * thm)

  type prover_problem =
    {state: Proof.state,
     goal: thm,
     subgoal: int,
     subgoal_count: int,
     facts: prover_fact list,
     smt_filter: (string * locality) SMT_Solver.smt_filter_data option}

  type prover_result =
    {outcome: failure option,
     used_facts: (string * locality) list,
     run_time_in_msecs: int option,
     message: string}

  type prover = params -> minimize_command -> prover_problem -> prover_result

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
  val das_Tool : string
  val select_smt_solver : string -> Proof.context -> Proof.context
  val is_smt_prover : Proof.context -> string -> bool
  val is_prover_supported : Proof.context -> string -> bool
  val is_prover_installed : Proof.context -> string -> bool
  val default_max_relevant_for_prover : Proof.context -> bool -> string -> int
  val is_built_in_const_for_prover :
    Proof.context -> string -> string * typ -> term list -> bool * term list
  val atp_relevance_fudge : relevance_fudge
  val smt_relevance_fudge : relevance_fudge
  val relevance_fudge_for_prover : Proof.context -> string -> relevance_fudge
  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_run_time : bool Config.T
  val weight_smt_fact :
    Proof.context -> int -> ((string * locality) * thm) * int
    -> (string * locality) * (int option * thm)
  val untranslated_fact : prover_fact -> (string * locality) * thm
  val smt_weighted_fact :
    Proof.context -> int -> prover_fact * int
    -> (string * locality) * (int option * thm)
  val supported_provers : Proof.context -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
  val get_prover : Proof.context -> bool -> string -> prover
end;

structure Sledgehammer_Provers : SLEDGEHAMMER_PROVERS =
struct

open ATP_Problem
open ATP_Proof
open ATP_Systems
open Metis_Translate
open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_ATP_Translate
open Sledgehammer_ATP_Reconstruct

(** The Sledgehammer **)

(* Identifier to distinguish Sledgehammer from other tools using
   "Async_Manager". *)
val das_Tool = "Sledgehammer"

val select_smt_solver =
  Context.proof_map o SMT_Config.select_solver

fun is_smt_prover ctxt name =
  member (op =) (SMT_Solver.available_solvers_of ctxt) name

fun is_prover_supported ctxt name =
  let val thy = Proof_Context.theory_of ctxt in
    is_smt_prover ctxt name orelse member (op =) (supported_atps thy) name
  end

fun is_prover_installed ctxt =
  is_smt_prover ctxt orf is_atp_installed (Proof_Context.theory_of ctxt)

fun get_slices slicing slices =
  (0 upto length slices - 1) ~~ slices |> not slicing ? (List.last #> single)

fun default_max_relevant_for_prover ctxt slicing name =
  let val thy = Proof_Context.theory_of ctxt in
    if is_smt_prover ctxt name then
      SMT_Solver.default_max_relevant ctxt name
    else
      fold (Integer.max o fst o snd o snd o snd)
           (get_slices slicing (#best_slices (get_atp thy name) ctxt)) 0
  end

(* These are either simplified away by "Meson.presimplify" (most of the time) or
   handled specially via "fFalse", "fTrue", ..., "fequal". *)
val atp_irrelevant_consts =
  [@{const_name False}, @{const_name True}, @{const_name Not},
   @{const_name conj}, @{const_name disj}, @{const_name implies},
   @{const_name HOL.eq}, @{const_name If}, @{const_name Let}]

fun is_built_in_const_for_prover ctxt name =
  if is_smt_prover ctxt name then
    let val ctxt = ctxt |> select_smt_solver name in
      fn x => fn ts =>
         if SMT_Builtin.is_builtin_num_ext ctxt (list_comb (Const x, ts)) then
           (true, [])
         else if SMT_Builtin.is_builtin_fun_ext ctxt x ts then
           (true, ts)
         else
           (false, ts)
    end
  else
    fn (s, _) => fn ts => (member (op =) atp_irrelevant_consts s, ts)

(* FUDGE *)
val atp_relevance_fudge =
  {allow_ext = true,
   local_const_multiplier = 1.5,
   worse_irrel_freq = 100.0,
   higher_order_irrel_weight = 1.05,
   abs_rel_weight = 0.5,
   abs_irrel_weight = 2.0,
   skolem_irrel_weight = 0.75,
   theory_const_rel_weight = 0.5,
   theory_const_irrel_weight = 0.25,
   intro_bonus = 0.15,
   elim_bonus = 0.15,
   simp_bonus = 0.15,
   local_bonus = 0.55,
   assum_bonus = 1.05,
   chained_bonus = 1.5,
   max_imperfect = 11.5,
   max_imperfect_exp = 1.0,
   threshold_divisor = 2.0,
   ridiculous_threshold = 0.01}

(* FUDGE (FIXME) *)
val smt_relevance_fudge =
  {allow_ext = false,
   local_const_multiplier = #local_const_multiplier atp_relevance_fudge,
   worse_irrel_freq = #worse_irrel_freq atp_relevance_fudge,
   higher_order_irrel_weight = #higher_order_irrel_weight atp_relevance_fudge,
   abs_rel_weight = #abs_rel_weight atp_relevance_fudge,
   abs_irrel_weight = #abs_irrel_weight atp_relevance_fudge,
   skolem_irrel_weight = #skolem_irrel_weight atp_relevance_fudge,
   theory_const_rel_weight = #theory_const_rel_weight atp_relevance_fudge,
   theory_const_irrel_weight = #theory_const_irrel_weight atp_relevance_fudge,
   intro_bonus = #intro_bonus atp_relevance_fudge,
   elim_bonus = #elim_bonus atp_relevance_fudge,
   simp_bonus = #simp_bonus atp_relevance_fudge,
   local_bonus = #local_bonus atp_relevance_fudge,
   assum_bonus = #assum_bonus atp_relevance_fudge,
   chained_bonus = #chained_bonus atp_relevance_fudge,
   max_imperfect = #max_imperfect atp_relevance_fudge,
   max_imperfect_exp = #max_imperfect_exp atp_relevance_fudge,
   threshold_divisor = #threshold_divisor atp_relevance_fudge,
   ridiculous_threshold = #ridiculous_threshold atp_relevance_fudge}

fun relevance_fudge_for_prover ctxt name =
  if is_smt_prover ctxt name then smt_relevance_fudge else atp_relevance_fudge

fun supported_provers ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val (remote_provers, local_provers) =
      sort_strings (supported_atps thy) @
      sort_strings (SMT_Solver.available_solvers_of ctxt)
      |> List.partition (String.isPrefix remote_prefix)
  in
    Output.urgent_message ("Supported provers: " ^
                           commas (local_provers @ remote_provers) ^ ".")
  end

fun kill_provers () = Async_Manager.kill_threads das_Tool "provers"
fun running_provers () = Async_Manager.running_threads das_Tool "provers"
val messages = Async_Manager.thread_messages das_Tool "prover"

(** problems, results, ATPs, etc. **)

datatype rich_type_system =
  Dumb_Type_Sys of type_system |
  Smart_Type_Sys of bool

type params =
  {debug: bool,
   verbose: bool,
   overlord: bool,
   blocking: bool,
   provers: string list,
   type_sys: rich_type_system,
   relevance_thresholds: real * real,
   max_relevant: int option,
   max_mono_iters: int,
   max_mono_instances: int,
   explicit_apply: bool,
   isar_proof: bool,
   isar_shrink_factor: int,
   slicing: bool,
   timeout: Time.time,
   expect: string}

datatype prover_fact =
  Untranslated_Fact of (string * locality) * thm |
  SMT_Weighted_Fact of (string * locality) * (int option * thm)

type prover_problem =
  {state: Proof.state,
   goal: thm,
   subgoal: int,
   subgoal_count: int,
   facts: prover_fact list,
   smt_filter: (string * locality) SMT_Solver.smt_filter_data option}

type prover_result =
  {outcome: failure option,
   message: string,
   used_facts: (string * locality) list,
   run_time_in_msecs: int option}

type prover = params -> minimize_command -> prover_problem -> prover_result

(* configuration attributes *)

val dest_dir =
  Attrib.setup_config_string @{binding sledgehammer_dest_dir} (K "")
  (* Empty string means create files in Isabelle's temporary files directory. *)

val problem_prefix =
  Attrib.setup_config_string @{binding sledgehammer_problem_prefix} (K "prob")

val measure_run_time =
  Attrib.setup_config_bool @{binding sledgehammer_measure_run_time} (K false)

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path)

fun proof_banner auto =
  if auto then "Auto Sledgehammer found a proof" else "Try this command"

val smt_triggers =
  Attrib.setup_config_bool @{binding sledgehammer_smt_triggers} (K true)
val smt_weights =
  Attrib.setup_config_bool @{binding sledgehammer_smt_weights} (K true)
val smt_weight_min_facts =
  Attrib.setup_config_int @{binding sledgehammer_smt_weight_min_facts} (K 20)

(* FUDGE *)
val smt_min_weight =
  Attrib.setup_config_int @{binding sledgehammer_smt_min_weight} (K 0)
val smt_max_weight =
  Attrib.setup_config_int @{binding sledgehammer_smt_max_weight} (K 10)
val smt_max_weight_index =
  Attrib.setup_config_int @{binding sledgehammer_smt_max_weight_index} (K 200)
val smt_weight_curve = Unsynchronized.ref (fn x : int => x * x)

fun smt_fact_weight ctxt j num_facts =
  if Config.get ctxt smt_weights andalso
     num_facts >= Config.get ctxt smt_weight_min_facts then
    let
      val min = Config.get ctxt smt_min_weight
      val max = Config.get ctxt smt_max_weight
      val max_index = Config.get ctxt smt_max_weight_index
      val curve = !smt_weight_curve
    in
      SOME (max - (max - min + 1) * curve (Int.max (0, max_index - j - 1))
            div curve max_index)
    end
  else
    NONE

fun weight_smt_fact ctxt num_facts ((info, th), j) =
  let val thy = Proof_Context.theory_of ctxt in
    (info, (smt_fact_weight ctxt j num_facts, th |> Thm.transfer thy))
  end

fun untranslated_fact (Untranslated_Fact p) = p
  | untranslated_fact (SMT_Weighted_Fact (info, (_, th))) = (info, th)
fun atp_translated_fact ctxt fact =
  translate_atp_fact ctxt false (untranslated_fact fact)
fun smt_weighted_fact _ _ (SMT_Weighted_Fact p, _) = p
  | smt_weighted_fact ctxt num_facts (fact, j) =
    (untranslated_fact fact, j) |> weight_smt_fact ctxt num_facts

fun overlord_file_location_for_prover prover =
  (getenv "ISABELLE_HOME_USER", "prob_" ^ prover)


(* generic TPTP-based ATPs *)

fun int_opt_add (SOME m) (SOME n) = SOME (m + n)
  | int_opt_add _ _ = NONE

val atp_blacklist_max_iters = 10
(* Important messages are important but not so important that users want to see
   them each time. *)
val atp_important_message_keep_quotient = 10

val fallback_best_type_systems =
  [Preds (Polymorphic, Const_Arg_Types),
   Preds (Mangled_Monomorphic, Nonmonotonic_Types)]

fun adjust_dumb_type_sys formats (Simple_Types level) =
    if member (op =) formats Tff then (Tff, Simple_Types level)
    else (Fof, Preds (Mangled_Monomorphic, level))
  | adjust_dumb_type_sys formats type_sys = (hd formats, type_sys)
fun determine_format_and_type_sys _ formats (Dumb_Type_Sys type_sys) =
    adjust_dumb_type_sys formats type_sys
  | determine_format_and_type_sys best_type_systems formats
                                  (Smart_Type_Sys full_types) =
    map type_sys_from_string best_type_systems @ fallback_best_type_systems
    |> find_first (if full_types then is_type_sys_virtually_sound else K true)
    |> the |> adjust_dumb_type_sys formats

fun repair_smt_monomorph_context debug max_mono_iters max_mono_instances
                                 num_facts =
  Config.put SMT_Config.verbose debug
  #> Config.put SMT_Config.monomorph_full false
  #> Config.put SMT_Config.monomorph_limit max_mono_iters
  #> Config.put SMT_Config.monomorph_instances
                (Int.max (max_mono_instances, num_facts))

fun run_atp auto name
        ({exec, required_execs, arguments, proof_delims, known_failures,
          conj_sym_kind, prem_kind, formats, best_slices, ...} : atp_config)
        ({debug, verbose, overlord, type_sys, max_relevant, max_mono_iters,
          max_mono_instances, explicit_apply, isar_proof, isar_shrink_factor,
          slicing, timeout, ...} : params)
        minimize_command ({state, goal, subgoal, facts, ...} : prover_problem) =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val (_, hyp_ts, concl_t) = strip_subgoal goal subgoal
    val (dest_dir, problem_prefix) =
      if overlord then overlord_file_location_for_prover name
      else (Config.get ctxt dest_dir, Config.get ctxt problem_prefix)
    val problem_file_name =
      Path.basic (problem_prefix ^ (if overlord then "" else serial_string ()) ^
                  "_" ^ string_of_int subgoal)
    val problem_path_name =
      if dest_dir = "" then
        File.tmp_path problem_file_name
      else if File.exists (Path.explode dest_dir) then
        Path.append (Path.explode dest_dir) problem_file_name
      else
        error ("No such directory: " ^ quote dest_dir ^ ".")
    val measure_run_time = verbose orelse Config.get ctxt measure_run_time
    val command = Path.explode (getenv (fst exec) ^ "/" ^ snd exec)
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n")
        val (output, t) = s |> split |> split_last |> apfst cat_lines
        fun as_num f = f >> (fst o read_int)
        val num = as_num (Scan.many1 Symbol.is_ascii_digit)
        val digit = Scan.one Symbol.is_ascii_digit
        val num3 = as_num (digit ::: digit ::: (digit >> single))
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b)
        val as_time = Scan.read Symbol.stopper time o raw_explode
      in (output, as_time t) end
    fun run_on prob_file =
      case filter (curry (op =) "" o getenv o fst) (exec :: required_execs) of
        (home_var, _) :: _ =>
        error ("The environment variable " ^ quote home_var ^ " is not set.")
      | [] =>
        if File.exists command then
          let
            (* If slicing is disabled, we expand the last slice to fill the
               entire time available. *)
            val actual_slices = get_slices slicing (best_slices ctxt)
            val num_actual_slices = length actual_slices
            fun monomorphize_facts facts =
              let
                val facts = facts |> map untranslated_fact
                (* pseudo-theorem involving the same constants as the subgoal *)
                val subgoal_th =
                  Logic.list_implies (hyp_ts, concl_t)
                  |> Skip_Proof.make_thm thy
                val indexed_facts =
                  (~1, subgoal_th) :: (0 upto length facts - 1 ~~ map snd facts)
              in
                ctxt |> repair_smt_monomorph_context debug max_mono_iters
                            max_mono_instances (length facts)
                     |> SMT_Monomorph.monomorph indexed_facts
                     |> fst |> sort (int_ord o pairself fst)
                     |> filter_out (curry (op =) ~1 o fst)
                     |> map (Untranslated_Fact o apfst (fst o nth facts))
              end
            fun run_slice blacklist (slice, (time_frac, (complete,
                                       (best_max_relevant, best_type_systems))))
                          time_left =
              let
                val num_facts =
                  length facts |> is_none max_relevant
                                  ? Integer.min best_max_relevant
                val (format, type_sys) =
                  determine_format_and_type_sys best_type_systems formats type_sys
                val fairly_sound = is_type_sys_fairly_sound type_sys
                val facts =
                  facts |> not fairly_sound
                           ? filter_out (is_dangerous_term o prop_of o snd
                                         o untranslated_fact)
                        |> take num_facts
                        |> not (null blacklist)
                           ? filter_out (member (op =) blacklist o fst
                                         o untranslated_fact)
                        |> polymorphism_of_type_sys type_sys <> Polymorphic
                           ? monomorphize_facts
                        |> map (atp_translated_fact ctxt)
                val real_ms = Real.fromInt o Time.toMilliseconds
                val slice_timeout =
                  ((real_ms time_left
                    |> (if slice < num_actual_slices - 1 then
                          curry Real.min (time_frac * real_ms timeout)
                        else
                          I))
                   * 0.001) |> seconds
                val _ =
                  if debug then
                    quote name ^ " slice #" ^ string_of_int (slice + 1) ^
                    " with " ^ string_of_int num_facts ^ " fact" ^
                    plural_s num_facts ^ " for " ^
                    string_from_time slice_timeout ^ "..."
                    |> Output.urgent_message
                  else
                    ()
                val (atp_problem, pool, conjecture_offset, facts_offset,
                     fact_names) =
                  prepare_atp_problem ctxt conj_sym_kind prem_kind type_sys
                                      explicit_apply hyp_ts concl_t facts
                fun weights () = atp_problem_weights atp_problem
                val core =
                  File.shell_path command ^ " " ^
                  arguments ctxt slice slice_timeout weights ^ " " ^
                  File.shell_path prob_file
                val command =
                  (if measure_run_time then
                     "TIMEFORMAT='%3R'; { time " ^ core ^ " ; }"
                   else
                     "exec " ^ core) ^ " 2>&1"
                val _ =
                  atp_problem
                  |> tptp_strings_for_atp_problem format
                  |> cons ("% " ^ command ^ "\n")
                  |> File.write_list prob_file
                val conjecture_shape =
                  conjecture_offset + 1
                    upto conjecture_offset + length hyp_ts + 1
                  |> map single
                val ((output, msecs), res_code) =
                  bash_output command
                  |>> (if overlord then
                         prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n")
                       else
                         I)
                  |>> (if measure_run_time then split_time else rpair NONE)
                val (atp_proof, outcome) =
                  extract_tstplike_proof_and_outcome debug verbose complete
                      res_code proof_delims known_failures output
                  |>> atp_proof_from_tstplike_proof
                val (conjecture_shape, facts_offset, fact_names) =
                  if is_none outcome then
                    repair_conjecture_shape_and_fact_names type_sys output
                        conjecture_shape facts_offset fact_names
                  else
                    (* don't bother repairing *)
                    (conjecture_shape, facts_offset, fact_names)
                val outcome =
                  case outcome of
                    NONE =>
                    if is_unsound_proof type_sys conjecture_shape facts_offset
                                        fact_names atp_proof then
                      SOME (UnsoundProof (is_type_sys_virtually_sound type_sys))
                    else
                      NONE
                  | SOME Unprovable =>
                    if null blacklist then outcome
                    else SOME IncompleteUnprovable
                  | _ => outcome
              in
                ((pool, conjecture_shape, facts_offset, fact_names),
                 (output, msecs, type_sys, atp_proof, outcome))
              end
            val timer = Timer.startRealTimer ()
            fun maybe_run_slice blacklist slice
                                (result as (_, (_, msecs0, _, _, SOME _))) =
                let
                  val time_left = Time.- (timeout, Timer.checkRealTimer timer)
                in
                  if Time.<= (time_left, Time.zeroTime) then
                    result
                  else
                    (run_slice blacklist slice time_left
                     |> (fn (stuff, (output, msecs, type_sys, atp_proof,
                                     outcome)) =>
                            (stuff, (output, int_opt_add msecs0 msecs, type_sys,
                                     atp_proof, outcome))))
                end
              | maybe_run_slice _ _ result = result
            fun maybe_blacklist_facts_and_retry iter blacklist
                    (result as ((_, _, facts_offset, fact_names),
                                (_, _, type_sys, atp_proof,
                                 SOME (UnsoundProof false)))) =
                (case used_facts_in_atp_proof type_sys facts_offset fact_names
                                              atp_proof of
                   [] => result
                 | new_baddies =>
                   let val blacklist = new_baddies @ blacklist in
                     result
                     |> maybe_run_slice blacklist (List.last actual_slices)
                     |> iter < atp_blacklist_max_iters
                        ? maybe_blacklist_facts_and_retry (iter + 1) blacklist
                   end)
              | maybe_blacklist_facts_and_retry _ _ result = result
          in
            ((Symtab.empty, [], 0, Vector.fromList []),
             ("", SOME 0, hd fallback_best_type_systems, [],
              SOME InternalError))
            |> fold (maybe_run_slice []) actual_slices
               (* The ATP found an unsound proof? Automatically try again
                  without the offending facts! *)
            |> maybe_blacklist_facts_and_retry 0 []
          end
        else
          error ("Bad executable: " ^ Path.print command ^ ".")

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup prob_file =
      if dest_dir = "" then try File.rm prob_file else NONE
    fun export prob_file (_, (output, _, _, _, _)) =
      if dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode prob_file ^ "_proof")) output
    val ((pool, conjecture_shape, facts_offset, fact_names),
         (output, msecs, type_sys, atp_proof, outcome)) =
      with_path cleanup export run_on problem_path_name
    val important_message =
      if not auto andalso
         random_range 0 (atp_important_message_keep_quotient - 1) = 0 then
        extract_important_message output
      else
        ""
    fun append_to_message message =
      message ^
      (if verbose then
         "\nATP real CPU time: " ^
         string_from_time (Time.fromMilliseconds (the msecs)) ^ "."
       else
         "") ^
      (if important_message <> "" then
         "\n\nImportant message from Dr. Geoff Sutcliffe:\n" ^ important_message
       else
         "")
    val isar_params = (ctxt, debug, isar_shrink_factor, pool, conjecture_shape)
    val metis_params =
      (proof_banner auto, minimize_command, type_sys, atp_proof, facts_offset,
       fact_names, goal, subgoal)
    val (outcome, (message, used_facts)) =
      case outcome of
        NONE =>
        (NONE, proof_text isar_proof isar_params metis_params
               |>> append_to_message)
      | SOME ProofMissing =>
        (NONE, metis_proof_text metis_params |>> append_to_message)
      | SOME failure => (outcome, (string_for_failure failure, []))
  in
    {outcome = outcome, message = message, used_facts = used_facts,
     run_time_in_msecs = msecs}
  end

(* "SMT_Failure.Abnormal_Termination" carries the solver's return code. Until
   these are sorted out properly in the SMT module, we have to interpret these
   ourselves. *)
val remote_smt_failures =
  [(22, CantConnect),
   (2, NoLibwwwPerl)]
val z3_wrapper_failures =
  [(10, NoRealZ3),
   (11, InternalError),
   (12, InternalError),
   (13, InternalError)]
val z3_failures =
  [(101, OutOfResources),
   (103, MalformedInput),
   (110, MalformedInput)]
val unix_failures =
  [(139, Crashed)]
val smt_failures =
  remote_smt_failures @ z3_wrapper_failures @ z3_failures @ unix_failures

fun failure_from_smt_failure (SMT_Failure.Counterexample {is_real_cex, ...}) =
    if is_real_cex then Unprovable else IncompleteUnprovable
  | failure_from_smt_failure SMT_Failure.Time_Out = TimedOut
  | failure_from_smt_failure (SMT_Failure.Abnormal_Termination code) =
    (case AList.lookup (op =) smt_failures code of
       SOME failure => failure
     | NONE => UnknownError ("Abnormal termination with exit code " ^
                             string_of_int code ^ "."))
  | failure_from_smt_failure SMT_Failure.Out_Of_Memory = OutOfResources
  | failure_from_smt_failure (SMT_Failure.Other_Failure msg) =
    UnknownError msg

(* FUDGE *)
val smt_max_slices =
  Attrib.setup_config_int @{binding sledgehammer_smt_max_slices} (K 8)
val smt_slice_fact_frac =
  Attrib.setup_config_real @{binding sledgehammer_smt_slice_fact_frac} (K 0.5)
val smt_slice_time_frac =
  Attrib.setup_config_real @{binding sledgehammer_smt_slice_time_frac} (K 0.5)
val smt_slice_min_secs =
  Attrib.setup_config_int @{binding sledgehammer_smt_slice_min_secs} (K 5)

fun smt_filter_loop ctxt name
                    ({debug, verbose, overlord, max_mono_iters,
                      max_mono_instances, timeout, slicing, ...} : params)
                    state i smt_filter =
  let
    val max_slices = if slicing then Config.get ctxt smt_max_slices else 1
    val repair_context =
          select_smt_solver name
          #> (if overlord then
                Config.put SMT_Config.debug_files
                           (overlord_file_location_for_prover name
                            |> (fn (path, name) => path ^ "/" ^ name))
              else
                I)
          #> Config.put SMT_Config.infer_triggers (Config.get ctxt smt_triggers)
    val state = state |> Proof.map_context repair_context
    fun do_slice timeout slice outcome0 time_so_far facts =
      let
        val timer = Timer.startRealTimer ()
        val state =
          state |> Proof.map_context
                       (repair_smt_monomorph_context debug max_mono_iters
                            max_mono_instances (length facts))
        val ms = timeout |> Time.toMilliseconds
        val slice_timeout =
          if slice < max_slices then
            Int.min (ms,
                Int.max (1000 * Config.get ctxt smt_slice_min_secs,
                    Real.ceil (Config.get ctxt smt_slice_time_frac
                               * Real.fromInt ms)))
            |> Time.fromMilliseconds
          else
            timeout
        val num_facts = length facts
        val _ =
          if debug then
            quote name ^ " slice " ^ string_of_int slice ^ " with " ^
            string_of_int num_facts ^ " fact" ^ plural_s num_facts ^ " for " ^
            string_from_time slice_timeout ^ "..."
            |> Output.urgent_message
          else
            ()
        val birth = Timer.checkRealTimer timer
        val _ =
          if debug then Output.urgent_message "Invoking SMT solver..." else ()
        val (outcome, used_facts) =
          (case (slice, smt_filter) of
             (1, SOME head) => head |> apsnd (apsnd repair_context)
           | _ => SMT_Solver.smt_filter_preprocess state facts i)
          |> SMT_Solver.smt_filter_apply slice_timeout
          |> (fn {outcome, used_facts} => (outcome, used_facts))
          handle exn => if Exn.is_interrupt exn then
                          reraise exn
                        else
                          (ML_Compiler.exn_message exn
                           |> SMT_Failure.Other_Failure |> SOME, [])
        val death = Timer.checkRealTimer timer
        val outcome0 = if is_none outcome0 then SOME outcome else outcome0
        val time_so_far = Time.+ (time_so_far, Time.- (death, birth))
        val too_many_facts_perhaps =
          case outcome of
            NONE => false
          | SOME (SMT_Failure.Counterexample _) => false
          | SOME SMT_Failure.Time_Out => slice_timeout <> timeout
          | SOME (SMT_Failure.Abnormal_Termination _) => true (* kind of *)
          | SOME SMT_Failure.Out_Of_Memory => true
          | SOME (SMT_Failure.Other_Failure _) => true
        val timeout = Time.- (timeout, Timer.checkRealTimer timer)
      in
        if too_many_facts_perhaps andalso slice < max_slices andalso
           num_facts > 0 andalso Time.> (timeout, Time.zeroTime) then
          let
            val new_num_facts =
              Real.ceil (Config.get ctxt smt_slice_fact_frac
                         * Real.fromInt num_facts)
            val _ =
              if verbose andalso is_some outcome then
                quote name ^ " invoked with " ^ string_of_int num_facts ^
                " fact" ^ plural_s num_facts ^ ": " ^
                string_for_failure (failure_from_smt_failure (the outcome)) ^
                " Retrying with " ^ string_of_int new_num_facts ^ " fact" ^
                plural_s new_num_facts ^ "..."
                |> Output.urgent_message
              else
                ()
          in
            facts |> take new_num_facts
                  |> do_slice timeout (slice + 1) outcome0 time_so_far
          end
        else
          {outcome = if is_none outcome then NONE else the outcome0,
           used_facts = used_facts,
           run_time_in_msecs = SOME (Time.toMilliseconds time_so_far)}
      end
  in do_slice timeout 1 NONE Time.zeroTime end

(* taken from "Mirabelle" and generalized *)
fun can_apply timeout tac state i =
  let
    val {context = ctxt, facts, goal} = Proof.goal state
    val full_tac = Method.insert_tac facts i THEN tac ctxt i
  in
    case try (TimeLimit.timeLimit timeout (Seq.pull o full_tac)) goal of
      SOME (SOME _) => true
    | _ => false
  end

val smt_metis_timeout = seconds 1.0

fun can_apply_metis debug state i ths =
  can_apply smt_metis_timeout
            (Config.put Metis_Tactics.verbose debug
             #> (fn ctxt => Metis_Tactics.metis_tac ctxt ths)) state i

fun run_smt_solver auto name (params as {debug, verbose, ...}) minimize_command
                   ({state, subgoal, subgoal_count, facts, smt_filter, ...}
                    : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val num_facts = length facts
    val facts = facts ~~ (0 upto num_facts - 1)
                |> map (smt_weighted_fact ctxt num_facts)
    val {outcome, used_facts, run_time_in_msecs} =
      smt_filter_loop ctxt name params state subgoal smt_filter facts
    val (chained_lemmas, other_lemmas) = split_used_facts (map fst used_facts)
    val outcome = outcome |> Option.map failure_from_smt_failure
    val message =
      case outcome of
        NONE =>
        let
          val (method, settings) =
            if can_apply_metis debug state subgoal (map snd used_facts) then
              ("metis", "")
            else
              ("smt", if name = SMT_Solver.solver_name_of ctxt then ""
                      else "smt_solver = " ^ maybe_quote name)
        in
          try_command_line (proof_banner auto)
              (apply_on_subgoal settings subgoal subgoal_count ^
               command_call method (map fst other_lemmas)) ^
          minimize_line minimize_command
                        (map fst (other_lemmas @ chained_lemmas)) ^
          (if verbose then
             "\nSMT solver real CPU time: " ^
             string_from_time (Time.fromMilliseconds (the run_time_in_msecs)) ^
             "."
           else
             "")
        end
      | SOME failure => string_for_failure failure
  in
    {outcome = outcome, used_facts = map fst used_facts,
     run_time_in_msecs = run_time_in_msecs, message = message}
  end

fun get_prover ctxt auto name =
  let val thy = Proof_Context.theory_of ctxt in
    if is_smt_prover ctxt name then
      run_smt_solver auto name
    else if member (op =) (supported_atps thy) name then
      run_atp auto name (get_atp thy name)
    else
      error ("No such prover: " ^ name ^ ".")
  end

end;
