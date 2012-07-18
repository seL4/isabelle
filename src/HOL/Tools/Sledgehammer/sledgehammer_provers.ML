(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_provers.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Generic prover abstraction for Sledgehammer.
*)

signature SLEDGEHAMMER_PROVERS =
sig
  type failure = ATP_Proof.failure
  type stature = ATP_Problem_Generate.stature
  type type_enc = ATP_Problem_Generate.type_enc
  type reconstructor = ATP_Proof_Reconstruct.reconstructor
  type play = ATP_Proof_Reconstruct.play
  type minimize_command = ATP_Proof_Reconstruct.minimize_command

  datatype mode = Auto_Try | Try | Normal | Auto_Minimize | Minimize

  type params =
    {debug: bool,
     verbose: bool,
     overlord: bool,
     blocking: bool,
     provers: string list,
     type_enc: string option,
     strict: bool,
     lam_trans: string option,
     uncurried_aliases: bool option,
     fact_filter: string option,
     max_facts: int option,
     fact_thresholds: real * real,
     max_mono_iters: int option,
     max_new_mono_instances: int option,
     isar_proof: bool,
     isar_shrink_factor: int,
     slice: bool,
     minimize: bool option,
     timeout: Time.time,
     preplay_timeout: Time.time,
     expect: string}

  type relevance_fudge =
    {local_const_multiplier : real,
     worse_irrel_freq : real,
     higher_order_irrel_weight : real,
     abs_rel_weight : real,
     abs_irrel_weight : real,
     skolem_irrel_weight : real,
     theory_const_rel_weight : real,
     theory_const_irrel_weight : real,
     chained_const_irrel_weight : real,
     intro_bonus : real,
     elim_bonus : real,
     simp_bonus : real,
     local_bonus : real,
     assum_bonus : real,
     chained_bonus : real,
     max_imperfect : real,
     max_imperfect_exp : real,
     threshold_divisor : real,
     ridiculous_threshold : real}

  datatype prover_fact =
    Untranslated_Fact of (string * stature) * thm |
    SMT_Weighted_Fact of (string * stature) * (int option * thm)

  type prover_problem =
    {state: Proof.state,
     goal: thm,
     subgoal: int,
     subgoal_count: int,
     facts: prover_fact list}

  type prover_result =
    {outcome: failure option,
     used_facts: (string * stature) list,
     run_time: Time.time,
     preplay: unit -> play,
     message: play -> string,
     message_tail: string}

  type prover =
    params -> ((string * string list) list -> string -> minimize_command)
    -> prover_problem -> prover_result

  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val completish : bool Config.T
  val atp_full_names : bool Config.T
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
  val das_tool : string
  val plain_metis : reconstructor
  val select_smt_solver : string -> Proof.context -> Proof.context
  val extract_reconstructor :
    params -> reconstructor -> string * (string * string list) list
  val is_reconstructor : string -> bool
  val is_atp : theory -> string -> bool
  val is_smt_prover : Proof.context -> string -> bool
  val is_ho_atp: Proof.context -> string -> bool
  val is_unit_equational_atp : Proof.context -> string -> bool
  val is_prover_supported : Proof.context -> string -> bool
  val is_prover_installed : Proof.context -> string -> bool
  val default_max_facts_for_prover : Proof.context -> bool -> string -> int
  val is_unit_equality : term -> bool
  val is_appropriate_prop_for_prover : Proof.context -> string -> term -> bool
  val is_built_in_const_for_prover :
    Proof.context -> string -> string * typ -> term list -> bool * term list
  val atp_relevance_fudge : relevance_fudge
  val smt_relevance_fudge : relevance_fudge
  val relevance_fudge_for_prover : Proof.context -> string -> relevance_fudge
  val weight_smt_fact :
    Proof.context -> int -> ((string * stature) * thm) * int
    -> (string * stature) * (int option * thm)
  val untranslated_fact : prover_fact -> (string * stature) * thm
  val smt_weighted_fact :
    Proof.context -> int -> prover_fact * int
    -> (string * stature) * (int option * thm)
  val supported_provers : Proof.context -> unit
  val kill_provers : unit -> unit
  val running_provers : unit -> unit
  val messages : int option -> unit
  val filter_used_facts : ''a list -> (''a * 'b) list -> (''a * 'b) list
  val get_prover : Proof.context -> mode -> string -> prover
end;

structure Sledgehammer_Provers : SLEDGEHAMMER_PROVERS =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Systems
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Tactic
open Sledgehammer_Util


(** The Sledgehammer **)

datatype mode = Auto_Try | Try | Normal | Auto_Minimize | Minimize

(* Identifier that distinguishes Sledgehammer from other tools that could use
   "Async_Manager". *)
val das_tool = "Sledgehammer"

val reconstructor_names = [metisN, smtN]
val plain_metis = Metis (hd partial_type_encs, combsN)
val is_reconstructor = member (op =) reconstructor_names

val is_atp = member (op =) o supported_atps

val select_smt_solver = Context.proof_map o SMT_Config.select_solver

fun is_smt_prover ctxt = member (op =) (SMT_Solver.available_solvers_of ctxt)

fun is_atp_for_format is_format ctxt name =
  let val thy = Proof_Context.theory_of ctxt in
    case try (get_atp thy) name of
      SOME config =>
      exists (fn (_, (_, ((_, format, _, _, _), _))) => is_format format)
             (#best_slices (config ()) ctxt)
    | NONE => false
  end

val is_unit_equational_atp = is_atp_for_format (curry (op =) CNF_UEQ)
val is_ho_atp = is_atp_for_format is_format_higher_order

fun is_prover_supported ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    is_reconstructor orf is_atp thy orf is_smt_prover ctxt
  end

fun is_prover_installed ctxt =
  is_reconstructor orf is_smt_prover ctxt orf
  is_atp_installed (Proof_Context.theory_of ctxt)

fun get_slices slice slices =
  (0 upto length slices - 1) ~~ slices |> not slice ? (List.last #> single)

val reconstructor_default_max_facts = 20

fun default_max_facts_for_prover ctxt slice name =
  let val thy = Proof_Context.theory_of ctxt in
    if is_reconstructor name then
      reconstructor_default_max_facts
    else if is_atp thy name then
      fold (Integer.max o #1 o fst o snd o snd o snd)
           (get_slices slice (#best_slices (get_atp thy name ()) ctxt)) 0
    else (* is_smt_prover ctxt name *)
      SMT_Solver.default_max_relevant ctxt name
  end

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

fun is_appropriate_prop_for_prover ctxt name =
  if is_unit_equational_atp ctxt name then is_unit_equality else K true

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
  {local_const_multiplier = 1.5,
   worse_irrel_freq = 100.0,
   higher_order_irrel_weight = 1.05,
   abs_rel_weight = 0.5,
   abs_irrel_weight = 2.0,
   skolem_irrel_weight = 0.05,
   theory_const_rel_weight = 0.5,
   theory_const_irrel_weight = 0.25,
   chained_const_irrel_weight = 0.25,
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
  {local_const_multiplier = #local_const_multiplier atp_relevance_fudge,
   worse_irrel_freq = #worse_irrel_freq atp_relevance_fudge,
   higher_order_irrel_weight = #higher_order_irrel_weight atp_relevance_fudge,
   abs_rel_weight = #abs_rel_weight atp_relevance_fudge,
   abs_irrel_weight = #abs_irrel_weight atp_relevance_fudge,
   skolem_irrel_weight = #skolem_irrel_weight atp_relevance_fudge,
   theory_const_rel_weight = #theory_const_rel_weight atp_relevance_fudge,
   theory_const_irrel_weight = #theory_const_irrel_weight atp_relevance_fudge,
   chained_const_irrel_weight = #chained_const_irrel_weight atp_relevance_fudge,
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
      reconstructor_names @
      sort_strings (supported_atps thy) @
      sort_strings (SMT_Solver.available_solvers_of ctxt)
      |> List.partition (String.isPrefix remote_prefix)
  in
    Output.urgent_message ("Supported provers: " ^
                           commas (local_provers @ remote_provers) ^ ".")
  end

fun kill_provers () = Async_Manager.kill_threads das_tool "prover"
fun running_provers () = Async_Manager.running_threads das_tool "prover"
val messages = Async_Manager.thread_messages das_tool "prover"


(** problems, results, ATPs, etc. **)

type params =
  {debug: bool,
   verbose: bool,
   overlord: bool,
   blocking: bool,
   provers: string list,
   type_enc: string option,
   strict: bool,
   lam_trans: string option,
   uncurried_aliases: bool option,
   fact_filter: string option,
   max_facts: int option,
   fact_thresholds: real * real,
   max_mono_iters: int option,
   max_new_mono_instances: int option,
   isar_proof: bool,
   isar_shrink_factor: int,
   slice: bool,
   minimize: bool option,
   timeout: Time.time,
   preplay_timeout: Time.time,
   expect: string}

type relevance_fudge =
  {local_const_multiplier : real,
   worse_irrel_freq : real,
   higher_order_irrel_weight : real,
   abs_rel_weight : real,
   abs_irrel_weight : real,
   skolem_irrel_weight : real,
   theory_const_rel_weight : real,
   theory_const_irrel_weight : real,
   chained_const_irrel_weight : real,
   intro_bonus : real,
   elim_bonus : real,
   simp_bonus : real,
   local_bonus : real,
   assum_bonus : real,
   chained_bonus : real,
   max_imperfect : real,
   max_imperfect_exp : real,
   threshold_divisor : real,
   ridiculous_threshold : real}

datatype prover_fact =
  Untranslated_Fact of (string * stature) * thm |
  SMT_Weighted_Fact of (string * stature) * (int option * thm)

type prover_problem =
  {state: Proof.state,
   goal: thm,
   subgoal: int,
   subgoal_count: int,
   facts: prover_fact list}

type prover_result =
  {outcome: failure option,
   used_facts: (string * stature) list,
   run_time: Time.time,
   preplay: unit -> play,
   message: play -> string,
   message_tail: string}

type prover =
  params -> ((string * string list) list -> string -> minimize_command)
  -> prover_problem -> prover_result

(* configuration attributes *)

(* Empty string means create files in Isabelle's temporary files directory. *)
val dest_dir =
  Attrib.setup_config_string @{binding sledgehammer_dest_dir} (K "")
val problem_prefix =
  Attrib.setup_config_string @{binding sledgehammer_problem_prefix} (K "prob")
val completish =
  Attrib.setup_config_bool @{binding sledgehammer_completish} (K false)

(* In addition to being easier to read, readable names are often much shorter,
   especially if types are mangled in names. This makes a difference for some
   provers (e.g., E). For these reason, short names are enabled by default. *)
val atp_full_names =
  Attrib.setup_config_bool @{binding sledgehammer_atp_full_names} (K false)

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
fun smt_weighted_fact _ _ (SMT_Weighted_Fact p, _) = p
  | smt_weighted_fact ctxt num_facts (fact, j) =
    (untranslated_fact fact, j) |> weight_smt_fact ctxt num_facts

fun overlord_file_location_for_prover prover =
  (getenv "ISABELLE_HOME_USER", "prob_" ^ prover)

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path)

fun proof_banner mode name =
  case mode of
    Auto_Try => "Auto Sledgehammer (" ^ quote name ^ ") found a proof"
  | Try => "Sledgehammer (" ^ quote name ^ ") found a proof"
  | _ => "Try this"

fun bunch_of_reconstructors needs_full_types lam_trans =
  [(false, Metis (partial_type_enc, lam_trans false)),
   (true, Metis (full_type_enc, lam_trans false)),
   (false, Metis (no_typesN, lam_trans true)),
   (true, Metis (really_full_type_enc, lam_trans true)),
   (true, SMT)]
  |> map_filter (fn (full_types, reconstr) =>
                    if needs_full_types andalso not full_types then NONE
                    else SOME reconstr)

fun extract_reconstructor ({type_enc, lam_trans, ...} : params)
                          (Metis (type_enc', lam_trans')) =
    let
      val override_params =
        (if is_none type_enc andalso type_enc' = hd partial_type_encs then
           []
         else
           [("type_enc", [hd (unalias_type_enc type_enc')])]) @
        (if is_none lam_trans andalso lam_trans' = metis_default_lam_trans then
           []
         else
           [("lam_trans", [lam_trans'])])
    in (metisN, override_params) end
  | extract_reconstructor _ SMT = (smtN, [])

(* based on "Mirabelle.can_apply" and generalized *)
fun timed_apply timeout tac state i =
  let
    val {context = ctxt, facts, goal} = Proof.goal state
    val full_tac = Method.insert_tac facts i THEN tac ctxt i
  in TimeLimit.timeLimit timeout (try (Seq.pull o full_tac)) goal end

fun tac_for_reconstructor (Metis (type_enc, lam_trans)) =
    metis_tac [type_enc] lam_trans
  | tac_for_reconstructor SMT = SMT_Solver.smt_tac

fun timed_reconstructor reconstr debug timeout ths =
  (Config.put Metis_Tactic.verbose debug
   #> Config.put SMT_Config.verbose debug
   #> (fn ctxt => tac_for_reconstructor reconstr ctxt ths))
  |> timed_apply timeout

fun filter_used_facts used = filter (member (op =) used o fst)

fun play_one_line_proof mode debug verbose timeout pairs state i preferred
                        reconstrs =
  let
    val _ =
      if mode = Minimize andalso Time.> (timeout, Time.zeroTime) then
        Output.urgent_message "Preplaying proof..."
      else
        ()
    val ths = pairs |> sort_wrt (fst o fst) |> map snd
    fun get_preferred reconstrs =
      if member (op =) reconstrs preferred then preferred
      else List.last reconstrs
    fun play [] [] = Failed_to_Play (get_preferred reconstrs)
      | play timed_outs [] =
        Trust_Playable (get_preferred timed_outs, SOME timeout)
      | play timed_out (reconstr :: reconstrs) =
        let
          val _ =
            if verbose then
              "Trying \"" ^ string_for_reconstructor reconstr ^ "\" for " ^
              string_from_time timeout ^ "..."
              |> Output.urgent_message
            else
              ()
          val timer = Timer.startRealTimer ()
        in
          case timed_reconstructor reconstr debug timeout ths state i of
            SOME (SOME _) => Played (reconstr, Timer.checkRealTimer timer)
          | _ => play timed_out reconstrs
        end
        handle TimeLimit.TimeOut => play (reconstr :: timed_out) reconstrs
  in
    if timeout = Time.zeroTime then
      Trust_Playable (get_preferred reconstrs, NONE)
    else
      play [] reconstrs
  end


(* generic TPTP-based ATPs *)

(* Too general means, positive equality literal with a variable X as one
   operand, when X does not occur properly in the other operand. This rules out
   clearly inconsistent facts such as X = a | X = b, though it by no means
   guarantees soundness. *)

(* Unwanted equalities are those between a (bound or schematic) variable that
   does not properly occur in the second operand. *)
val is_exhaustive_finite =
  let
    fun is_bad_equal (Var z) t =
        not (exists_subterm (fn Var z' => z = z' | _ => false) t)
      | is_bad_equal (Bound j) t = not (loose_bvar1 (t, j))
      | is_bad_equal _ _ = false
    fun do_equals t1 t2 = is_bad_equal t1 t2 orelse is_bad_equal t2 t1
    fun do_formula pos t =
      case (pos, t) of
        (_, @{const Trueprop} $ t1) => do_formula pos t1
      | (true, Const (@{const_name all}, _) $ Abs (_, _, t')) =>
        do_formula pos t'
      | (true, Const (@{const_name All}, _) $ Abs (_, _, t')) =>
        do_formula pos t'
      | (false, Const (@{const_name Ex}, _) $ Abs (_, _, t')) =>
        do_formula pos t'
      | (_, @{const "==>"} $ t1 $ t2) =>
        do_formula (not pos) t1 andalso
        (t2 = @{prop False} orelse do_formula pos t2)
      | (_, @{const HOL.implies} $ t1 $ t2) =>
        do_formula (not pos) t1 andalso
        (t2 = @{const False} orelse do_formula pos t2)
      | (_, @{const Not} $ t1) => do_formula (not pos) t1
      | (true, @{const HOL.disj} $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (false, @{const HOL.conj} $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (true, Const (@{const_name HOL.eq}, _) $ t1 $ t2) => do_equals t1 t2
      | (true, Const (@{const_name "=="}, _) $ t1 $ t2) => do_equals t1 t2
      | _ => false
  in do_formula true end

fun has_bound_or_var_of_type pred =
  exists_subterm (fn Var (_, T as Type _) => pred T
                   | Abs (_, T as Type _, _) => pred T
                   | _ => false)

(* Facts are forbidden to contain variables of these types. The typical reason
   is that they lead to unsoundness. Note that "unit" satisfies numerous
   equations like "?x = ()". The resulting clauses will have no type constraint,
   yielding false proofs. Even "bool" leads to many unsound proofs, though only
   for higher-order problems. *)

(* Facts containing variables of type "unit" or "bool" or of the form
   "ALL x. x = A | x = B | x = C" are likely to lead to unsound proofs if types
   are omitted. *)
fun is_dangerous_prop ctxt =
  transform_elim_prop
  #> (has_bound_or_var_of_type (is_type_surely_finite ctxt) orf
      is_exhaustive_finite)

(* Important messages are important but not so important that users want to see
   them each time. *)
val atp_important_message_keep_quotient = 25

fun choose_type_enc soundness best_type_enc format =
  the_default best_type_enc
  #> type_enc_from_string soundness
  #> adjust_type_enc format

val metis_minimize_max_time = seconds 2.0

fun choose_minimize_command params minimize_command name preplay =
  let
    val (name, override_params) =
      case preplay of
        Played (reconstr, time) =>
        if Time.<= (time, metis_minimize_max_time) then
          extract_reconstructor params reconstr
        else
          (name, [])
      | _ => (name, [])
  in minimize_command override_params name end

fun repair_monomorph_context max_iters best_max_iters max_new_instances
                             best_max_new_instances =
  Config.put Monomorph.max_rounds (max_iters |> the_default best_max_iters)
  #> Config.put Monomorph.max_new_instances
         (max_new_instances |> the_default best_max_new_instances)
  #> Config.put Monomorph.keep_partial_instances false

fun suffix_for_mode Auto_Try = "_auto_try"
  | suffix_for_mode Try = "_try"
  | suffix_for_mode Normal = ""
  | suffix_for_mode Auto_Minimize = "_auto_min"
  | suffix_for_mode Minimize = "_min"

(* Give the ATPs some slack before interrupting them the hard way. "z3_tptp" on
   Linux appears to be the only ATP that does not honor its time limit. *)
val atp_timeout_slack = seconds 1.0

fun run_atp mode name
        ({exec, required_vars, arguments, proof_delims, known_failures,
          prem_role, best_slices, best_max_mono_iters,
          best_max_new_mono_instances, ...} : atp_config)
        (params as {debug, verbose, overlord, type_enc, strict, lam_trans,
                    uncurried_aliases, max_facts, max_mono_iters,
                    max_new_mono_instances, isar_proof, isar_shrink_factor,
                    slice, timeout, preplay_timeout, ...})
        minimize_command
        ({state, goal, subgoal, subgoal_count, facts, ...} : prover_problem) =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val atp_mode =
      if Config.get ctxt completish then Sledgehammer_Completish
      else Sledgehammer
    val (_, hyp_ts, concl_t) = strip_subgoal ctxt goal subgoal
    val (dest_dir, problem_prefix) =
      if overlord then overlord_file_location_for_prover name
      else (Config.get ctxt dest_dir, Config.get ctxt problem_prefix)
    val problem_file_name =
      Path.basic (problem_prefix ^ (if overlord then "" else serial_string ()) ^
                  suffix_for_mode mode ^ "_" ^ string_of_int subgoal)
    val problem_path_name =
      if dest_dir = "" then
        File.tmp_path problem_file_name
      else if File.exists (Path.explode dest_dir) then
        Path.append (Path.explode dest_dir) problem_file_name
      else
        error ("No such directory: " ^ quote dest_dir ^ ".")
    val command =
      case find_first (fn var => getenv var <> "") (fst exec) of
        SOME var => Path.explode (getenv var ^ "/" ^ snd exec)
      | NONE => error ("The environment variable " ^ quote (hd (fst exec)) ^
                       " is not set.")
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n")
        val (output, t) =
          s |> split |> (try split_last #> the_default ([], "0"))
            |>> cat_lines
        fun as_num f = f >> (fst o read_int)
        val num = as_num (Scan.many1 Symbol.is_ascii_digit)
        val digit = Scan.one Symbol.is_ascii_digit
        val num3 = as_num (digit ::: digit ::: (digit >> single))
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b)
        val as_time =
          raw_explode #> Scan.read Symbol.stopper time #> the_default 0
      in (output, as_time t |> Time.fromMilliseconds) end
    fun run_on prob_file =
      case find_first (forall (fn var => getenv var = ""))
                      (fst exec :: required_vars) of
        SOME home_vars =>
        error ("The environment variable " ^ quote (hd home_vars) ^
               " is not set.")
      | NONE =>
        if File.exists command then
          let
            (* If slicing is disabled, we expand the last slice to fill the
               entire time available. *)
            val actual_slices = get_slices slice (best_slices ctxt)
            val num_actual_slices = length actual_slices
            fun monomorphize_facts facts =
              let
                val ctxt =
                  ctxt
                  |> repair_monomorph_context max_mono_iters best_max_mono_iters
                          max_new_mono_instances best_max_new_mono_instances
                (* pseudo-theorem involving the same constants as the subgoal *)
                val subgoal_th =
                  Logic.list_implies (hyp_ts, concl_t)
                  |> Skip_Proof.make_thm thy
                val rths =
                  facts |> chop (length facts div 4)
                        |>> map (pair 1 o snd)
                        ||> map (pair 2 o snd)
                        |> op @
                        |> cons (0, subgoal_th)
              in
                Monomorph.monomorph atp_schematic_consts_of rths ctxt
                |> fst |> tl
                |> curry ListPair.zip (map fst facts)
                |> maps (fn (name, rths) =>
                            map (pair name o zero_var_indexes o snd) rths)
              end
            fun run_slice time_left (cache_key, cache_value)
                    (slice, (time_frac, (complete,
                        (key as (best_max_facts, format, best_type_enc,
                                 best_lam_trans, best_uncurried_aliases),
                                 extra)))) =
              let
                val num_facts =
                  length facts |> is_none max_facts ? Integer.min best_max_facts
                val soundness = if strict then Strict else Non_Strict
                val type_enc =
                  type_enc |> choose_type_enc soundness best_type_enc format
                val sound = is_type_enc_sound type_enc
                val real_ms = Real.fromInt o Time.toMilliseconds
                val slice_timeout =
                  ((real_ms time_left
                    |> (if slice < num_actual_slices - 1 then
                          curry Real.min (time_frac * real_ms timeout)
                        else
                          I))
                   * 0.001) |> seconds
                val generous_slice_timeout =
                  Time.+ (slice_timeout, atp_timeout_slack)
                val _ =
                  if debug then
                    quote name ^ " slice #" ^ string_of_int (slice + 1) ^
                    " with " ^ string_of_int num_facts ^ " fact" ^
                    plural_s num_facts ^ " for " ^
                    string_from_time slice_timeout ^ "..."
                    |> Output.urgent_message
                  else
                    ()
                val readable_names = not (Config.get ctxt atp_full_names)
                val lam_trans =
                  case lam_trans of
                    SOME s => s
                  | NONE => best_lam_trans
                val uncurried_aliases =
                  case uncurried_aliases of
                    SOME b => b
                  | NONE => best_uncurried_aliases
                val value as (atp_problem, _, fact_names, _, _) =
                  if cache_key = SOME key then
                    cache_value
                  else
                    facts
                    |> map untranslated_fact
                    |> not sound
                       ? filter_out (is_dangerous_prop ctxt o prop_of o snd)
                    |> take num_facts
                    |> not (is_type_enc_polymorphic type_enc)
                       ? monomorphize_facts
                    |> map (apsnd prop_of)
                    |> prepare_atp_problem ctxt format prem_role type_enc
                                           atp_mode lam_trans uncurried_aliases
                                           readable_names true hyp_ts concl_t
                fun sel_weights () = atp_problem_selection_weights atp_problem
                fun ord_info () = atp_problem_term_order_info atp_problem
                val ord = effective_term_order ctxt name
                val full_proof = debug orelse isar_proof
                val args = arguments ctxt full_proof extra slice_timeout
                                     (ord, ord_info, sel_weights)
                val command =
                  File.shell_path command ^ " " ^ args ^ " " ^
                  File.shell_path prob_file
                  |> enclose "TIMEFORMAT='%3R'; { time " " ; } 2>&1"
                val _ =
                  atp_problem
                  |> lines_for_atp_problem format ord ord_info
                  |> cons ("% " ^ command ^ "\n")
                  |> File.write_list prob_file
                val ((output, run_time), (atp_proof, outcome)) =
                  TimeLimit.timeLimit generous_slice_timeout
                                      Isabelle_System.bash_output command
                  |>> (if overlord then
                         prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n")
                       else
                         I)
                  |> fst |> split_time
                  |> (fn accum as (output, _) =>
                         (accum,
                          extract_tstplike_proof_and_outcome verbose complete
                              proof_delims known_failures output
                          |>> atp_proof_from_tstplike_proof atp_problem
                          handle UNRECOGNIZED_ATP_PROOF () =>
                                 ([], SOME ProofIncomplete)))
                  handle TimeLimit.TimeOut =>
                         (("", slice_timeout), ([], SOME TimedOut))
                val outcome =
                  case outcome of
                    NONE =>
                    (case used_facts_in_unsound_atp_proof ctxt fact_names
                                                          atp_proof
                          |> Option.map (sort string_ord) of
                       SOME facts =>
                       let
                         val failure =
                           UnsoundProof (is_type_enc_sound type_enc, facts)
                       in
                         if debug then
                           (warning (string_for_failure failure); NONE)
                         else
                           SOME failure
                       end
                     | NONE => NONE)
                  | _ => outcome
              in ((SOME key, value), (output, run_time, atp_proof, outcome)) end
            val timer = Timer.startRealTimer ()
            fun maybe_run_slice slice
                    (result as (cache, (_, run_time0, _, SOME _))) =
                let
                  val time_left = Time.- (timeout, Timer.checkRealTimer timer)
                in
                  if Time.<= (time_left, Time.zeroTime) then
                    result
                  else
                    run_slice time_left cache slice
                    |> (fn (cache, (output, run_time, atp_proof, outcome)) =>
                           (cache, (output, Time.+ (run_time0, run_time),
                                    atp_proof, outcome)))
                end
              | maybe_run_slice _ result = result
          in
            ((NONE, ([], Symtab.empty, Vector.fromList [], [], Symtab.empty)),
             ("", Time.zeroTime, [], SOME InternalError))
            |> fold maybe_run_slice actual_slices
          end
        else
          error ("Bad executable: " ^ Path.print command)

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup prob_file =
      if dest_dir = "" then try File.rm prob_file else NONE
    fun export prob_file (_, (output, _, _, _)) =
      if dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode prob_file ^ "_proof")) output
    val ((_, (_, pool, fact_names, _, sym_tab)),
         (output, run_time, atp_proof, outcome)) =
      with_path cleanup export run_on problem_path_name
    val important_message =
      if mode = Normal andalso
         random_range 0 (atp_important_message_keep_quotient - 1) = 0 then
        extract_important_message output
      else
        ""
    val (used_facts, preplay, message, message_tail) =
      case outcome of
        NONE =>
        let
          val used_facts = used_facts_in_atp_proof ctxt fact_names atp_proof
          val needs_full_types = is_typed_helper_used_in_atp_proof atp_proof
          val reconstrs =
            bunch_of_reconstructors needs_full_types
                (lam_trans_from_atp_proof atp_proof
                 o (fn desperate => if desperate then hide_lamsN
                                    else metis_default_lam_trans))
        in
          (used_facts,
           fn () =>
              let
                val used_pairs =
                  facts |> map untranslated_fact |> filter_used_facts used_facts
              in
                play_one_line_proof mode debug verbose preplay_timeout
                    used_pairs state subgoal (hd reconstrs) reconstrs
              end,
           fn preplay =>
              let
                val isar_params =
                  (debug, isar_shrink_factor, pool, fact_names, sym_tab,
                   atp_proof, goal)
                val one_line_params =
                  (preplay, proof_banner mode name, used_facts,
                   choose_minimize_command params minimize_command name preplay,
                   subgoal, subgoal_count)
              in proof_text ctxt isar_proof isar_params one_line_params end,
           (if verbose then
              "\nATP real CPU time: " ^ string_from_time run_time ^ "."
            else
              "") ^
           (if important_message <> "" then
              "\n\nImportant message from Dr. Geoff Sutcliffe:\n" ^
              important_message
            else
              ""))
        end
      | SOME failure =>
        ([], K (Failed_to_Play plain_metis),
         fn _ => string_for_failure failure, "")
  in
    {outcome = outcome, used_facts = used_facts, run_time = run_time,
     preplay = preplay, message = message, message_tail = message_tail}
  end

(* "SMT_Failure.Abnormal_Termination" carries the solver's return code. Until
   these are sorted out properly in the SMT module, we have to interpret these
   ourselves. *)
val remote_smt_failures =
  [(2, NoLibwwwPerl),
   (22, CantConnect)]
val z3_failures =
  [(101, OutOfResources),
   (103, MalformedInput),
   (110, MalformedInput)]
val unix_failures =
  [(139, Crashed)]
val smt_failures = remote_smt_failures @ z3_failures @ unix_failures

fun failure_from_smt_failure (SMT_Failure.Counterexample {is_real_cex, ...}) =
    if is_real_cex then Unprovable else GaveUp
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
                      max_new_mono_instances, timeout, slice, ...} : params)
                    state i =
  let
    val max_slices = if slice then Config.get ctxt smt_max_slices else 1
    val repair_context =
      select_smt_solver name
      #> Config.put SMT_Config.verbose debug
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
                       (repair_monomorph_context max_mono_iters
                            default_max_mono_iters max_new_mono_instances
                            default_max_new_mono_instances)
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
          SMT_Solver.smt_filter_preprocess state facts i
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
           used_facts = used_facts, run_time = time_so_far}
      end
  in do_slice timeout 1 NONE Time.zeroTime end

fun run_smt_solver mode name (params as {debug, verbose, preplay_timeout, ...})
        minimize_command
        ({state, subgoal, subgoal_count, facts, ...} : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val num_facts = length facts
    val facts = facts ~~ (0 upto num_facts - 1)
                |> map (smt_weighted_fact ctxt num_facts)
    val {outcome, used_facts = used_pairs, run_time} =
      smt_filter_loop ctxt name params state subgoal facts
    val used_facts = used_pairs |> map fst
    val outcome = outcome |> Option.map failure_from_smt_failure
    val (preplay, message, message_tail) =
      case outcome of
        NONE =>
        (fn () =>
            play_one_line_proof mode debug verbose preplay_timeout used_pairs
                state subgoal SMT
                (bunch_of_reconstructors false
                     (fn plain =>
                         if plain then metis_default_lam_trans else liftingN)),
         fn preplay =>
            let
              val one_line_params =
                (preplay, proof_banner mode name, used_facts,
                 choose_minimize_command params minimize_command name preplay,
                 subgoal, subgoal_count)
            in one_line_proof_text one_line_params end,
         if verbose then
           "\nSMT solver real CPU time: " ^ string_from_time run_time ^ "."
         else
           "")
      | SOME failure =>
        (K (Failed_to_Play plain_metis), fn _ => string_for_failure failure, "")
  in
    {outcome = outcome, used_facts = used_facts, run_time = run_time,
     preplay = preplay, message = message, message_tail = message_tail}
  end

fun run_reconstructor mode name
        (params as {debug, verbose, timeout, type_enc, lam_trans, ...})
        minimize_command
        ({state, subgoal, subgoal_count, facts, ...} : prover_problem) =
  let
    val reconstr =
      if name = metisN then
        Metis (type_enc |> the_default (hd partial_type_encs),
               lam_trans |> the_default metis_default_lam_trans)
      else if name = smtN then
        SMT
      else
        raise Fail ("unknown reconstructor: " ^ quote name)
    val used_pairs = facts |> map untranslated_fact
    val used_facts = used_pairs |> map fst
  in
    case play_one_line_proof (if mode = Minimize then Normal else mode) debug
                             verbose timeout used_pairs state subgoal reconstr
                             [reconstr] of
      play as Played (_, time) =>
      {outcome = NONE, used_facts = used_facts, run_time = time,
       preplay = K play,
       message =
         fn play =>
            let
              val (_, override_params) = extract_reconstructor params reconstr
              val one_line_params =
                (play, proof_banner mode name, used_facts,
                 minimize_command override_params name, subgoal,
                 subgoal_count)
            in one_line_proof_text one_line_params end,
       message_tail = ""}
    | play =>
      let
        val failure = case play of Failed_to_Play _ => GaveUp | _ => TimedOut
      in
        {outcome = SOME failure, used_facts = [], run_time = Time.zeroTime,
         preplay = K play, message = fn _ => string_for_failure failure,
         message_tail = ""}
      end
  end

fun get_prover ctxt mode name =
  let val thy = Proof_Context.theory_of ctxt in
    if is_reconstructor name then run_reconstructor mode name
    else if is_atp thy name then run_atp mode name (get_atp thy name ())
    else if is_smt_prover ctxt name then run_smt_solver mode name
    else error ("No such prover: " ^ name ^ ".")
  end

end;
