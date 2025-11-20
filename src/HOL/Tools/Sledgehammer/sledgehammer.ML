(*  Title:      HOL/Tools/Sledgehammer/sledgehammer.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER =
sig
  type stature = ATP_Problem_Generate.stature
  type fact = Sledgehammer_Fact.fact
  type fact_override = Sledgehammer_Fact.fact_override
  type proof_method = Sledgehammer_Proof_Methods.proof_method
  type play_outcome = Sledgehammer_Proof_Methods.play_outcome
  type mode = Sledgehammer_Prover.mode
  type params = Sledgehammer_Prover.params
  type induction_rules = Sledgehammer_Prover.induction_rules
  type prover_problem = Sledgehammer_Prover.prover_problem
  type prover_result = Sledgehammer_Prover.prover_result

  type preplay_result = proof_method * (play_outcome * (Pretty.T * stature) list)

  datatype sledgehammer_outcome =
    SH_Some of prover_result * preplay_result list
  | SH_Unknown
  | SH_TimeOut
  | SH_ResourcesOut
  | SH_None

  val short_string_of_sledgehammer_outcome : sledgehammer_outcome -> string
  val string_of_factss : (string * fact list) list -> string
  val run_sledgehammer : params -> mode -> (string -> unit) option -> int -> fact_override ->
    Proof.state -> bool * (sledgehammer_outcome * string)
end;

structure Sledgehammer : SLEDGEHAMMER =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
open Sledgehammer_Instantiations
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay
open Sledgehammer_Isar_Minimize
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Prover_Tactic
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh

type preplay_result = proof_method * (play_outcome * (Pretty.T * stature) list)

datatype sledgehammer_outcome =
  SH_Some of prover_result * preplay_result list
| SH_Unknown
| SH_TimeOut
| SH_ResourcesOut
| SH_None

fun short_string_of_sledgehammer_outcome (SH_Some _) = "some"
  | short_string_of_sledgehammer_outcome SH_Unknown = "unknown"
  | short_string_of_sledgehammer_outcome SH_TimeOut = "timeout"
  | short_string_of_sledgehammer_outcome SH_ResourcesOut = "resources_out"
  | short_string_of_sledgehammer_outcome SH_None = "none"

fun alternative f (SOME x) (SOME y) = SOME (f (x, y))
  | alternative _ (x as SOME _) NONE = x
  | alternative _ NONE (y as SOME _) = y
  | alternative _ NONE NONE = NONE

fun varify_nonfixed_terms_global nonfixeds tm =
  tm |> Term.map_aterms
    (fn Free (x, T) => if member (op =) nonfixeds x then Var ((x, 0), T) else raise Same.SAME
      | Var (xi, _) => raise TERM (Logic.bad_schematic xi, [tm])
      | _ => raise Same.SAME)

fun max_outcome outcomes =
  let
    val some = find_first (fn (SH_Some _, _) => true | _ => false) outcomes
    val timeout = find_first (fn (SH_TimeOut, _) => true | _ => false) outcomes
    val resources_out = find_first (fn (SH_ResourcesOut, _) => true | _ => false) outcomes
    val unknown = find_first (fn (SH_Unknown, _) => true | _ => false) outcomes
    val none = find_first (fn (SH_None, _) => true | _ => false) outcomes
  in
    some
    |> alternative snd unknown
    |> alternative snd timeout
    |> alternative snd resources_out
    |> alternative snd none
    |> the_default (SH_Unknown, "")
  end

fun play_one_line_proofs minimize timeout used_facts state goal i methss : preplay_result list =
  (if timeout = Time.zeroTime then
     []
   else
     let
       val ctxt = Proof.context_of state
       val name_of_fact = content_of_pretty o fst
       val fact_names = map name_of_fact used_facts
       val {facts = chained, ...} = Proof.goal state
       val goal_t = Logic.get_goal (Thm.prop_of goal) i

       fun try_methss ress [] = ress
         | try_methss ress (meths :: methss) =
           let
             fun mk_step meths =
               Prove {
                 qualifiers = [],
                 obtains = [],
                 label = ("", 0),
                 goal = goal_t,
                 subproofs = [],
                 facts = ([], fact_names),
                 proof_methods = meths,
                 comment = ""}
             val ress' =
               preplay_isar_step ctxt chained timeout [] (mk_step meths)
               |> map (fn (meth, play_outcome) =>
                  (case (minimize, play_outcome) of
                    (true, Played time) =>
                    let
                      val (time', used_names') =
                        minimized_isar_step ctxt chained time (mk_step [meth])
                        ||> (facts_of_isar_step #> snd)
                      val used_facts' =
                        filter (member (op =) used_names' o name_of_fact) used_facts
                    in
                      (meth, (Played time', used_facts'))
                    end
                  | _ => (meth, (play_outcome, used_facts))))
             val any_succeeded = exists (fn (_, (Played _, _)) => true | _ => false) ress'
           in
             try_methss (ress' @ ress) (if any_succeeded then [] else methss)
           end
     in
       try_methss [] methss
     end)
  |> sort (play_outcome_ord o apply2 (fn (_, (play_outcome, _)) => play_outcome))

fun select_one_line_proof preferred_meth preplay_results =
  (case preplay_results of
    (* Select best method if preplay succeeded *)
    (best_meth, (best_outcome as Played _, best_used_facts)) :: _ =>
    SOME (best_used_facts, (best_meth, best_outcome))
    (* Otherwise select preferred method *)
  | _ =>
    AList.lookup (op =) preplay_results preferred_meth
    |> Option.map (fn (outcome, used_facts) => (used_facts, (preferred_meth, outcome))))

fun launch_prover (params as {verbose, spy, slices, timeout, ...}) mode learn
    (problem as {state, subgoal, factss, ...} : prover_problem)
    (slice as ((slice_size, abduce, falsify, num_facts, fact_filter), _)) name =
  let
    val ctxt = Proof.context_of state

    val _ = spying spy (fn () => (state, subgoal, name,
      "Launched" ^ (if abduce then " (abduce)" else "") ^ (if falsify then " (falsify)" else "")))

    val _ =
      if verbose then
        writeln (name ^ " with " ^ string_of_int num_facts ^ " " ^ fact_filter ^ " fact" ^
          plural_s num_facts ^ " for " ^ string_of_time (slice_timeout slice_size slices timeout) ^
          (if abduce then " (abduce)" else "") ^ (if falsify then " (falsify)" else "") ^ "...")
      else
        ()

    fun print_used_facts used_facts used_from =
      used_from
      |> map_index (fn (j, fact) => fact |> apsnd (K (j + 1)))
      |> filter_used_facts false used_facts
      |> map (fn ((name, _), j) => name ^ "@" ^ string_of_int j)
      |> commas
      |> prefix ("Facts in " ^ name ^ " " ^ (if falsify then "falsification" else "proof") ^ ": ")
      |> writeln

    fun spying_str_of_res ({outcome = NONE, used_facts, used_from, ...} : prover_result) =
        let
          val num_used_facts = length used_facts

          fun find_indices facts =
            facts
            |> map_index (fn (j, fact) => fact |> apsnd (K (j + 1)))
            |> filter_used_facts false used_facts
            |> distinct (eq_fst (op =))
            |> map (prefix "@" o string_of_int o snd)

          fun filter_info (fact_filter, facts) =
            let
              val indices = find_indices facts
              (* "Int.max" is there for robustness *)
              val unknowns = replicate (Int.max (0, num_used_facts - length indices)) "?"
            in
              (commas (indices @ unknowns), fact_filter)
            end

          val filter_infos =
            map filter_info (("actual", used_from) :: factss)
            |> AList.group (op =)
            |> map (fn (indices, fact_filters) => commas fact_filters ^ ": " ^ indices)
        in
          "Success: Found " ^ (if falsify then "falsification" else "proof") ^ " with " ^
          string_of_int num_used_facts ^ " fact" ^ plural_s num_used_facts ^
          (if num_used_facts = 0 then "" else ": " ^ commas filter_infos)
        end
      | spying_str_of_res {outcome = SOME failure, ...} =
        "Failure: " ^ string_of_atp_failure failure
 in
   get_minimizing_prover ctxt mode learn name params problem slice
   |> verbose ? tap (fn {outcome = NONE, used_facts as _ :: _, used_from, ...} =>
       print_used_facts used_facts used_from
     | _ => ())
   |> spy ? tap (fn res => spying spy (fn () => (state, subgoal, name, spying_str_of_res res)))
 end

fun preplay_prover_result ({verbose, instantiate, minimize, preplay_timeout, ...} : params)
    state goal subgoal
    (result as {outcome, used_facts, preferred_methss, message, ...} : prover_result) =
  if outcome = SOME ATP_Proof.TimedOut then
    (SH_TimeOut, fn () => message NONE)
  else if outcome = SOME ATP_Proof.OutOfResources then
    (SH_ResourcesOut, fn () => message NONE)
  else if is_some outcome then
    (SH_None, fn () => message NONE)
  else
    let
      val used_facts0 = filter_out (fn (_, (sc, _)) => sc = Chained) used_facts
      val pretty_used_facts0 = map (apfst Pretty.str) used_facts0
      fun preplay methss pretty_used_facts =
        play_one_line_proofs minimize preplay_timeout pretty_used_facts state goal subgoal methss
      fun preplay_succeeded ((_, (Played _, _)) :: _) = true
        | preplay_succeeded _ = false
      val instantiate_timeout =
        if preplay_timeout = Time.zeroTime then
          Time.fromSeconds 5
        else
          Time.scale 5.0 preplay_timeout
      val instantiate = if null used_facts0 then SOME false else instantiate
      val preplay_results =
        (case instantiate of
          SOME false => preplay (snd preferred_methss) pretty_used_facts0
        | SOME true =>
          (* Always try to infer variable instantiations *)
          (case instantiate_facts state verbose instantiate_timeout goal subgoal used_facts0 of
            NONE => preplay (snd preferred_methss) pretty_used_facts0
          | SOME pretty_used_facts =>
            if preplay_timeout = Time.zeroTime then
              [(fst preferred_methss, (Play_Timed_Out Time.zeroTime, pretty_used_facts))]
            else if null (snd preferred_methss) then
              preplay [[fst preferred_methss]] pretty_used_facts
            else
              preplay (snd preferred_methss) pretty_used_facts)
        | NONE =>
          let
            val preplay_results0 = preplay (snd preferred_methss) pretty_used_facts0
            val preplay_disabled =
              preplay_timeout = Time.zeroTime orelse null (snd preferred_methss)
          in
            if preplay_succeeded preplay_results0 orelse preplay_disabled then
              preplay_results0
            else
              (* Preplay failed, now try to infer variable instantiations *)
              instantiate_facts state verbose instantiate_timeout goal subgoal used_facts0
              |> Option.map (preplay (snd preferred_methss))
              |> the_default preplay_results0
          end)
      fun output_message () =
        message (select_one_line_proof (fst preferred_methss) preplay_results)
    in
      (SH_Some (result, preplay_results), output_message)
    end

fun analyze_prover_result_for_inconsistency (result as {outcome, used_facts, ...} : prover_result) =
  if outcome = SOME ATP_Proof.TimedOut then
    (SH_TimeOut, K "")
  else if outcome = SOME ATP_Proof.OutOfResources then
    (SH_ResourcesOut, K "")
  else if is_some outcome then
    (SH_None, K "")
  else
    (SH_Some (result, []), fn () =>
       (if member (op = o apsnd fst) used_facts sledgehammer_goal_as_fact then
          (case map fst (filter_out (equal sledgehammer_goal_as_fact o fst) used_facts) of
            [] => "The goal is inconsistent"
          | facts => "The goal is falsified by these facts: " ^ commas facts)
        else
          "Derived \"False\" from these facts alone: " ^
          implode_space (map fst used_facts)))

fun check_expected_outcome ctxt prover_name expect outcome =
  let
    val outcome_code = short_string_of_sledgehammer_outcome outcome
  in
    (* The "expect" argument is deliberately ignored if the prover is missing so that
       "Metis_Examples" can be processed on any machine. *)
    if expect = "" orelse not (is_prover_installed ctxt prover_name) then
      ()
    else
      (case (expect, outcome) of
        ("some", SH_Some _) => ()
      | ("some_preplayed", SH_Some (_, preplay_results)) =>
          if exists (fn (_, (Played _, _)) => true | _ => false) preplay_results then
            ()
          else
            error ("Unexpected outcome: the external prover found a proof but preplay failed")
      | ("unknown", SH_Unknown) => ()
      | ("timeout", SH_TimeOut) => ()
      | ("resources_out", SH_ResourcesOut) => ()
      | ("none", SH_None) => ()
      | _ => error ("Unexpected outcome: " ^ quote outcome_code))
  end

fun launch_prover_and_preplay (params as {debug, timeout, expect, ...}) mode
    has_already_found_something found_something massage_message writeln_result learn
    (problem as {state, subgoal, ...}) (slice as ((_, _, falsify, _, _), _)) prover_name =
  let
    val ctxt = Proof.context_of state
    val hard_timeout = Time.scale 5.0 timeout

    fun flip_problem {comment, state, goal, subgoal, factss, memoize_fun_call, ...} =
      let
        val thy = Proof_Context.theory_of ctxt
        val assms = Assumption.all_assms_of ctxt
        val assm_ts = map Thm.term_of assms
        val subgoal_t = Logic.get_goal (Thm.prop_of goal) subgoal
        val polymorphic_subgoal_t = (Logic.list_implies (assm_ts, subgoal_t))
          |> Logic.varify_global
        val nonfixeds =
          subtract (op =) (fold Term.add_free_names assm_ts []) (Term.add_free_names subgoal_t [])
        val monomorphic_subgoal_t = subgoal_t
          |> varify_nonfixed_terms_global nonfixeds
        val subgoal_thms = map (Skip_Proof.make_thm thy)
          [polymorphic_subgoal_t, monomorphic_subgoal_t]
        val new_facts =
          map (fn thm => (((sledgehammer_goal_as_fact, (Assum, General)), thm))) subgoal_thms
      in
        {comment = comment, state = state, goal = Thm.trivial @{cprop False}, subgoal = 1,
         subgoal_count = 1, factss = map (apsnd (append new_facts)) factss,
         has_already_found_something = has_already_found_something,
         found_something = found_something "a falsification",
         memoize_fun_call = memoize_fun_call}
      end

    val problem as {goal, ...} = problem |> falsify ? flip_problem

    fun really_go () =
      launch_prover params mode learn problem slice prover_name
      |> (if falsify then analyze_prover_result_for_inconsistency else
        preplay_prover_result params state goal subgoal)

    fun go () =
      if debug then
        really_go ()
      else
        \<^try>\<open>really_go ()
          catch ERROR msg => (SH_Unknown, fn () => msg ^ "\n")
            | exn => (SH_Unknown, fn () => Runtime.exn_message exn ^ "\n")\<close>

    val (outcome, message) = Timeout.apply hard_timeout go ()
    val () = check_expected_outcome ctxt prover_name expect outcome

    val message = message ()
    val () =
      if mode = Auto_Try then
        ()
      else
        (case outcome of
          SH_Some _ =>
          the_default writeln writeln_result (prover_name ^ ": " ^
            massage_message (if falsify then "falsification" else "proof") message)
        | _ => ())
  in
    (outcome, message)
  end

fun string_of_facts filter facts =
  "Selected " ^ string_of_int (length facts) ^ " " ^ (if filter = "" then "" else filter ^ " ") ^
  "fact" ^ plural_s (length facts) ^ ": " ^ (implode_space (map (fst o fst) facts))

fun string_of_factss factss =
  if forall (null o snd) factss then
    "Found no relevant facts"
  else
    cat_lines (map (fn (filter, facts) => string_of_facts filter facts) factss)

local

fun default_slice_schedule (ctxt : Proof.context) : string list =
  (* We want to subsume try0. *)
  flat (Try0.get_schedule ctxt) @
  (* FUDGE (loosely inspired by "Hammering without ATPs" evaluation) *)
  ["metis", "fastforce", "metis", "simp", "auto", "fastforce", "metis", "simp"] @
  (* FUDGE (loosely inspired by Seventeen evaluation) *)
  [cvc5N, zipperpositionN, vampireN, veritN, spassN, zipperpositionN, eN, cvc5N, zipperpositionN,
   cvc5N, eN, zipperpositionN, vampireN, cvc5N, cvc5N, vampireN, cvc5N, iproverN, zipperpositionN,
   spassN, vampireN, zipperpositionN, vampireN, zipperpositionN, z3N, zipperpositionN, vampireN,
   iproverN, spassN, zipperpositionN, vampireN, cvc5N, zipperpositionN, z3N, z3N, cvc5N,
   zipperpositionN]

in

fun schedule_of_provers (ctxt : Proof.context) (provers : string list) num_slices =
  let
    val default_schedule = default_slice_schedule ctxt
    val (tactics, known_provers, unknown_provers) =
      let
        fun partition_into name (tactics, known_provers, unknown_provers) =
          if Option.isSome (Try0.get_proof_method name) then
            (name :: tactics, known_provers, unknown_provers)
          else if member (op =) default_schedule name then
            (tactics, name :: known_provers, unknown_provers)
          else
            (tactics, known_provers, name :: unknown_provers)
      in
        fold partition_into provers ([], [], [])
      end

    val default_schedule =
      filter (fn name => member (op =) tactics name orelse member (op =) known_provers name)
        default_schedule
    val num_default_slices = length default_schedule

    fun round_robin _ [] = []
      | round_robin 0 _ = []
      | round_robin n (prover :: provers) = prover :: round_robin (n - 1) (provers @ [prover])
  in
    if num_slices <= num_default_slices then
      take num_slices default_schedule
    else
      default_schedule
      @ round_robin (num_slices - num_default_slices) (unknown_provers @ known_provers)
  end

end

fun prover_slices_of_schedule ctxt goal subgoal factss
    ({abduce, falsify, max_facts, fact_filter, type_enc, lam_trans, uncurried_aliases,
      ...} : params)
    schedule =
  let
    fun triplicate_slices original =
      let
        val shift =
          map (apfst (fn (slice_size, abduce, falsify, num_facts, fact_filter) =>
            (slice_size, abduce, falsify, num_facts,
             if fact_filter = mashN then mepoN
             else if fact_filter = mepoN then meshN
             else mashN)))

        val shifted_once = shift original
        val shifted_twice = shift shifted_once
      in
        original @ shifted_once @ shifted_twice
      end

    fun adjust_extra (ATP_Slice (format0, type_enc0, lam_trans0, uncurried_aliases0,
        extra_extra0)) =
        ATP_Slice (format0, the_default type_enc0 type_enc, the_default lam_trans0 lam_trans,
          the_default uncurried_aliases0 uncurried_aliases, extra_extra0)
      | adjust_extra extra = extra

    fun adjust_slice max_slice_size
        ((slice_size0, abduce0, falsify0, num_facts0, fact_filter0), extra) =
      let
        val slice_size = Int.min (max_slice_size, slice_size0)
        val the_subgoal = Logic.get_goal (Thm.prop_of goal) subgoal
        val goal_not_False = not (the_subgoal aconv @{prop False})
        val abduce =
          (case abduce of
            NONE => abduce0 andalso goal_not_False
          | SOME max_candidates => max_candidates > 0)
        val falsify =
          (case falsify of
            NONE => falsify0 andalso goal_not_False
          | SOME falsify => falsify)
          andalso not (Term.is_schematic the_subgoal)
        val fact_filter = fact_filter |> the_default fact_filter0
        val max_facts = max_facts |> the_default num_facts0
        val num_facts = Int.min (max_facts, length (facts_of_filter fact_filter factss))
      in
        ((slice_size, abduce, falsify, num_facts, fact_filter), adjust_extra extra)
      end

    val provers = distinct (op =) schedule
    val prover_slices =
      map (fn prover => (prover,
          (is_none fact_filter ? triplicate_slices) (get_slices ctxt prover)))
        provers

    val max_threads = Multithreading.max_threads ()

    fun translate_schedule _ 0 _ = []
      | translate_schedule _ _ [] = []
      | translate_schedule prover_slices slices_left (prover :: schedule) =
        (case AList.lookup (op =) prover_slices prover of
          SOME (slice0 :: slices) =>
          let
            val prover_slices' = AList.update (op =) (prover, slices) prover_slices
            val slice as ((slice_size, _, _, _, _), _) =
              adjust_slice ((slices_left + max_threads - 1) div max_threads) slice0
          in
            (prover, slice) :: translate_schedule prover_slices' (slices_left - slice_size) schedule
          end
        | _ => translate_schedule prover_slices slices_left schedule)
  in
    translate_schedule prover_slices (length schedule) schedule
    |> distinct (op =)
  end

local

fun memoize verbose cache_dir f arg =
  let
    val hash = SHA1.rep (SHA1.digest arg)
    val file = cache_dir + Path.explode hash
  in
    (case try File.read file of
      NONE =>
      let val result = f arg in
        File.write file result;
        result
      end
    | SOME s =>
      let
        val () =
          if verbose then
            writeln ("Found problem with key " ^ hash ^ " in cache.")
          else
            ()
      in s end)
  end
in

fun run_sledgehammer (params as {verbose, spy, provers, falsify, induction_rules, max_facts,
    max_proofs, slices, timeout, cache_dir, ...}) mode writeln_result i (fact_override as {only, ...}) state =
  if null provers then
    error "No prover is set"
  else
    (case subgoal_count state of
      0 => (error "No subgoal!"; (false, (SH_None, "")))
    | n =>
      let
        val _ = Proof.assert_backward state
        val print = if mode = Normal andalso is_none writeln_result then writeln else K ()

        val found_proofs_and_falsifications = Synchronized.var "found_proofs_and_falsifications" 0

        fun has_already_found_something () =
          if mode = Normal then
            Synchronized.value found_proofs_and_falsifications > 0
          else
            false

        fun found_something a_proof_or_inconsistency prover_name =
          if mode = Normal then
            (Synchronized.change found_proofs_and_falsifications (fn n => n + 1);
             (the_default writeln writeln_result) (prover_name ^ " found " ^
             a_proof_or_inconsistency ^ "..."))
          else
            ()

        val seen_messages = Synchronized.var "seen_messages" ([] : string list)

        fun strip_until_left_paren "" = ""
          | strip_until_left_paren s =
            let
              val n = String.size s
              val s' = String.substring (s, 0, n - 1)
            in
              s' |> String.substring (s, n - 1, 1) <> "(" ? strip_until_left_paren
            end

        (* Remove the measured preplay time when looking for duplicates. This is
           admittedly rather ad hoc. *)
        fun strip_time s =
          if String.isSuffix " s)" s orelse String.isSuffix " ms)" s then
            strip_until_left_paren s
          else
            s

        fun massage_message proof_or_inconsistency s =
          let val s' = strip_time s in
            if member (op =) (Synchronized.value seen_messages) s' then
              "Duplicate " ^ proof_or_inconsistency
            else
              (Synchronized.change seen_messages (cons s'); s)
          end

        val ctxt = Proof.context_of state
        val inst_inducts = induction_rules = SOME Instantiate
        val {facts = chained_thms, goal, ...} = Proof.goal state
        val (_, hyp_ts, concl_t) = strip_subgoal goal i ctxt
        val _ =
          (case find_first (not o is_prover_supported ctxt) provers of
            SOME name => error ("No such prover: " ^ name)
          | NONE => ())
        val _ = print "Sledgehammering..."
        val _ = spying spy (fn () => (state, i, "***", "Starting " ^ str_of_mode mode ^ " mode"))
        val ({elapsed, ...}, all_facts) = Timing.timing
          (nearly_all_facts_of_context ctxt inst_inducts fact_override chained_thms hyp_ts) concl_t
        val _ = spying spy (fn () => (state, i, "All",
          "Extracting " ^ string_of_int (length all_facts) ^ " facts from background theory in " ^
          string_of_int (Time.toMilliseconds elapsed) ^ " ms"))

        val spying_str_of_factss =
          commas o map (fn (filter, facts) => filter ^ ": " ^ string_of_int (length facts))

        fun get_factss provers =
          let
            val max_max_facts =
              (case max_facts of
                SOME n => n
              | NONE =>
                fold (fn prover =>
                      fold (fn ((_, _, _, max_facts, _), _) => Integer.max max_facts)
                    (get_slices ctxt prover))
                  provers 0)
              * 51 div 50  (* some slack to account for filtering of induction facts below *)

            val ({elapsed, ...}, factss) = Timing.timing
              (relevant_facts ctxt params (hd provers) max_max_facts fact_override hyp_ts concl_t)
              all_facts

            val induction_rules = the_default (if only then Include else Exclude) induction_rules
            val factss = map (apsnd (maybe_filter_out_induction_rules induction_rules)) factss

            val () = spying spy (fn () => (state, i, "All",
              "Filtering facts in " ^ string_of_int (Time.toMilliseconds elapsed) ^
              " ms (MaSh algorithm: " ^ str_of_mash_algorithm (the_mash_algorithm ()) ^ ")"));
            val () = if verbose then print (string_of_factss factss) else ()
            val () = spying spy (fn () =>
              (state, i, "All", "Selected facts: " ^ spying_str_of_factss factss))
          in
            factss
          end

        val memoize_fun_call =
          (case cache_dir of
            NONE => (fn f => fn arg => f arg)
          | SOME path =>
            (if File.is_dir path then
              memoize verbose path
            else
              (warning ("No such directory: " ^ quote (Path.print path));
              fn f => fn arg => f arg)))

        fun launch_provers () =
          let
            val factss = get_factss provers
            val problem =
              {comment = "", state = state, goal = goal, subgoal = i, subgoal_count = n,
               factss = factss, has_already_found_something = has_already_found_something,
               found_something = found_something "a proof", memoize_fun_call = memoize_fun_call}
            val learn = mash_learn_proof ctxt params (Thm.prop_of goal)
            val launch = launch_prover_and_preplay params mode has_already_found_something
              found_something massage_message writeln_result learn

            val timer = Timer.startRealTimer ()

            val schedule =
              if mode = Auto_Try then provers
              else schedule_of_provers ctxt provers slices
            val prover_slices = prover_slices_of_schedule ctxt goal i factss params schedule

            val _ =
              if verbose then
                writeln ("Running " ^ commas (map fst prover_slices) ^ "...")
              else
                ()
          in
            if mode = Auto_Try then
              (SH_Unknown, "")
              |> fold (fn (prover, slice) =>
                  fn accum as (SH_Some _, _) => accum
                    | _ => launch problem slice prover)
                prover_slices
            else
              (learn chained_thms;
               Par_List.map (fn (prover, slice) =>
                   if Synchronized.value found_proofs_and_falsifications < max_proofs
                      andalso Timer.checkRealTimer timer < timeout then
                     launch problem slice prover
                   else
                     (SH_None, ""))
                 prover_slices
               |> max_outcome)
          end

        fun normal_failure () =
          (the_default writeln writeln_result
             ("No " ^ (if falsify = SOME true then "falsification" else "proof") ^
              " found");
           false)
      in
        (launch_provers ()
         handle Timeout.TIMEOUT _ => (SH_TimeOut, ""))
        |> `(fn (outcome, message) =>
          (case outcome of
            SH_Some _ => (the_default writeln writeln_result "Done"; true)
          | SH_Unknown =>
            if message = "" then normal_failure ()
            else (the_default writeln writeln_result ("Warning: " ^ message); false)
          | SH_TimeOut => normal_failure ()
          | SH_ResourcesOut => normal_failure ()
          | SH_None =>
            if message = "" then normal_failure ()
            else (the_default writeln writeln_result ("Warning: " ^ message); false)))
      end)

end

end;
