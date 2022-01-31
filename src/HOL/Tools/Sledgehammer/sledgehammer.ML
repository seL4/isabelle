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

  datatype sledgehammer_outcome =
    SH_Some of prover_result
  | SH_Unknown
  | SH_Timeout
  | SH_None

  val short_string_of_sledgehammer_outcome : sledgehammer_outcome -> string

  val play_one_line_proof : bool -> Time.time -> (string * stature) list -> Proof.state -> int ->
    proof_method * proof_method list list -> (string * stature) list * (proof_method * play_outcome)
  val string_of_factss : (string * fact list) list -> string
  val run_sledgehammer : params -> mode -> (string -> unit) option -> int -> fact_override ->
    Proof.state -> bool * (sledgehammer_outcome * string)
end;

structure Sledgehammer : SLEDGEHAMMER =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay
open Sledgehammer_Isar_Minimize
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh

datatype sledgehammer_outcome =
  SH_Some of prover_result
| SH_Unknown
| SH_Timeout
| SH_None

fun short_string_of_sledgehammer_outcome (SH_Some _) = "some"
  | short_string_of_sledgehammer_outcome SH_Unknown = "unknown"
  | short_string_of_sledgehammer_outcome SH_Timeout = "timeout"
  | short_string_of_sledgehammer_outcome SH_None = "none"

fun alternative f (SOME x) (SOME y) = SOME (f (x, y))
  | alternative _ (x as SOME _) NONE = x
  | alternative _ NONE (y as SOME _) = y
  | alternative _ NONE NONE = NONE

fun max_outcome outcomes =
  let
    val result = find_first (fn (SH_Some _, _) => true | _ => false) outcomes
    val unknown = find_first (fn (SH_Unknown, _) => true | _ => false) outcomes
    val timeout = find_first (fn (SH_Timeout, _) => true | _ => false) outcomes
    val none = find_first (fn (SH_None, _) => true | _ => false) outcomes
  in
    result
    |> alternative snd unknown
    |> alternative snd timeout
    |> alternative snd none
    |> the_default (SH_Unknown, "")
  end

fun is_metis_method (Metis_Method _) = true
  | is_metis_method _ = false

fun play_one_line_proof minimize timeout used_facts state i (preferred_meth, methss) =
  (if timeout = Time.zeroTime then
     (used_facts, (preferred_meth, Play_Timed_Out Time.zeroTime))
   else
     let
       val ctxt = Proof.context_of state

       val fact_names = used_facts |> filter_out (fn (_, (sc, _)) => sc = Chained) |> map fst
       val {facts = chained, goal, ...} = Proof.goal state
       val goal_t = Logic.get_goal (Thm.prop_of goal) i

       fun try_methss [] [] = (used_facts, (preferred_meth, Play_Timed_Out Time.zeroTime))
         | try_methss ress [] =
           (used_facts,
            (case AList.lookup (op =) ress preferred_meth of
              SOME play => (preferred_meth, play)
            | NONE => hd (sort (play_outcome_ord o apply2 snd) (rev ress))))
         | try_methss ress (meths :: methss) =
           let
             fun mk_step fact_names meths =
               Prove {
                 qualifiers = [],
                 obtains = [],
                 label = ("", 0),
                 goal = goal_t,
                 subproofs = [],
                 facts = ([], fact_names),
                 proof_methods = meths,
                 comment = ""}
           in
             (case preplay_isar_step ctxt chained timeout [] (mk_step fact_names meths) of
               (res as (meth, Played time)) :: _ =>
               (* if a fact is needed by an ATP, it will be needed by "metis" *)
               if not minimize orelse is_metis_method meth then
                 (used_facts, res)
               else
                 let
                   val (time', used_names') =
                     minimized_isar_step ctxt chained time (mk_step fact_names [meth])
                     ||> (facts_of_isar_step #> snd)
                   val used_facts' = filter (member (op =) used_names' o fst) used_facts
                 in
                   (used_facts', (meth, Played time'))
                 end
             | ress' => try_methss (ress' @ ress) methss)
           end
     in
       try_methss [] methss
     end)
  |> (fn (used_facts, (meth, play)) =>
        (used_facts |> filter_out (fn (_, (sc, _)) => sc = Chained), (meth, play)))

fun launch_prover (params as {verbose, spy, max_facts, induction_rules, ...}) mode only learn
    ({comment, state, goal, subgoal, subgoal_count, facts, found_proof} : prover_problem) name =
  let
    val ctxt = Proof.context_of state

    val _ = spying spy (fn () => (state, subgoal, name, "Launched"))
    val max_facts = max_facts |> the_default (default_max_facts_of_prover ctxt name)
    val num_facts = length (snd facts) |> not only ? Integer.min max_facts
    val induction_rules = the_default Exclude induction_rules

    val problem =
      {comment = comment, state = state, goal = goal, subgoal = subgoal,
       subgoal_count = subgoal_count,
       facts = facts
         (* We take "num_facts" because "facts" contains the maximum of all called provers. *)
         |> apsnd (take num_facts o maybe_filter_out_induction_rules induction_rules),
       found_proof = found_proof}

    fun print_used_facts used_facts used_from =
      tag_list 1 used_from
      |> map (fn (j, fact) => fact |> apsnd (K j))
      |> filter_used_facts false used_facts
      |> map (fn ((name, _), j) => name ^ "@" ^ string_of_int j)
      |> commas
      |> prefix ("Fact" ^ plural_s num_facts ^ " in " ^ name ^
        " proof (of " ^ string_of_int num_facts ^ "): ")
      |> writeln

    fun spying_str_of_res ({outcome = NONE, used_facts, used_from, ...} : prover_result) =
        let
          val num_used_facts = length used_facts

          fun find_indices facts =
            tag_list 1 facts
            |> map (fn (j, fact) => fact |> apsnd (K j))
            |> filter_used_facts false used_facts
            |> distinct (eq_fst (op =))
            |> map (prefix "@" o string_of_int o snd)

          fun filter_info (fact_filter, facts) =
            let
              val indices = find_indices facts
              (* "Int.max" is there for robustness -- it shouldn't be necessary *)
              val unknowns = replicate (Int.max (0, num_used_facts - length indices)) "?"
            in
              (commas (indices @ unknowns), fact_filter)
            end

          val filter_infos =
            map filter_info [("actual", used_from), facts]
            |> AList.group (op =)
            |> map (fn (indices, fact_filters) => commas fact_filters ^ ": " ^ indices)
        in
          "Success: Found proof with " ^ string_of_int num_used_facts ^ " of " ^
          string_of_int num_facts ^ " fact" ^ plural_s num_facts ^
          (if num_used_facts = 0 then "" else ": " ^ commas filter_infos)
        end
      | spying_str_of_res {outcome = SOME failure, ...} =
        "Failure: " ^ string_of_atp_failure failure
 in
  problem
  |> get_minimizing_prover ctxt mode learn name params
  |> verbose ? tap (fn {outcome = NONE, used_facts as _ :: _, used_from, ...} =>
      print_used_facts used_facts used_from
    | _ => ())
  |> spy ? tap (fn res => spying spy (fn () => (state, subgoal, name, spying_str_of_res res)))
 end

fun preplay_prover_result ({ minimize, preplay_timeout, ...} : params) state subgoal
    (result as {outcome, used_facts, preferred_methss, message, ...} : prover_result) =
  let
    val output =
      if outcome = SOME ATP_Proof.TimedOut then
        SH_Timeout
      else if is_some outcome then
        SH_None
      else
        SH_Some result
    fun output_message () = message (fn () =>
      play_one_line_proof minimize preplay_timeout used_facts state subgoal preferred_methss)
  in
    (output, output_message)
  end

fun check_expected_outcome ctxt prover_name expect outcome =
  let
    val outcome_code = short_string_of_sledgehammer_outcome outcome
  in
    (* The "expect" argument is deliberately ignored if the prover is
       missing so that the "Metis_Examples" can be processed on any
       machine. *)
    if expect = "" orelse outcome_code = expect orelse
       not (is_prover_installed ctxt prover_name) then
      ()
    else
      error ("Unexpected outcome: " ^ quote outcome_code)
  end

fun launch_prover_and_preplay (params as {debug, timeout, expect, ...}) mode writeln_result only
    learn (problem as {state, subgoal, ...}) prover_name =
  let
    val ctxt = Proof.context_of state
    val hard_timeout = Time.scale 5.0 timeout

    fun really_go () =
      launch_prover params mode only learn problem prover_name
      |> preplay_prover_result params state subgoal

    fun go () =
      if debug then
        really_go ()
      else
        (really_go ()
         handle
           ERROR msg => (SH_Unknown, fn () => "Error: " ^ msg ^ "\n")
         | exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else (SH_Unknown, fn () => "Internal error:\n" ^ Runtime.exn_message exn ^ "\n"))

    val (outcome, message) = Timeout.apply hard_timeout go ()
    val () = check_expected_outcome ctxt prover_name expect outcome

    val message = message ()
    val () =
      (case outcome of
        SH_Some _ =>
        the_default writeln writeln_result (prover_name ^ ": " ^ message)
      | _ => ())
  in
    (outcome, message)
  end

val auto_try_max_facts_divisor = 2 (* FUDGE *)

fun string_of_facts facts =
  "Including " ^ string_of_int (length facts) ^ " relevant fact" ^ plural_s (length facts) ^ ": " ^
  (facts |> map (fst o fst) |> space_implode " ")

fun string_of_factss factss =
  if forall (null o snd) factss then
    "Found no relevant facts"
  else
    cat_lines (map (fn (filter, facts) =>
      (if filter = "" then "" else filter ^ ": ") ^ string_of_facts facts) factss)

fun run_sledgehammer (params as {verbose, spy, provers, induction_rules, max_facts, ...}) mode
    writeln_result i (fact_override as {only, ...}) state =
  if null provers then
    error "No prover is set"
  else
    (case subgoal_count state of
      0 => (error "No subgoal!"; (false, (SH_None, "")))
    | n =>
      let
        val _ = Proof.assert_backward state
        val print = if mode = Normal andalso is_none writeln_result then writeln else K ()

        val found_proof =
          fn prover_name =>
            if mode = Normal then
              (writeln_result |> the_default writeln) (prover_name ^ " found a proof...")
            else
              ()

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
                0 |> fold (Integer.max o default_max_facts_of_prover ctxt) provers
                  |> mode = Auto_Try ? (fn n => n div auto_try_max_facts_divisor))
            val ({elapsed, ...}, factss) = Timing.timing
              (relevant_facts ctxt params (hd provers) max_max_facts fact_override hyp_ts concl_t)
              all_facts
            val () = spying spy (fn () => (state, i, "All",
              "Filtering facts in " ^ string_of_int (Time.toMilliseconds elapsed) ^
              " ms (MaSh algorithm: " ^ str_of_mash_algorithm (the_mash_algorithm ()) ^ ")"));
            val () = if verbose then print (string_of_factss factss) else ()
            val () = spying spy (fn () =>
              (state, i, "All", "Selected facts: " ^ spying_str_of_factss factss))
          in
            factss
          end

        fun launch_provers () =
          let
            val facts = hd (get_factss provers) (* temporary *)
            val problem =
              {comment = "", state = state, goal = goal, subgoal = i, subgoal_count = n,
               facts = facts, found_proof = found_proof}
            val learn = mash_learn_proof ctxt params (Thm.prop_of goal)
            val launch = launch_prover_and_preplay params mode writeln_result only learn
          in
            if mode = Auto_Try then
              (SH_Unknown, "")
              |> fold (fn prover =>
                fn accum as (SH_Some _, _) => accum
                 | _ => launch problem prover)
                provers
            else
              (learn chained_thms;
               provers
               |> Par_List.map (launch problem)
               |> max_outcome)
          end
      in
        (launch_provers ()
         handle Timeout.TIMEOUT _ => (SH_Timeout, ""))
        |> `(fn (outcome, _) =>
          (case outcome of
            SH_Some _ => (print "QED"; true)
          | SH_Timeout => (print "Timed out"; false)
          | _ => (print "Done"; false)))
      end)

end;
