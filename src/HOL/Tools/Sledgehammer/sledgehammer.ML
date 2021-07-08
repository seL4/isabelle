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

  val someN : string
  val noneN : string
  val timeoutN : string
  val unknownN : string

  val play_one_line_proof : bool -> Time.time -> (string * stature) list -> Proof.state -> int ->
    proof_method * proof_method list list -> (string * stature) list * (proof_method * play_outcome)
  val string_of_factss : (string * fact list) list -> string
  val run_sledgehammer : params -> mode -> (string -> unit) option -> int -> fact_override ->
    Proof.state -> bool * (string * string list)
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

val someN = "some"
val noneN = "none"
val timeoutN = "timeout"
val unknownN = "unknown"

val ordered_outcome_codes = [someN, unknownN, timeoutN, noneN]

fun max_outcome_code codes =
  NONE
  |> fold (fn candidate =>
      fn accum as SOME _ => accum
       | NONE => if member (op =) codes candidate then SOME candidate else NONE)
    ordered_outcome_codes
  |> the_default unknownN

fun is_metis_method (Metis_Method _) = true
  | is_metis_method _ = false

fun play_one_line_proof minimize timeout used_facts state i (preferred_meth, methss) =
  (if timeout = Time.zeroTime then
     (used_facts, (preferred_meth, Play_Timed_Out Time.zeroTime))
   else
     let
       val ctxt = Proof.context_of state

       val fact_names = map fst used_facts
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
             (case preplay_isar_step ctxt [] timeout [] (mk_step fact_names meths) of
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
        (used_facts |> not (proof_method_distinguishes_chained_and_direct meth)
           ? filter_out (fn (_, (sc, _)) => sc = Chained),
         (meth, play)))

fun launch_prover (params as {debug, verbose, spy, max_facts, minimize, timeout, preplay_timeout,
      expect, ...}) mode writeln_result only learn
    {comment, state, goal, subgoal, subgoal_count, factss as (_, facts) :: _, found_proof} name =
  let
    val ctxt = Proof.context_of state

    val hard_timeout = Time.scale 5.0 timeout
    val _ = spying spy (fn () => (state, subgoal, name, "Launched"));
    val max_facts = max_facts |> the_default (default_max_facts_of_prover ctxt name)
    val num_facts = length facts |> not only ? Integer.min max_facts

    val problem =
      {comment = comment, state = state, goal = goal, subgoal = subgoal,
       subgoal_count = subgoal_count,
       factss = factss
       |> map (apsnd ((not (is_ho_atp ctxt name)
           ? filter_out (fn ((_, (_, Induction)), _) => true | _ => false))
         #> take num_facts)),
       found_proof = found_proof}

    fun print_used_facts used_facts used_from =
      tag_list 1 used_from
      |> map (fn (j, fact) => fact |> apsnd (K j))
      |> filter_used_facts false used_facts
      |> map (fn ((name, _), j) => name ^ "@" ^ string_of_int j)
      |> commas
      |> prefix ("Fact" ^ plural_s (length facts) ^ " in " ^ quote name ^
        " proof (of " ^ string_of_int (length facts) ^ "): ")
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
            map filter_info (("actual", used_from) :: factss)
            |> AList.group (op =)
            |> map (fn (indices, fact_filters) => commas fact_filters ^ ": " ^ indices)
        in
          "Success: Found proof with " ^ string_of_int num_used_facts ^ " of " ^
          string_of_int num_facts ^ " fact" ^ plural_s num_facts ^
          (if num_used_facts = 0 then "" else ": " ^ commas filter_infos)
        end
      | spying_str_of_res {outcome = SOME failure, ...} =
        "Failure: " ^ string_of_atp_failure failure

    fun really_go () =
      problem
      |> get_minimizing_prover ctxt mode learn name params
      |> verbose ? tap (fn {outcome = NONE, used_facts as _ :: _, used_from, ...} =>
          print_used_facts used_facts used_from
        | _ => ())
      |> spy ? tap (fn res => spying spy (fn () => (state, subgoal, name, spying_str_of_res res)))
      |> (fn {outcome, used_facts, preferred_methss, message, ...} =>
        (if outcome = SOME ATP_Proof.TimedOut then timeoutN
         else if is_some outcome then noneN
         else someN,
         fn () => message (fn () => play_one_line_proof minimize preplay_timeout used_facts state
           subgoal preferred_methss)))

    fun go () =
      let
        val (outcome_code, message) =
          if debug then
            really_go ()
          else
            (really_go ()
             handle
               ERROR msg => (unknownN, fn () => "Error: " ^ msg ^ "\n")
             | exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else (unknownN, fn () => "Internal error:\n" ^ Runtime.exn_message exn ^ "\n"))

        val _ =
          (* The "expect" argument is deliberately ignored if the prover is
             missing so that the "Metis_Examples" can be processed on any
             machine. *)
          if expect = "" orelse outcome_code = expect orelse
             not (is_prover_installed ctxt name) then
            ()
          else
            error ("Unexpected outcome: " ^ quote outcome_code)
      in (outcome_code, message) end
  in
    if mode = Auto_Try then
      let val (outcome_code, message) = Timeout.apply timeout go () in
        (outcome_code, if outcome_code = someN then [message ()] else [])
      end
    else
      let
        val (outcome_code, message) = Timeout.apply hard_timeout go ()
        val outcome =
          if outcome_code = someN orelse mode = Normal then quote name ^ ": " ^ message () else ""
        val _ =
          if outcome <> "" andalso is_some writeln_result then the writeln_result outcome
          else writeln outcome
      in (outcome_code, []) end
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
      (if filter = "" then "" else quote filter ^ ": ") ^ string_of_facts facts) factss)

fun run_sledgehammer (params as {verbose, spy, provers, induction_rules, max_facts, ...}) mode
    writeln_result i (fact_override as {only, ...}) state =
  if null provers then
    error "No prover is set"
  else
    (case subgoal_count state of
      0 => (error "No subgoal!"; (false, (noneN, [])))
    | n =>
      let
        val _ = Proof.assert_backward state
        val print = if mode = Normal andalso is_none writeln_result then writeln else K ()

        val found_proof =
          if mode = Normal then
            let val proof_found = Synchronized.var "proof_found" false in
              fn () =>
                if Synchronized.change_result proof_found (rpair true) then ()
                else (writeln_result |> the_default writeln) "Proof found..."
            end
          else
            I

        val ctxt = Proof.context_of state
        val keywords = Thy_Header.get_keywords' ctxt
        val {facts = chained, goal, ...} = Proof.goal state
        val (_, hyp_ts, concl_t) = strip_subgoal goal i ctxt
        val ho_atp = exists (is_ho_atp ctxt) provers
        val induction_rules = the_default (if ho_atp then Instantiate else Exclude) induction_rules
        val css = clasimpset_rule_table_of ctxt
        val all_facts =
          nearly_all_facts ctxt induction_rules fact_override keywords css chained hyp_ts
            concl_t
        val _ =
          (case find_first (not o is_prover_supported ctxt) provers of
            SOME name => error ("No such prover: " ^ name)
          | NONE => ())
        val _ = print "Sledgehammering..."
        val _ = spying spy (fn () => (state, i, "***", "Starting " ^ str_of_mode mode ^ " mode"))

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
            val _ = spying spy (fn () => (state, i, "All",
              "Filtering " ^ string_of_int (length all_facts) ^ " facts (MaSh algorithm: " ^
              str_of_mash_algorithm (the_mash_algorithm ()) ^ ")"));
          in
            all_facts
            |> relevant_facts ctxt params (hd provers) max_max_facts fact_override hyp_ts concl_t
            |> tap (fn factss => if verbose then print (string_of_factss factss) else ())
            |> spy ? tap (fn factss => spying spy (fn () =>
              (state, i, "All", "Selected facts: " ^ spying_str_of_factss factss)))
          end

        fun launch_provers () =
          let
            val factss = get_factss provers
            val problem =
              {comment = "", state = state, goal = goal, subgoal = i, subgoal_count = n,
               factss = factss, found_proof = found_proof}
            val learn = mash_learn_proof ctxt params (Thm.prop_of goal)
            val launch = launch_prover params mode writeln_result only learn
          in
            if mode = Auto_Try then
              (unknownN, [])
              |> fold (fn prover => fn accum as (outcome_code, _) =>
                  if outcome_code = someN then accum else launch problem prover)
                provers
            else
              (learn chained;
               provers
               |> Par_List.map (launch problem #> fst)
               |> max_outcome_code |> rpair [])
          end
      in
        launch_provers ()
        handle Timeout.TIMEOUT _ =>
          (print "Sledgehammer ran out of time"; (unknownN, []))
      end
      |> `(fn (outcome_code, _) => outcome_code = someN))

end;
