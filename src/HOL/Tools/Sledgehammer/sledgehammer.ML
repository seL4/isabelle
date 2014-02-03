(*  Title:      HOL/Tools/Sledgehammer/sledgehammer.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER =
sig
  type fact = Sledgehammer_Fact.fact
  type fact_override = Sledgehammer_Fact.fact_override
  type minimize_command = Sledgehammer_Proof_Methods.minimize_command
  type mode = Sledgehammer_Prover.mode
  type params = Sledgehammer_Prover.params

  val someN : string
  val noneN : string
  val timeoutN : string
  val unknownN : string

  val string_of_factss : (string * fact list) list -> string
  val run_sledgehammer : params -> mode -> (string -> unit) option -> int -> fact_override ->
    ((string * string list) list -> string -> minimize_command) -> Proof.state ->
    bool * (string * Proof.state)
end;

structure Sledgehammer : SLEDGEHAMMER =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
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

fun prover_description ctxt ({verbose, blocking, ...} : params) name num_facts i n goal =
  (quote name,
   (if verbose then
      " with " ^ string_of_int num_facts ^ " fact" ^ plural_s num_facts
    else
      "") ^
   " on " ^ (if n = 1 then "goal" else "subgoal " ^ string_of_int i) ^
   (if blocking then "."
    else "\n" ^ Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i))))

fun launch_prover (params as {debug, verbose, spy, blocking, max_facts, timeout, expect, ...}) mode
    output_result minimize_command only learn
    {comment, state, goal, subgoal, subgoal_count, factss as (_, facts) :: _} name =
  let
    val ctxt = Proof.context_of state

    val hard_timeout = time_mult 3.0 timeout
    val _ = spying spy (fn () => (state, subgoal, name, "Launched"));
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, hard_timeout)
    val max_facts = max_facts |> the_default (default_max_facts_of_prover ctxt name)
    val num_facts = length facts |> not only ? Integer.min max_facts

    fun desc () = prover_description ctxt params name num_facts subgoal subgoal_count goal

    val problem =
      {comment = comment, state = state, goal = goal, subgoal = subgoal,
       subgoal_count = subgoal_count,
       factss = factss
         |> map (apsnd ((not (is_ho_atp ctxt name)
                         ? filter_out (fn ((_, (_, Induction)), _) => true
                                        | _ => false))
                        #> take num_facts))}

    fun print_used_facts used_facts used_from =
      tag_list 1 used_from
      |> map (fn (j, fact) => fact |> apsnd (K j))
      |> filter_used_facts false used_facts
      |> map (fn ((name, _), j) => name ^ "@" ^ string_of_int j)
      |> commas
      |> enclose ("Fact" ^ plural_s (length facts) ^ " in " ^ quote name ^
                  " proof (of " ^ string_of_int (length facts) ^ "): ") "."
      |> Output.urgent_message

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
          "Success: Found proof with " ^ string_of_int num_used_facts ^
          " of " ^ string_of_int num_facts ^ " fact" ^ plural_s num_facts ^
          (if num_used_facts = 0 then "" else ": " ^ commas filter_infos)
        end
      | spying_str_of_res {outcome = SOME failure, ...} =
        "Failure: " ^ string_of_atp_failure failure

    fun really_go () =
      problem
      |> get_minimizing_prover ctxt mode learn name params minimize_command
      |> verbose
         ? tap (fn {outcome = NONE, used_facts as _ :: _, used_from, ...} =>
                   print_used_facts used_facts used_from
                 | _ => ())
      |> spy
         ? tap (fn res => spying spy (fn () => (state, subgoal, name, spying_str_of_res res)))
      |> (fn {outcome, preplay, message, message_tail, ...} =>
             (if outcome = SOME ATP_Proof.TimedOut then timeoutN
              else if is_some outcome then noneN
              else someN, fn () => message (Lazy.force preplay) ^ message_tail))

    fun go () =
      let
        val (outcome_code, message) =
          if debug then
            really_go ()
          else
            (really_go ()
             handle ERROR msg => (unknownN, fn () => "Error: " ^ msg ^ "\n")
                  | exn =>
                    if Exn.is_interrupt exn then
                      reraise exn
                    else
                      (unknownN, fn () => "Internal error:\n" ^
                                          ML_Compiler.exn_message exn ^ "\n"))
        val _ =
          (* The "expect" argument is deliberately ignored if the prover is
             missing so that the "Metis_Examples" can be processed on any
             machine. *)
          if expect = "" orelse outcome_code = expect orelse
             not (is_prover_installed ctxt name) then
            ()
          else if blocking then
            error ("Unexpected outcome: " ^ quote outcome_code ^ ".")
          else
            warning ("Unexpected outcome: " ^ quote outcome_code ^ ".");
      in (outcome_code, message) end
  in
    if mode = Auto_Try then
      let val (outcome_code, message) = TimeLimit.timeLimit timeout go () in
        (outcome_code,
         state
         |> outcome_code = someN
            ? Proof.goal_message (fn () =>
                  Pretty.mark Markup.information (Pretty.str (message ()))))
      end
    else if blocking then
      let
        val (outcome_code, message) = TimeLimit.timeLimit hard_timeout go ()
        val outcome =
          if outcome_code = someN orelse mode = Normal then
            quote name ^ ": " ^ message ()
          else ""
        val _ =
          if outcome <> "" andalso is_some output_result then
            the output_result outcome
          else
            outcome
            |> Async_Manager.break_into_chunks
            |> List.app Output.urgent_message
      in (outcome_code, state) end
    else
      (Async_Manager.thread SledgehammerN birth_time death_time (desc ())
         ((fn (outcome_code, message) => (verbose orelse outcome_code = someN, message ())) o go);
       (unknownN, state))
  end

val auto_try_max_facts_divisor = 2 (* FUDGE *)

fun string_of_facts facts =
  "Including " ^ string_of_int (length facts) ^
  " relevant fact" ^ plural_s (length facts) ^ ":\n" ^
  (facts |> map (fst o fst) |> space_implode " ") ^ "."

fun string_of_factss factss =
  if forall (null o snd) factss then
    "Found no relevant facts."
  else
    (case factss of
      [(_, facts)] => string_of_facts facts
    | _ =>
      factss
      |> map (fn (filter, facts) => quote filter ^ ": " ^ string_of_facts facts)
      |> space_implode "\n\n")

fun run_sledgehammer (params as {debug, verbose, spy, blocking, provers, max_facts, ...}) mode
    output_result i (fact_override as {only, ...}) minimize_command state =
  if null provers then
    error "No prover is set."
  else
    (case subgoal_count state of
      0 =>
      ((if blocking then error else Output.urgent_message) "No subgoal!"; (false, (noneN, state)))
    | n =>
      let
        val _ = Proof.assert_backward state
        val print =
          if mode = Normal andalso is_none output_result then Output.urgent_message else K ()
        val state = state |> Proof.map_context (silence_proof_methods debug)
        val ctxt = Proof.context_of state
        val {facts = chained, goal, ...} = Proof.goal state
        val (_, hyp_ts, concl_t) = strip_subgoal goal i ctxt
        val ho_atp = exists (is_ho_atp ctxt) provers
        val reserved = reserved_isar_keyword_table ()
        val css = clasimpset_rule_table_of ctxt
        val all_facts =
          nearly_all_facts ctxt ho_atp fact_override reserved css chained hyp_ts
                           concl_t
        val _ = () |> not blocking ? kill_provers
        val _ =
          (case find_first (not o is_prover_supported ctxt) provers of
            SOME name => error ("No such prover: " ^ name ^ ".")
          | NONE => ())
        val _ = print "Sledgehammering..."
        val _ = spying spy (fn () => (state, i, "***", "Starting " ^ @{make_string} mode ^ " mode"))

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
              "Filtering " ^ string_of_int (length all_facts) ^ " facts"));
          in
            all_facts
            |> relevant_facts ctxt params (hd provers) max_max_facts fact_override hyp_ts concl_t
            |> tap (fn factss => if verbose then print (string_of_factss factss) else ())
            |> spy ? tap (fn factss => spying spy (fn () =>
              (state, i, "All", "Selected facts: " ^ spying_str_of_factss factss)))
          end

        fun launch_provers state =
          let
            val factss = get_factss provers
            val problem =
              {comment = "", state = state, goal = goal, subgoal = i, subgoal_count = n,
               factss = factss}
            val learn = mash_learn_proof ctxt params (prop_of goal) all_facts
            val launch = launch_prover params mode output_result minimize_command only learn
          in
            if mode = Auto_Try then
              (unknownN, state)
              |> fold (fn prover => fn accum as (outcome_code, _) =>
                          if outcome_code = someN then accum
                          else launch problem prover)
                      provers
            else
              provers
              |> (if blocking then Par_List.map else map) (launch problem #> fst)
              |> max_outcome_code |> rpair state
          end
      in
        (if blocking then launch_provers state
         else (Future.fork (tap (fn () => launch_provers state)); (unknownN, state)))
        handle TimeLimit.TimeOut => (print "Sledgehammer ran out of time."; (unknownN, state))
      end
      |> `(fn (outcome_code, _) => outcome_code = someN))

end;
