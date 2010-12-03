(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
*)

signature SLEDGEHAMMER_ISAR =
sig
  type params = Sledgehammer.params

  val auto : bool Unsynchronized.ref
  val provers : string Unsynchronized.ref
  val timeout : int Unsynchronized.ref
  val full_types : bool Unsynchronized.ref
  val default_params : Proof.context -> (string * string) list -> params
  val setup : theory -> theory
end;

structure Sledgehammer_Isar : SLEDGEHAMMER_ISAR =
struct

open ATP_Systems
open Sledgehammer_Util
open Sledgehammer
open Sledgehammer_Minimize

val auto = Unsynchronized.ref false

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
      (Preferences.bool_pref auto "auto-sledgehammer"
           "Run Sledgehammer automatically.")

(** Sledgehammer commands **)

val no_relevance_override = {add = [], del = [], only = false}
fun add_relevance_override ns : relevance_override =
  {add = ns, del = [], only = false}
fun del_relevance_override ns : relevance_override =
  {add = [], del = ns, only = false}
fun only_relevance_override ns : relevance_override =
  {add = ns, del = [], only = true}
fun merge_relevance_override_pairwise (r1 : relevance_override)
                                      (r2 : relevance_override) =
  {add = #add r1 @ #add r2, del = #del r1 @ #del r2,
   only = #only r1 andalso #only r2}
fun merge_relevance_overrides rs =
  fold merge_relevance_override_pairwise rs (only_relevance_override [])

(*** parameters ***)

val provers = Unsynchronized.ref ""
val timeout = Unsynchronized.ref 30
val full_types = Unsynchronized.ref false

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
      (Preferences.string_pref provers
          "Sledgehammer: Provers"
          "Default automatic provers (separated by whitespace)")

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
      (Preferences.int_pref timeout
          "Sledgehammer: Time Limit"
          "ATPs will be interrupted after this time (in seconds)")

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
      (Preferences.bool_pref full_types
          "Sledgehammer: Full Types" "ATPs will use full type information")

type raw_param = string * string list

val default_default_params =
  [("blocking", "false"),
   ("debug", "false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("explicit_apply", "false"),
   ("relevance_thresholds", "0.45 0.85"),
   ("max_relevant", "smart"),
   ("isar_proof", "false"),
   ("isar_shrink_factor", "1")]

val alias_params =
  [("prover", "provers"),
   ("atps", "provers"), (* FIXME: legacy *)
   ("atp", "provers")]  (* FIXME: legacy *)
val negated_alias_params =
  [("non_blocking", "blocking"),
   ("no_debug", "debug"),
   ("quiet", "verbose"),
   ("no_overlord", "overlord"),
   ("partial_types", "full_types"),
   ("implicit_apply", "explicit_apply"),
   ("no_isar_proof", "isar_proof")]

val params_for_minimize =
  ["debug", "verbose", "overlord", "full_types", "isar_proof",
   "isar_shrink_factor", "timeout"]

val property_dependent_params = ["provers", "full_types", "timeout"]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) property_dependent_params s orelse s = "expect"

fun check_raw_param (s, _) =
  if is_known_raw_param s then ()
  else error ("Unknown parameter: " ^ quote s ^ ".")

fun unalias_raw_param (name, value) =
  case AList.lookup (op =) alias_params name of
    SOME name' => (name', value)
  | NONE =>
    case AList.lookup (op =) negated_alias_params name of
      SOME name' => (name', case value of
                              ["false"] => ["true"]
                            | ["true"] => ["false"]
                            | [] => ["false"]
                            | _ => value)
    | NONE => (name, value)

structure Data = Theory_Data(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  val extend = I
  fun merge p : T = AList.merge (op =) (K true) p)

fun remotify_prover_if_available_and_not_already_remote ctxt name =
  if String.isPrefix remote_prefix name then
    SOME name
  else
    let val remote_name = remote_prefix ^ name in
      if is_prover_available ctxt remote_name then SOME remote_name else NONE
    end

fun remotify_prover_if_not_installed ctxt name =
  if is_prover_available ctxt name andalso is_prover_installed ctxt name then
    SOME name
  else
    remotify_prover_if_available_and_not_already_remote ctxt name

fun avoid_too_many_local_threads _ _ [] = []
  | avoid_too_many_local_threads ctxt 0 provers =
    map_filter (remotify_prover_if_available_and_not_already_remote ctxt)
               provers
  | avoid_too_many_local_threads ctxt n (prover :: provers) =
    let val n = if String.isPrefix remote_prefix prover then n else n - 1 in
      prover :: avoid_too_many_local_threads ctxt n provers
    end

(* The first ATP of the list is used by Auto Sledgehammer. Because of the low
   timeout, it makes sense to put SPASS first. *)
fun default_provers_param_value ctxt =
  [spassN, eN, vampireN, sine_eN, SMT_Solver.solver_name_of ctxt]
  |> map_filter (remotify_prover_if_not_installed ctxt)
  |> avoid_too_many_local_threads ctxt (Multithreading.max_threads_value ())
  |> space_implode " "

val set_default_raw_param = Data.map o AList.update (op =) o unalias_raw_param
fun default_raw_params ctxt =
  let val thy = ProofContext.theory_of ctxt in
    Data.get thy
    |> fold (AList.default (op =))
            [("provers", [case !provers of
                            "" => default_provers_param_value ctxt
                          | s => s]),
             ("full_types", [if !full_types then "true" else "false"]),
             ("timeout", let val timeout = !timeout in
                           [if timeout <= 0 then "none"
                            else string_of_int timeout]
                         end)]
  end

val infinity_time_in_secs = 60 * 60 * 24 * 365
val the_timeout = the_default (Time.fromSeconds infinity_time_in_secs)

fun extract_params auto default_params override_params =
  let
    val override_params = map unalias_raw_param override_params
    val raw_params = rev override_params @ rev default_params
    val lookup = Option.map (space_implode " ") o AList.lookup (op =) raw_params
    val lookup_string = the_default "" o lookup
    fun general_lookup_bool option default_value name =
      case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value
    val lookup_bool = the o general_lookup_bool false (SOME false)
    fun lookup_time name =
      case lookup name of
        SOME s => parse_time_option name s
      | NONE => NONE
    fun lookup_int name =
      case lookup name of
        NONE => 0
      | SOME s => case Int.fromString s of
                    SOME n => n
                  | NONE => error ("Parameter " ^ quote name ^
                                   " must be assigned an integer value.")
    fun lookup_real_pair name =
      case lookup name of
        NONE => (0.0, 0.0)
      | SOME s => case s |> space_explode " " |> map Real.fromString of
                    [SOME r1, SOME r2] => (r1, r2)
                  | _ => error ("Parameter " ^ quote name ^
                                "must be assigned a pair of floating-point \
                                \values (e.g., \"0.6 0.95\")")
    fun lookup_int_option name =
      case lookup name of
        SOME "smart" => NONE
      | _ => SOME (lookup_int name)
    val blocking = auto orelse lookup_bool "blocking"
    val debug = not auto andalso lookup_bool "debug"
    val verbose = debug orelse (not auto andalso lookup_bool "verbose")
    val overlord = lookup_bool "overlord"
    val provers = lookup_string "provers" |> space_explode " "
                  |> auto ? single o hd
    val full_types = lookup_bool "full_types"
    val explicit_apply = lookup_bool "explicit_apply"
    val relevance_thresholds = lookup_real_pair "relevance_thresholds"
    val max_relevant = lookup_int_option "max_relevant"
    val isar_proof = lookup_bool "isar_proof"
    val isar_shrink_factor = Int.max (1, lookup_int "isar_shrink_factor")
    val timeout = (if auto then NONE else lookup_time "timeout") |> the_timeout
    val expect = lookup_string "expect"
  in
    {blocking = blocking, debug = debug, verbose = verbose, overlord = overlord,
     provers = provers, full_types = full_types,
     explicit_apply = explicit_apply,
     relevance_thresholds = relevance_thresholds, max_relevant = max_relevant,
     isar_proof = isar_proof, isar_shrink_factor = isar_shrink_factor,
     timeout = timeout, expect = expect}
  end

fun get_params auto ctxt = extract_params auto (default_raw_params ctxt)
fun default_params thy = get_params false thy o map (apsnd single)

(* Sledgehammer the given subgoal *)

val sledgehammerN = "sledgehammer"
val sledgehammer_paramsN = "sledgehammer_params"

val runN = "run"
val minimizeN = "minimize"
val messagesN = "messages"
val available_proversN = "available_provers"
val running_proversN = "running_provers"
val kill_proversN = "kill_provers"
val refresh_tptpN = "refresh_tptp"

val is_raw_param_relevant_for_minimize =
  member (op =) params_for_minimize o fst o unalias_raw_param
fun string_for_raw_param (key, values) =
  key ^ (case space_implode " " values of "" => "" | value => " = " ^ value)

fun minimize_command override_params i prover_name fact_names =
  sledgehammerN ^ " " ^ minimizeN ^ " [prover = " ^ prover_name ^
  (override_params |> filter is_raw_param_relevant_for_minimize
                   |> implode o map (prefix ", " o string_for_raw_param)) ^
  "] (" ^ space_implode " " fact_names ^ ")" ^
  (if i = 1 then "" else " " ^ string_of_int i)

fun hammer_away override_params subcommand opt_i relevance_override state =
  let
    val ctxt = Proof.context_of state
    val _ = app check_raw_param override_params
  in
    if subcommand = runN then
      let val i = the_default 1 opt_i in
        run_sledgehammer (get_params false ctxt override_params) false i
                         relevance_override (minimize_command override_params i)
                         state
        |> K ()
      end
    else if subcommand = minimizeN then
      run_minimize (get_params false ctxt override_params) (the_default 1 opt_i)
                   (#add relevance_override) state
    else if subcommand = messagesN then
      messages opt_i
    else if subcommand = available_proversN then
      available_provers ctxt
    else if subcommand = running_proversN then
      running_provers ()
    else if subcommand = kill_proversN then
      kill_provers ()
    else if subcommand = refresh_tptpN then
      refresh_systems_on_tptp ()
    else
      error ("Unknown subcommand: " ^ quote subcommand ^ ".")
  end

fun sledgehammer_trans (((subcommand, params), relevance_override), opt_i) =
  Toplevel.keep (hammer_away params subcommand opt_i relevance_override
                 o Toplevel.proof_of)

fun string_for_raw_param (name, value) = name ^ " = " ^ space_implode " " value

fun sledgehammer_params_trans params =
  Toplevel.theory
      (fold set_default_raw_param params
       #> tap (fn thy =>
                  let val ctxt = ProofContext.init_global thy in
                    writeln ("Default parameters for Sledgehammer:\n" ^
                             (case default_raw_params ctxt |> rev of
                                [] => "none"
                              | params =>
                                (map check_raw_param params;
                                 params |> map string_for_raw_param
                                        |> sort_strings |> cat_lines)))
                  end))

val parse_key = Scan.repeat1 Parse.typ_group >> space_implode " "
val parse_value = Scan.repeat1 (Parse.xname || Parse.float_number)
val parse_param = parse_key -- Scan.optional (Parse.$$$ "=" |-- parse_value) []
val parse_params = Scan.optional (Args.bracks (Parse.list parse_param)) []
val parse_fact_refs =
  Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse_Spec.xthm)
val parse_relevance_chunk =
  (Args.add |-- Args.colon |-- parse_fact_refs >> add_relevance_override)
  || (Args.del |-- Args.colon |-- parse_fact_refs >> del_relevance_override)
  || (parse_fact_refs >> only_relevance_override)
val parse_relevance_override =
  Scan.optional (Args.parens (Scan.repeat parse_relevance_chunk
                              >> merge_relevance_overrides))
                no_relevance_override
val parse_sledgehammer_command =
  (Scan.optional Parse.short_ident runN -- parse_params
   -- parse_relevance_override -- Scan.option Parse.nat) #>> sledgehammer_trans
val parse_sledgehammer_params_command =
  parse_params #>> sledgehammer_params_trans

val _ =
  Outer_Syntax.improper_command sledgehammerN
      "search for first-order proof using automatic theorem provers" Keyword.diag
      parse_sledgehammer_command
val _ =
  Outer_Syntax.command sledgehammer_paramsN
      "set and display the default parameters for Sledgehammer" Keyword.thy_decl
      parse_sledgehammer_params_command

fun auto_sledgehammer state =
  let val ctxt = Proof.context_of state in
    run_sledgehammer (get_params true ctxt []) true 1 no_relevance_override
                     (minimize_command [] 1) state
  end

val setup = Auto_Tools.register_tool (auto, auto_sledgehammer)

end;
