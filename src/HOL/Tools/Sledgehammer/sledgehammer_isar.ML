(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
*)

signature SLEDGEHAMMER_ISAR =
sig
  type params = ATP_Manager.params

  val atps: string Unsynchronized.ref
  val timeout: int Unsynchronized.ref
  val full_types: bool Unsynchronized.ref
  val default_params : theory -> (string * string) list -> params
  val setup: theory -> theory
end;

structure Sledgehammer_Isar : SLEDGEHAMMER_ISAR =
struct

open Sledgehammer_Util
open Sledgehammer_Fact_Filter
open Sledgehammer_Fact_Preprocessor
open ATP_Manager
open ATP_Systems
open Sledgehammer_Fact_Minimizer

(** Proof method used in Isar proofs **)

val neg_clausify_setup =
  Method.setup @{binding neg_clausify}
               (Scan.succeed (SIMPLE_METHOD' o neg_clausify_tac)
                o tap (fn _ => legacy_feature "Old 'neg_clausify' method -- \
                                   \rerun Sledgehammer to obtain a direct \
                                   \proof"))
               "conversion of goal to negated conjecture clauses (legacy)"

(** Attribute for converting a theorem into clauses **)

val parse_clausify_attribute : attribute context_parser =
  Scan.lift Parse.nat
  >> (fn i => Thm.rule_attribute (fn context => fn th =>
                  let val thy = Context.theory_of context in
                    Meson.make_meta_clause (nth (cnf_axiom thy th) i)
                  end))

val clausify_setup =
  Attrib.setup @{binding clausify}
               (parse_clausify_attribute
                o tap (fn _ => legacy_feature "Old 'clausify' attribute"))
               "conversion of theorem to clauses"

(** Sledgehammer commands **)

fun add_to_relevance_override ns : relevance_override =
  {add = ns, del = [], only = false}
fun del_from_relevance_override ns : relevance_override =
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

val atps = Unsynchronized.ref ""
val timeout = Unsynchronized.ref 60
val full_types = Unsynchronized.ref false

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
      (Preferences.string_pref atps
          "Sledgehammer: ATPs"
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
  [("debug", "false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("explicit_apply", "false"),
   ("respect_no_atp", "true"),
   ("relevance_threshold", "50"),
   ("relevance_convergence", "320"),
   ("theory_relevant", "smart"),
   ("defs_relevant", "false"),
   ("isar_proof", "false"),
   ("isar_shrink_factor", "1"),
   ("minimize_timeout", "5 s")]

val alias_params =
  [("atp", "atps")]
val negated_alias_params =
  [("no_debug", "debug"),
   ("quiet", "verbose"),
   ("no_overlord", "overlord"),
   ("partial_types", "full_types"),
   ("implicit_apply", "explicit_apply"),
   ("ignore_no_atp", "respect_no_atp"),
   ("theory_irrelevant", "theory_relevant"),
   ("defs_irrelevant", "defs_relevant"),
   ("no_isar_proof", "isar_proof")]

val params_for_minimize =
  ["debug", "verbose", "overlord", "full_types", "explicit_apply",
   "isar_proof", "isar_shrink_factor", "minimize_timeout"]

val property_dependent_params = ["atps", "full_types", "timeout"]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) property_dependent_params s

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

val set_default_raw_param = Data.map o AList.update (op =) o unalias_raw_param
fun default_raw_params thy =
  Data.get thy
  |> fold (AList.default (op =))
          [("atps", [case !atps of "" => default_atps_param_value () | s => s]),
           ("full_types", [if !full_types then "true" else "false"]),
           ("timeout", let val timeout = !timeout in
                         [if timeout <= 0 then "none"
                          else string_of_int timeout ^ " s"]
                       end)]

val infinity_time_in_secs = 60 * 60 * 24 * 365
val the_timeout = the_default (Time.fromSeconds infinity_time_in_secs)

fun extract_params default_params override_params =
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
    val lookup_bool_option = general_lookup_bool true NONE
    fun lookup_time name =
      the_timeout (case lookup name of
                     NONE => NONE
                   | SOME s => parse_time_option name s)
    fun lookup_int name =
      case lookup name of
        NONE => 0
      | SOME s => case Int.fromString s of
                    SOME n => n
                  | NONE => error ("Parameter " ^ quote name ^
                                   " must be assigned an integer value.")
    val debug = lookup_bool "debug"
    val verbose = debug orelse lookup_bool "verbose"
    val overlord = lookup_bool "overlord"
    val atps = lookup_string "atps" |> space_explode " "
    val full_types = lookup_bool "full_types"
    val explicit_apply = lookup_bool "explicit_apply"
    val respect_no_atp = lookup_bool "respect_no_atp"
    val relevance_threshold =
      0.01 * Real.fromInt (lookup_int "relevance_threshold")
    val relevance_convergence =
      0.01 * Real.fromInt (lookup_int "relevance_convergence")
    val theory_relevant = lookup_bool_option "theory_relevant"
    val defs_relevant = lookup_bool "defs_relevant"
    val isar_proof = lookup_bool "isar_proof"
    val isar_shrink_factor = Int.max (1, lookup_int "isar_shrink_factor")
    val timeout = lookup_time "timeout"
    val minimize_timeout = lookup_time "minimize_timeout"
  in
    {debug = debug, verbose = verbose, overlord = overlord, atps = atps,
     full_types = full_types, explicit_apply = explicit_apply,
     respect_no_atp = respect_no_atp, relevance_threshold = relevance_threshold,
     relevance_convergence = relevance_convergence,
     theory_relevant = theory_relevant, defs_relevant = defs_relevant,
     isar_proof = isar_proof, isar_shrink_factor = isar_shrink_factor,
     timeout = timeout, minimize_timeout = minimize_timeout}
  end

fun get_params thy = extract_params (default_raw_params thy)
fun default_params thy = get_params thy o map (apsnd single)

val subgoal_count = Logic.count_prems o prop_of o #goal o Proof.goal

(* Sledgehammer the given subgoal *)

fun run {atps = [], ...} _ _ _ _ = error "No ATP is set."
  | run (params as {atps, timeout, ...}) i relevance_override minimize_command
        state =
    case subgoal_count state of
      0 => priority "No subgoal!"
    | n =>
      let
        val birth_time = Time.now ()
        val death_time = Time.+ (birth_time, timeout)
        val _ = kill_atps ()
        val _ = priority "Sledgehammering..."
        val _ = app (start_prover_thread params birth_time death_time i n
                                         relevance_override minimize_command
                                         state) atps
      in () end

fun minimize override_params i refs state =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val chained_ths = #facts (Proof.goal state)
    val name_thms_pairs = map (name_thms_pair_from_ref ctxt chained_ths) refs
  in
    case subgoal_count state of
      0 => priority "No subgoal!"
    | n =>
      (kill_atps ();
       priority (#2 (minimize_theorems (get_params thy override_params) i n
                                       state name_thms_pairs)))
  end

val sledgehammerN = "sledgehammer"
val sledgehammer_paramsN = "sledgehammer_params"

val runN = "run"
val minimizeN = "minimize"
val messagesN = "messages"
val available_atpsN = "available_atps"
val running_atpsN = "running_atps"
val kill_atpsN = "kill_atps"
val refresh_tptpN = "refresh_tptp"

fun minimizize_raw_param_name "timeout" = "minimize_timeout"
  | minimizize_raw_param_name name = name

val is_raw_param_relevant_for_minimize =
  member (op =) params_for_minimize o fst o unalias_raw_param
fun string_for_raw_param (key, values) =
  key ^ (case space_implode " " values of "" => "" | value => " = " ^ value)

fun minimize_command override_params i atp_name fact_names =
  sledgehammerN ^ " " ^ minimizeN ^ " [atp = " ^ atp_name ^
  (override_params |> filter is_raw_param_relevant_for_minimize
                   |> implode o map (prefix ", " o string_for_raw_param)) ^
  "] (" ^ space_implode " " fact_names ^ ")" ^
  (if i = 1 then "" else " " ^ string_of_int i)

fun hammer_away override_params subcommand opt_i relevance_override state =
  let
    val thy = Proof.theory_of state
    val _ = app check_raw_param override_params
  in
    if subcommand = runN then
      let val i = the_default 1 opt_i in
        run (get_params thy override_params) i relevance_override
            (minimize_command override_params i) state
      end
    else if subcommand = minimizeN then
      minimize (map (apfst minimizize_raw_param_name) override_params)
               (the_default 1 opt_i) (#add relevance_override) state
    else if subcommand = messagesN then
      messages opt_i
    else if subcommand = available_atpsN then
      available_atps thy
    else if subcommand = running_atpsN then
      running_atps ()
    else if subcommand = kill_atpsN then
      kill_atps ()
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
                  writeln ("Default parameters for Sledgehammer:\n" ^
                           (case rev (default_raw_params thy) of
                              [] => "none"
                            | params =>
                              (map check_raw_param params;
                               params |> map string_for_raw_param
                                      |> sort_strings |> cat_lines)))))

val parse_key = Scan.repeat1 Parse.typ_group >> space_implode " "
val parse_value = Scan.repeat1 Parse.xname
val parse_param = parse_key -- Scan.optional (Parse.$$$ "=" |-- parse_value) []
val parse_params = Scan.optional (Args.bracks (Parse.list parse_param)) []
val parse_fact_refs =
  Scan.repeat1 (Scan.unless (Parse.name -- Args.colon)
                            (Parse.xname -- Scan.option Attrib.thm_sel)
                >> (fn (name, interval) =>
                       Facts.Named ((name, Position.none), interval)))
val parse_relevance_chunk =
  (Args.add |-- Args.colon |-- parse_fact_refs >> add_to_relevance_override)
  || (Args.del |-- Args.colon |-- parse_fact_refs
      >> del_from_relevance_override)
  || (parse_fact_refs >> only_relevance_override)
val parse_relevance_override =
  Scan.optional (Args.parens (Scan.repeat parse_relevance_chunk
                              >> merge_relevance_overrides))
                (add_to_relevance_override [])
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

val setup =
  neg_clausify_setup
  #> clausify_setup

end;
