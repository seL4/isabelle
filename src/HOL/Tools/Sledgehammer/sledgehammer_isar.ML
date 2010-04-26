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
open Sledgehammer_Fact_Preprocessor
open ATP_Manager
open ATP_Systems
open Sledgehammer_Fact_Minimizer

structure K = OuterKeyword and P = OuterParse

(** Proof method used in Isar proofs **)

val neg_clausify_setup =
  Method.setup @{binding neg_clausify}
               (Scan.succeed (SIMPLE_METHOD' o neg_clausify_tac))
               "conversion of goal to negated conjecture clauses"

(** Attribute for converting a theorem into clauses **)

val parse_clausify_attribute =
  Scan.lift OuterParse.nat
  >> (fn i => Thm.rule_attribute (fn context => fn th =>
                  let val thy = Context.theory_of context in
                    Meson.make_meta_clause (nth (cnf_axiom thy th) i)
                  end))

val clausify_setup =
  Attrib.setup @{binding clausify} parse_clausify_attribute
               "conversion of theorem to clauses"

(** Sledgehammer commands **)

fun add_to_relevance_override ns : relevance_override =
  {add = ns, del = [], only = false}
fun del_from_relevance_override ns : relevance_override =
  {add = [], del = ns, only = false}
fun only_relevance_override ns : relevance_override =
  {add = ns, del = [], only = true}
val no_relevance_override = add_to_relevance_override []
fun merge_relevance_override_pairwise (r1 : relevance_override)
                                      (r2 : relevance_override) =
  {add = #add r1 @ #add r2, del = #del r1 @ #del r2,
   only = #only r1 andalso #only r2}
fun merge_relevance_overrides rs =
  fold merge_relevance_override_pairwise rs (only_relevance_override [])

(*** parameters ***)

val atps = Unsynchronized.ref (default_atps_param_value ())
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
   ("convergence", "320"),
   ("theory_relevant", "smart"),
   ("higher_order", "smart"),
   ("follow_defs", "false"),
   ("isar_proof", "false"),
   ("shrink_factor", "1"),
   ("sorts", "false"),
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
   ("first_order", "higher_order"),
   ("dont_follow_defs", "follow_defs"),
   ("metis_proof", "isar_proof"),
   ("no_sorts", "sorts")]

val params_for_minimize =
  ["debug", "verbose", "overlord", "full_types", "explicit_apply",
   "higher_order", "isar_proof", "shrink_factor", "sorts", "minimize_timeout"]

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
          [("atps", [!atps]),
           ("full_types", [if !full_types then "true" else "false"]),
           ("timeout", let val timeout = !timeout in
                         [if timeout <= 0 then "none"
                          else string_of_int timeout ^ " s"]
                       end)]

val infinity_time_in_secs = 60 * 60 * 24 * 365
val the_timeout = the_default (Time.fromSeconds infinity_time_in_secs)

fun extract_params thy default_params override_params =
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
    val convergence = 0.01 * Real.fromInt (lookup_int "convergence")
    val theory_relevant = lookup_bool_option "theory_relevant"
    val higher_order = lookup_bool_option "higher_order"
    val follow_defs = lookup_bool "follow_defs"
    val isar_proof = lookup_bool "isar_proof"
    val shrink_factor = Int.max (1, lookup_int "shrink_factor")
    val sorts = lookup_bool "sorts"
    val timeout = lookup_time "timeout"
    val minimize_timeout = lookup_time "minimize_timeout"
  in
    {debug = debug, verbose = verbose, overlord = overlord, atps = atps,
     full_types = full_types, explicit_apply = explicit_apply,
     respect_no_atp = respect_no_atp, relevance_threshold = relevance_threshold,
     convergence = convergence, theory_relevant = theory_relevant,
     higher_order = higher_order, follow_defs = follow_defs,
     isar_proof = isar_proof, shrink_factor = shrink_factor, sorts = sorts,
     timeout = timeout, minimize_timeout = minimize_timeout}
  end

fun get_params thy = extract_params thy (default_raw_params thy)
fun default_params thy = get_params thy o map (apsnd single)

(* Sledgehammer the given subgoal *)

fun run {atps = [], ...} _ _ _ _ = error "No ATP is set."
  | run (params as {atps, timeout, ...}) i relevance_override minimize_command
        proof_state =
    let
      val birth_time = Time.now ()
      val death_time = Time.+ (birth_time, timeout)
      val _ = kill_atps ()  (* race w.r.t. other invocations of Sledgehammer *)
      val _ = priority "Sledgehammering..."
      val _ = List.app (start_prover_thread params birth_time death_time i
                                            relevance_override minimize_command
                                            proof_state) atps
    in () end

fun minimize override_params i fact_refs state =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val theorems_from_refs =
      map o pairf Facts.string_of_ref o ProofContext.get_fact
    val name_thms_pairs = theorems_from_refs ctxt fact_refs
  in
    priority (#2 (minimize_theorems (get_params thy override_params) i state
                                    name_thms_pairs))
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
val helpN = "help"

fun minimizize_raw_param_name "timeout" = "minimize_timeout"
  | minimizize_raw_param_name name = name

val is_raw_param_relevant_for_minimize =
  member (op =) params_for_minimize o fst o unalias_raw_param
fun string_for_raw_param (key, values) =
  key ^ (case space_implode " " values of
           "" => ""
         | value => " = " ^ value)

fun minimize_command override_params i atp_name facts =
  sledgehammerN ^ " " ^ minimizeN ^ " [atp = " ^ atp_name ^
  (override_params |> filter is_raw_param_relevant_for_minimize
                   |> implode o map (prefix ", " o string_for_raw_param)) ^
  "] (" ^ space_implode " " facts ^ ")" ^
  (if i = 1 then "" else " " ^ string_of_int i)

fun hammer_away override_params subcommand opt_i relevance_override state =
  let
    val thy = Proof.theory_of state
    val _ = List.app check_raw_param override_params
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

val parse_key = Scan.repeat1 P.typ_group >> space_implode " "
val parse_value = Scan.repeat1 P.xname
val parse_param = parse_key -- Scan.optional (P.$$$ "=" |-- parse_value) []
val parse_params = Scan.optional (Args.bracks (P.list parse_param)) []
val parse_fact_refs =
  Scan.repeat1 (Scan.unless (P.name -- Args.colon)
                            (P.xname -- Scan.option Attrib.thm_sel)
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
  (Scan.optional P.short_ident runN -- parse_params -- parse_relevance_override
   -- Scan.option P.nat) #>> sledgehammer_trans
val parse_sledgehammer_params_command =
  parse_params #>> sledgehammer_params_trans

val _ =
  OuterSyntax.improper_command sledgehammerN
      "search for first-order proof using automatic theorem provers" K.diag
      parse_sledgehammer_command
val _ =
  OuterSyntax.command sledgehammer_paramsN
      "set and display the default parameters for Sledgehammer" K.thy_decl
      parse_sledgehammer_params_command

val setup =
  neg_clausify_setup
  #> clausify_setup

end;
