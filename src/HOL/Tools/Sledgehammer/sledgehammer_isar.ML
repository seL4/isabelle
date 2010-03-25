(*  Title:      HOL/Sledgehammer/sledgehammer_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
*)

signature SLEDGEHAMMER_ISAR =
sig
  type params = ATP_Manager.params

  val default_params : theory -> (string * string) list -> params
end;

structure Sledgehammer_Isar : SLEDGEHAMMER_ISAR =
struct

open Sledgehammer_Util
open ATP_Manager
open ATP_Minimal
open ATP_Wrapper

structure K = OuterKeyword and P = OuterParse

fun add_to_relevance_override ns : relevance_override =
  {add = ns, del = [], only = false}
fun del_from_relevance_override ns : relevance_override =
  {add = [], del = ns, only = false}
fun only_relevance_override ns : relevance_override =
  {add = ns, del = [], only = true}
val default_relevance_override = add_to_relevance_override []
fun merge_relevance_override_pairwise r1 r2 : relevance_override =
  {add = #add r1 @ #add r2, del = #del r1 @ #del r2,
   only = #only r1 orelse #only r2} 
fun merge_relevance_overrides rs =
  fold merge_relevance_override_pairwise rs default_relevance_override

type raw_param = string * string list

val default_default_params =
  [("debug", "false"),
   ("verbose", "false"),
   ("relevance_threshold", "50"),
   ("higher_order", "smart"),
   ("respect_no_atp", "true"),
   ("follow_defs", "false"),
   ("isar_proof", "false"),
   ("minimize_timeout", "5 s")]

val negated_params =
  [("no_debug", "debug"),
   ("quiet", "verbose"),
   ("partial_types", "full_types"),
   ("first_order", "higher_order"),
   ("ignore_no_atp", "respect_no_atp"),
   ("dont_follow_defs", "follow_defs"),
   ("metis_proof", "isar_proof")]

val property_dependent_params = ["atps", "full_types", "timeout"]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) negated_params s orelse
  member (op =) property_dependent_params s

fun check_raw_param (s, _) =
  if is_known_raw_param s then ()
  else error ("Unknown parameter: " ^ quote s ^ ".")

fun unnegate_raw_param (name, value) =
  case AList.lookup (op =) negated_params name of
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

val set_default_raw_param = Data.map o AList.update (op =) o unnegate_raw_param
fun default_raw_params thy =
  [("atps", [!atps]),
   ("full_types", [if !full_types then "true" else "false"]),
   ("timeout", [string_of_int (!timeout) ^ " s"])] @
  Data.get thy

val infinity_time_in_secs = 60 * 60 * 24 * 365
val the_timeout = the_default (Time.fromSeconds infinity_time_in_secs)

fun extract_params thy default_params override_params =
  let
    val override_params = map unnegate_raw_param override_params
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
    val atps = lookup_string "atps" |> space_explode " "
    val full_types = lookup_bool "full_types"
    val relevance_threshold =
      0.01 * Real.fromInt (lookup_int "relevance_threshold")
    val higher_order = lookup_bool_option "higher_order"
    val respect_no_atp = lookup_bool "respect_no_atp"
    val follow_defs = lookup_bool "follow_defs"
    val isar_proof = lookup_bool "isar_proof"
    val timeout = lookup_time "timeout"
    val minimize_timeout = lookup_time "minimize_timeout"
  in
    {debug = debug, verbose = verbose, atps = atps, full_types = full_types,
     relevance_threshold = relevance_threshold, higher_order = higher_order,
     respect_no_atp = respect_no_atp, follow_defs = follow_defs,
     isar_proof = isar_proof, timeout = timeout,
     minimize_timeout = minimize_timeout}
  end

fun get_params thy = extract_params thy (default_raw_params thy)
fun default_params thy = get_params thy o map (apsnd single)

fun atp_minimize_command override_params old_style_args fact_refs state =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    fun theorems_from_refs ctxt =
      map (fn fact_ref =>
              let
                val ths = ProofContext.get_fact ctxt fact_ref
                val name' = Facts.string_of_ref fact_ref
              in (name', ths) end)
    fun get_time_limit_arg s =
      (case Int.fromString s of
        SOME t => Time.fromSeconds t
      | NONE => error ("Invalid time limit: " ^ quote s))
    fun get_opt (name, a) (p, t) =
      (case name of
        "time" => (p, get_time_limit_arg a)
      | "atp" => (a, t)
      | n => error ("Invalid argument: " ^ n))
    val {atps, minimize_timeout, ...} = get_params thy override_params
    val (atp, timeout) = fold get_opt old_style_args (hd atps, minimize_timeout)
    val params =
      get_params thy
          [("atps", [atp]),
           ("minimize_timeout",
            [string_of_int (Time.toSeconds timeout) ^ " s"])]
    val prover =
      (case get_prover thy atp of
        SOME prover => prover
      | NONE => error ("Unknown ATP: " ^ quote atp))
    val name_thms_pairs = theorems_from_refs ctxt fact_refs
  in
    writeln (#2 (minimize_theorems params linear_minimize prover atp state
                                   name_thms_pairs))
  end

val runN = "run"
val minimizeN = "minimize"
val messagesN = "messages"
val available_atpsN = "available_atps"
val running_atpsN = "running_atps"
val kill_atpsN = "kill_atps"
val refresh_tptpN = "refresh_tptp"
val helpN = "help"

val addN = "add"
val delN = "del"
val onlyN = "only"

fun hammer_away override_params subcommand opt_i relevance_override state =
  let
    val thy = Proof.theory_of state
    val _ = List.app check_raw_param override_params
  in
    if subcommand = runN then
      sledgehammer (get_params thy override_params) (the_default 1 opt_i)
                   relevance_override state
    else if subcommand = minimizeN then
      atp_minimize_command override_params [] (#add relevance_override) state
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
  || (P.$$$ onlyN |-- Args.colon |-- parse_fact_refs >> only_relevance_override)
val parse_relevance_override =
  Scan.optional (Args.parens
      (Scan.optional (parse_fact_refs >> only_relevance_override)
                     default_relevance_override
       -- Scan.repeat parse_relevance_chunk)
       >> op :: >> merge_relevance_overrides)
      default_relevance_override
val parse_sledgehammer_command =
  (Scan.optional P.short_ident runN -- parse_params -- parse_relevance_override
   -- Scan.option P.nat) #>> sledgehammer_trans
val parse_sledgehammer_params_command =
  parse_params #>> sledgehammer_params_trans

val parse_minimize_args =
  Scan.optional (Args.bracks (P.list (P.short_ident --| P.$$$ "=" -- P.xname)))
                []
val _ =
  OuterSyntax.improper_command "atp_kill" "kill all managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative kill_atps))
val _ =
  OuterSyntax.improper_command "atp_info"
    "print information about managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative running_atps))
val _ =
  OuterSyntax.improper_command "atp_messages"
    "print recent messages issued by managed provers" K.diag
    (Scan.option (P.$$$ "(" |-- P.nat --| P.$$$ ")") >>
      (fn limit => Toplevel.no_timing
                   o Toplevel.imperative (fn () => messages limit)))
val _ =
  OuterSyntax.improper_command "print_atps" "print external provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory o
      Toplevel.keep (available_atps o Toplevel.theory_of)))
val _ =
  OuterSyntax.improper_command "atp_minimize"
    "minimize theorem list with external prover" K.diag
    (parse_minimize_args -- parse_fact_refs >> (fn (args, fact_refs) =>
      Toplevel.no_timing o Toplevel.unknown_proof o
        Toplevel.keep (atp_minimize_command [] args fact_refs
                       o Toplevel.proof_of)))

val _ =
  OuterSyntax.improper_command "sledgehammer"
    "search for first-order proof using automatic theorem provers" K.diag
    parse_sledgehammer_command
val _ =
  OuterSyntax.command "sledgehammer_params"
    "set and display the default parameters for Sledgehammer" K.thy_decl
    parse_sledgehammer_params_command

end;
