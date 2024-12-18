(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_commands.ML
    Author:     Jasmin Blanchette, TU Muenchen

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
*)

signature SLEDGEHAMMER_COMMANDS =
sig
  type params = Sledgehammer_Prover.params

  val provers : string Unsynchronized.ref
  val default_params : theory -> (string * string) list -> params
  val parse_params: (string * string) list parser
end;

structure Sledgehammer_Commands : SLEDGEHAMMER_COMMANDS =
struct

open ATP_Util
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover
open Sledgehammer_Prover_SMT
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh
open Sledgehammer

val runN = "run"
val supported_proversN = "supported_provers"
val refresh_tptpN = "refresh_tptp"

(** Sledgehammer commands **)

fun add_fact_override ns : fact_override = {add = ns, del = [], only = false}
fun del_fact_override ns : fact_override = {add = [], del = ns, only = false}
fun only_fact_override ns : fact_override = {add = ns, del = [], only = true}
fun merge_fact_override_pairwise (r1 : fact_override) (r2 : fact_override) =
  {add = #add r1 @ #add r2, del = #del r1 @ #del r2, only = #only r1 andalso #only r2}
fun merge_fact_overrides rs = fold merge_fact_override_pairwise rs (only_fact_override [])

(*** parameters ***)

val provers = Unsynchronized.ref ""

type raw_param = string * string list

val default_default_params =
  [("debug", "false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("spy", "false"),
   ("abduce", "0"),
   ("falsify", "false"),
   ("type_enc", "smart"),
   ("strict", "false"),
   ("lam_trans", "smart"),
   ("uncurried_aliases", "smart"),
   ("learn", "true"),
   ("fact_filter", "smart"),
   ("induction_rules", "smart"),
   ("max_facts", "smart"),
   ("fact_thresholds", "0.45 0.85"),
   ("max_mono_iters", "smart"),
   ("max_new_mono_instances", "smart"),
   ("max_proofs", "4"),
   ("isar_proofs", "smart"),
   ("compress", "smart"),
   ("try0", "true"),
   ("smt_proofs", "true"),
   ("suggest_of", "smart"),
   ("minimize", "true"),
   ("slices", string_of_int (12 * Multithreading.max_threads ())),
   ("preplay_timeout", "1"),
   ("cache_dir", "")]

val alias_params =
  [("prover", ("provers", [])), (* undocumented *)
   ("dont_abduce", ("abduce", ["0"])),
   ("dont_preplay", ("preplay_timeout", ["0"])),
   ("dont_compress", ("compress", ["1"])),
   ("dont_slice", ("slices", ["1"])),
   ("isar_proof", ("isar_proofs", [])) (* legacy *)]
val negated_alias_params =
  [("no_debug", "debug"),
   ("quiet", "verbose"),
   ("no_overlord", "overlord"),
   ("dont_spy", "spy"),
   ("dont_falsify", "falsify"),
   ("non_strict", "strict"),
   ("no_uncurried_aliases", "uncurried_aliases"),
   ("dont_learn", "learn"),
   ("no_isar_proofs", "isar_proofs"),
   ("dont_minimize", "minimize"),
   ("dont_try0", "try0"),
   ("no_smt_proofs", "smt_proofs"),
   ("dont_suggest_of", "suggest_of")]

val property_dependent_params = ["provers", "timeout"]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) property_dependent_params s orelse s = "expect"

fun is_prover_list ctxt s =
  (case space_explode " " s of
    ss as _ :: _ => forall (is_prover_supported ctxt) ss
  | _ => false)

fun unalias_raw_param (name, value) =
  (case AList.lookup (op =) alias_params name of
    SOME (name', []) => (name', value)
  | SOME (param' as (name', _)) =>
    if value <> ["false"] then
      param'
    else
      error ("Parameter " ^ quote name ^ " cannot be set to \"false\" (cf. " ^ quote name' ^ ")")
  | NONE =>
    (case AList.lookup (op =) negated_alias_params name of
      SOME name' => (name',
        (case value of
          ["false"] => ["true"]
        | ["true"] => ["false"]
        | [] => ["false"]
        | _ => value))
    | NONE => (name, value)))

val any_type_enc = type_enc_of_string Strict "erased"

(* "provers =", "type_enc =", "lam_trans =", "fact_filter =", and "max_facts ="
   can be omitted. For the last four, this is a secret feature. *)
fun normalize_raw_param ctxt =
  unalias_raw_param
  #> (fn (name, value) =>
         if is_known_raw_param name then
           (name, value)
         else if null value then
           if is_prover_list ctxt name then
             ("provers", [name])
           else if can (type_enc_of_string Strict) name then
             ("type_enc", [name])
           else if can (trans_lams_of_string ctxt any_type_enc) name then
             ("lam_trans", [name])
           else if member (op =) fact_filters name then
             ("fact_filter", [name])
           else if is_some (Int.fromString name) then
             ("max_facts", [name])
           else
             error ("Unknown parameter: " ^ quote name)
         else
           error ("Unknown parameter: " ^ quote name))

(* Ensures that type encodings such as "mono_native?" and "poly_guards!!" are
   read correctly. *)
val implode_param = strip_spaces_except_between_idents o implode_space

(* FIXME: use "Generic_Data" *)
structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  fun merge data : T = AList.merge (op =) (K true) data
)

(* The first ATP of the list is used by Auto Sledgehammer. *)
fun default_provers_param_value ctxt =
  \<comment> \<open>see also \<^system_option>\<open>sledgehammer_provers\<close>\<close>
  filter (is_prover_installed ctxt) (smts ctxt @ local_atps)
  |> implode_param

fun set_default_raw_param param thy =
  let val ctxt = Proof_Context.init_global thy in
    thy |> Data.map (AList.update (op =) (normalize_raw_param ctxt param))
  end

fun default_raw_params thy =
  let val ctxt = Proof_Context.init_global thy in
    Data.get thy
    |> fold (AList.default (op =))
       [("provers", [(case !provers of "" => default_provers_param_value ctxt | s => s)]),
        ("timeout",
         let val timeout = Options.default_int \<^system_option>\<open>sledgehammer_timeout\<close> in
           [if timeout <= 0 then "none" else string_of_int timeout]
         end)]
  end

fun extract_params mode default_params override_params =
  let
    val raw_params = rev override_params @ rev default_params
    val lookup = Option.map implode_param o AList.lookup (op =) raw_params
    val lookup_string = the_default "" o lookup

    fun general_lookup_bool option default_value name =
      (case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value)
    val lookup_bool = the o general_lookup_bool false (SOME false)
    fun lookup_time name =
      (case lookup name of
        SOME s => parse_time name s
      | NONE => Time.zeroTime)
    fun lookup_int name =
      (case lookup name of
        NONE => 0
      | SOME s =>
        (case Int.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned an integer value")))
    fun lookup_real name =
      (case lookup name of
        NONE => 0.0
      | SOME s =>
        (case Real.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned a real value")))
    fun lookup_real_pair name =
      (case lookup name of
        NONE => (0.0, 0.0)
      | SOME s =>
        (case s |> space_explode " " |> map Real.fromString of
          [SOME r1, SOME r2] => (r1, r2)
        | _ => error ("Parameter " ^ quote name ^ " must be assigned a pair of floating-point \
                 \values (e.g., \"0.6 0.95\")")))
    fun lookup_option lookup' name =
      (case lookup name of
        SOME "smart" => NONE
      | _ => SOME (lookup' name))
    val debug = mode <> Auto_Try andalso lookup_bool "debug"
    val verbose = debug orelse (mode <> Auto_Try andalso lookup_bool "verbose")
    val overlord = lookup_bool "overlord"
    val spy = getenv "SLEDGEHAMMER_SPY" = "yes" orelse lookup_bool "spy"
    val provers = lookup_string "provers" |> space_explode " " |> mode = Auto_Try ? single o hd
    val abduce =
      if mode = Auto_Try then SOME 0
      else lookup_option lookup_int "abduce"
    val falsify =
      if mode = Auto_Try then SOME false
      else lookup_option lookup_bool "falsify"
    val type_enc =
      if mode = Auto_Try then
        NONE
      else
        (case lookup_string "type_enc" of
          "smart" => NONE
        | s => (type_enc_of_string Strict s; SOME s))
    val strict = mode = Auto_Try orelse lookup_bool "strict"
    val lam_trans = lookup_option lookup_string "lam_trans"
    val uncurried_aliases = lookup_option lookup_bool "uncurried_aliases"
    val learn = lookup_bool "learn"
    val fact_filter =
      lookup_option lookup_string "fact_filter"
      |> mode = Auto_Try ? (fn NONE => SOME mepoN | sf => sf)
    val induction_rules =
      lookup_option (the o induction_rules_of_string o lookup_string) "induction_rules"
    val max_facts = lookup_option lookup_int "max_facts"
    val fact_thresholds = lookup_real_pair "fact_thresholds"
    val max_mono_iters = lookup_option lookup_int "max_mono_iters"
    val max_new_mono_instances =
      lookup_option lookup_int "max_new_mono_instances"
    val max_proofs = lookup_int "max_proofs"
    val isar_proofs = lookup_option lookup_bool "isar_proofs"
    val compress = Option.map (curry Real.max 1.0) (lookup_option lookup_real "compress")
    val try0 = lookup_bool "try0"
    val smt_proofs = lookup_bool "smt_proofs"
    val suggest_of = lookup_option lookup_bool "suggest_of"
    val minimize = mode <> Auto_Try andalso lookup_bool "minimize"
    val slices = if mode = Auto_Try then 1 else Int.max (1, lookup_int "slices")
    val timeout = lookup_time "timeout"
    val preplay_timeout = lookup_time "preplay_timeout"
    val expect = lookup_string "expect"
    val cache_dir = Option.mapPartial
      (fn str => if str = "" then NONE else SOME (Path.explode str)) (lookup "cache_dir")
  in
    {debug = debug, verbose = verbose, overlord = overlord, spy = spy, provers = provers,
     abduce = abduce, falsify = falsify, type_enc = type_enc, strict = strict,
     lam_trans = lam_trans, uncurried_aliases = uncurried_aliases, learn = learn,
     fact_filter = fact_filter, induction_rules = induction_rules, max_facts = max_facts,
     fact_thresholds = fact_thresholds, max_mono_iters = max_mono_iters,
     max_new_mono_instances = max_new_mono_instances, max_proofs = max_proofs,
     isar_proofs = isar_proofs, compress = compress, try0 = try0, smt_proofs = smt_proofs,
     suggest_of = suggest_of, minimize = minimize, slices = slices, timeout = timeout,
     preplay_timeout = preplay_timeout, expect = expect, cache_dir = cache_dir}
  end

fun get_params mode = extract_params mode o default_raw_params
fun default_params thy = get_params Normal thy o map (apsnd single)

val silence_state =
  Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose false)

(* Sledgehammer the given subgoal *)

val default_learn_prover_timeout = 2.0

fun hammer_away override_params writeln_result subcommand opt_i fact_override state0 =
  let
    val state = silence_state state0
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val override_params = override_params |> map (normalize_raw_param ctxt)
  in
    if subcommand = runN then
      let val i = the_default 1 opt_i in
        ignore (run_sledgehammer
          (get_params Normal thy override_params) Normal writeln_result i fact_override state)
      end
    else if subcommand = supported_proversN then
      supported_provers ctxt
    else if subcommand = unlearnN then
      mash_unlearn ctxt
    else if subcommand = learn_isarN orelse subcommand = learn_proverN orelse
            subcommand = relearn_isarN orelse subcommand = relearn_proverN then
      (if subcommand = relearn_isarN orelse subcommand = relearn_proverN then mash_unlearn ctxt
       else ();
       mash_learn ctxt
           (* TODO: Use MaSh mode instead and have the special defaults hardcoded in "get_params". *)
           (get_params Normal thy
                ([("timeout", [string_of_real default_learn_prover_timeout]),
                  ("slice", ["false"])] @
                 override_params @
                 [("preplay_timeout", ["0"])]))
           fact_override (#facts (Proof.goal state))
           (subcommand = learn_proverN orelse subcommand = relearn_proverN))
    else if subcommand = refresh_tptpN then
      refresh_systems_on_tptp ()
    else
      error ("Unknown subcommand: " ^ quote subcommand)
  end

fun string_of_raw_param (key, values) =
  key ^ (case implode_param values of "" => "" | value => " = " ^ value)

val parse_query_bang = \<^keyword>\<open>?\<close> || \<^keyword>\<open>!\<close> || \<^keyword>\<open>!!\<close>
val parse_key = Scan.repeat1 (Parse.embedded || parse_query_bang) >> implode_param
val parse_value = Scan.repeat1 (Parse.name || Parse.float_number || parse_query_bang)
val parse_param = parse_key -- Scan.optional (\<^keyword>\<open>=\<close> |-- parse_value) []
val parse_raw_params = Scan.optional (Args.bracks (Parse.list parse_param)) []
val parse_params = parse_raw_params >> map (apsnd implode_param)
val parse_fact_refs = Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse.thm)
val parse_fact_override_chunk =
  (Args.add |-- Args.colon |-- parse_fact_refs >> add_fact_override)
  || (Args.add |-- Args.colon |-- Scan.succeed [] >> add_fact_override)
  || (Args.del |-- Args.colon |-- parse_fact_refs >> del_fact_override)
  || (Args.del |-- Args.colon |-- Scan.succeed [] >> del_fact_override)
  || (parse_fact_refs >> only_fact_override)
val parse_fact_override =
  Scan.optional (Args.parens (Scan.repeat parse_fact_override_chunk >> merge_fact_overrides))
    no_fact_override

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sledgehammer\<close>
    "search for first-order proof using automatic theorem provers"
    (Scan.optional Parse.name runN -- parse_raw_params
      -- parse_fact_override -- Scan.option Parse.nat >>
      (fn (((subcommand, params), fact_override), opt_i) =>
        Toplevel.keep_proof
          (hammer_away params NONE subcommand opt_i fact_override o Toplevel.proof_of)))
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sledgehammer_params\<close>
    "set and display the default parameters for Sledgehammer"
    (parse_raw_params >> (fn params =>
      Toplevel.theory (fold set_default_raw_param params #> tap (fn thy =>
        writeln ("Default parameters for Sledgehammer:\n" ^
          (case rev (default_raw_params thy) of
            [] => "none"
          | params => params |> map string_of_raw_param |> sort_strings |> cat_lines))))))

val _ =
  Try.tool_setup
   {name = sledgehammerN, weight = 40, auto_option = \<^system_option>\<open>auto_sledgehammer\<close>,
    body = fn auto => fn state =>
      let
        val thy = Proof.theory_of state
        val mode = if auto then Auto_Try else Try
        val i = 1
      in
        run_sledgehammer (get_params mode thy []) mode NONE i no_fact_override (silence_state state)
        |> apsnd (map_prod short_string_of_sledgehammer_outcome single)
      end}

val _ =
  Query_Operation.register {name = sledgehammerN, pri = 0}
    (fn {state = st, args, writeln_result, ...} =>
      (case try Toplevel.proof_of st of
        SOME state =>
          let
            val [provers_arg, isar_proofs_arg, try0_arg] = args
            val override_params =
              ((if provers_arg = "" then [] else [("provers", space_explode " " provers_arg)]) @
                [("isar_proofs", [if isar_proofs_arg = "true" then "true" else "smart"]),
                 ("try0", [try0_arg]),
                 ("debug", ["false"]),
                 ("verbose", ["false"]),
                 ("overlord", ["false"])]);
          in hammer_away override_params (SOME writeln_result) runN NONE no_fact_override state end
      | NONE => error "Unknown proof context"))

end;
