(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
*)

signature SLEDGEHAMMER_ISAR =
sig
  type params = Sledgehammer_Provers.params

  val auto : bool Unsynchronized.ref
  val provers : string Unsynchronized.ref
  val timeout : int Unsynchronized.ref
  val default_params : Proof.context -> (string * string) list -> params
  val setup : theory -> theory
end;

structure Sledgehammer_Isar : SLEDGEHAMMER_ISAR =
struct

open ATP_Util
open ATP_Systems
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_Provers
open Sledgehammer_Minimize
open Sledgehammer_Run

val runN = "run"
val minN = "min"
val messagesN = "messages"
val supported_proversN = "supported_provers"
val running_proversN = "running_provers"
val kill_proversN = "kill_provers"
val refresh_tptpN = "refresh_tptp"

val auto = Unsynchronized.ref false

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
      (Preferences.bool_pref auto "auto-sledgehammer"
           "Run Sledgehammer automatically.")

(** Sledgehammer commands **)

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

type raw_param = string * string list

val default_default_params =
  [("debug", "false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("blocking", "false"),
   ("type_enc", "smart"),
   ("strict", "false"),
   ("lam_trans", "smart"),
   ("uncurried_aliases", "smart"),
   ("relevance_thresholds", "0.45 0.85"),
   ("max_relevant", "smart"),
   ("max_mono_iters", "3"),
   ("max_new_mono_instances", "200"),
   ("isar_proof", "false"),
   ("isar_shrink_factor", "1"),
   ("slice", "true"),
   ("minimize", "smart"),
   ("preplay_timeout", "3")]

val alias_params =
  [("prover", ("provers", [])),
   ("dont_preplay", ("preplay_timeout", ["0"]))]
val negated_alias_params =
  [("no_debug", "debug"),
   ("quiet", "verbose"),
   ("no_overlord", "overlord"),
   ("non_blocking", "blocking"),
   ("non_strict", "strict"),
   ("no_uncurried_aliases", "uncurried_aliases"),
   ("no_isar_proof", "isar_proof"),
   ("dont_slice", "slice"),
   ("dont_minimize", "minimize")]

val params_for_minimize =
  ["debug", "verbose", "overlord", "type_enc", "strict", "lam_trans",
   "uncurried_aliases", "max_mono_iters", "max_new_mono_instances",
   "isar_proof", "isar_shrink_factor", "timeout", "preplay_timeout"]

val property_dependent_params = ["provers", "timeout"]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) property_dependent_params s orelse s = "expect"

fun is_prover_list ctxt s =
  case space_explode " " s of
    ss as _ :: _ => forall (is_prover_supported ctxt) ss
  | _ => false

fun unalias_raw_param (name, value) =
  case AList.lookup (op =) alias_params name of
    SOME (name', []) => (name', value)
  | SOME (param' as (name', _)) =>
    if value <> ["false"] then
      param'
    else
      error ("Parameter " ^ quote name ^ " cannot be set to \"false\" \
             \(cf. " ^ quote name' ^ ").")
  | NONE =>
    case AList.lookup (op =) negated_alias_params name of
      SOME name' => (name', case value of
                              ["false"] => ["true"]
                            | ["true"] => ["false"]
                            | [] => ["false"]
                            | _ => value)
    | NONE => (name, value)

val any_type_enc = type_enc_from_string Strict "erased"

(* "provers =", "type_enc =", and "lam_trans" can be omitted. For the last two,
   this is a secret feature. *)
fun normalize_raw_param ctxt =
  unalias_raw_param
  #> (fn (name, value) =>
         if is_known_raw_param name then
           (name, value)
         else if is_prover_list ctxt name andalso null value then
           ("provers", [name])
         else if can (type_enc_from_string Strict) name andalso null value then
           ("type_enc", [name])
         else if can (trans_lams_from_string ctxt any_type_enc) name andalso
                 null value then
           ("lam_trans", [name])
         else
           error ("Unknown parameter: " ^ quote name ^ "."))


(* Ensures that type encodings such as "mono_native?" and "poly_guards!!" are
   read correctly. *)
val implode_param = strip_spaces_except_between_idents o space_implode " "

structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  val extend = I
  fun merge data : T = AList.merge (op =) (K true) data
)

fun remotify_prover_if_supported_and_not_already_remote ctxt name =
  if String.isPrefix remote_prefix name then
    SOME name
  else
    let val remote_name = remote_prefix ^ name in
      if is_prover_supported ctxt remote_name then SOME remote_name else NONE
    end

fun remotify_prover_if_not_installed ctxt name =
  if is_prover_supported ctxt name andalso is_prover_installed ctxt name then
    SOME name
  else
    remotify_prover_if_supported_and_not_already_remote ctxt name

fun avoid_too_many_threads _ _ [] = []
  | avoid_too_many_threads _ (0, 0) _ = []
  | avoid_too_many_threads ctxt (0, max_remote) provers =
    provers
    |> map_filter (remotify_prover_if_supported_and_not_already_remote ctxt)
    |> take max_remote
  | avoid_too_many_threads _ (max_local, 0) provers =
    provers
    |> filter_out (String.isPrefix remote_prefix)
    |> take max_local
  | avoid_too_many_threads ctxt max_local_and_remote (prover :: provers) =
    let
      val max_local_and_remote =
        max_local_and_remote
        |> (if String.isPrefix remote_prefix prover then apsnd else apfst)
              (Integer.add ~1)
    in prover :: avoid_too_many_threads ctxt max_local_and_remote provers end

val max_default_remote_threads = 4

(* The first ATP of the list is used by Auto Sledgehammer. Because of the low
   timeout, it makes sense to put SPASS first. *)
fun default_provers_param_value ctxt =
  [spassN, eN, vampireN, SMT_Solver.solver_name_of ctxt, e_sineN, waldmeisterN]
  |> map_filter (remotify_prover_if_not_installed ctxt)
  |> avoid_too_many_threads ctxt (Multithreading.max_threads_value (),
                                  max_default_remote_threads)
  |> implode_param

fun set_default_raw_param param thy =
  let val ctxt = Proof_Context.init_global thy in
    thy |> Data.map (AList.update (op =) (normalize_raw_param ctxt param))
  end
fun default_raw_params ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    Data.get thy
    |> fold (AList.default (op =))
            [("provers", [case !provers of
                            "" => default_provers_param_value ctxt
                          | s => s]),
             ("timeout", let val timeout = !timeout in
                           [if timeout <= 0 then "none"
                            else string_of_int timeout]
                         end)]
  end

val infinity_time_in_secs = 60 * 60 * 24 * 365
val the_timeout = the_default (Time.fromSeconds infinity_time_in_secs)

fun extract_params mode default_params override_params =
  let
    val raw_params = rev override_params @ rev default_params
    val lookup = Option.map implode_param o AList.lookup (op =) raw_params
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
    fun lookup_option lookup' name =
      case lookup name of
        SOME "smart" => NONE
      | _ => SOME (lookup' name)
    val debug = mode <> Auto_Try andalso lookup_bool "debug"
    val verbose = debug orelse (mode <> Auto_Try andalso lookup_bool "verbose")
    val overlord = lookup_bool "overlord"
    val blocking =
      Isabelle_Process.is_active () orelse mode <> Normal orelse debug orelse
      lookup_bool "blocking"
    val provers = lookup_string "provers" |> space_explode " "
                  |> mode = Auto_Try ? single o hd
    val type_enc =
      if mode = Auto_Try then
        NONE
      else case lookup_string "type_enc" of
        "smart" => NONE
      | s => (type_enc_from_string Strict s; SOME s)
    val strict = mode = Auto_Try orelse lookup_bool "strict"
    val lam_trans = lookup_option lookup_string "lam_trans"
    val uncurried_aliases = lookup_option lookup_bool "uncurried_aliases"
    val relevance_thresholds = lookup_real_pair "relevance_thresholds"
    val max_relevant = lookup_option lookup_int "max_relevant"
    val max_mono_iters = lookup_int "max_mono_iters"
    val max_new_mono_instances = lookup_int "max_new_mono_instances"
    val isar_proof = lookup_bool "isar_proof"
    val isar_shrink_factor = Int.max (1, lookup_int "isar_shrink_factor")
    val slice = mode <> Auto_Try andalso lookup_bool "slice"
    val minimize =
      if mode = Auto_Try then NONE else lookup_option lookup_bool "minimize"
    val timeout =
      (if mode = Auto_Try then NONE else lookup_time "timeout") |> the_timeout
    val preplay_timeout =
      if mode = Auto_Try then Time.zeroTime
      else lookup_time "preplay_timeout" |> the_timeout
    val expect = lookup_string "expect"
  in
    {debug = debug, verbose = verbose, overlord = overlord, blocking = blocking,
     provers = provers, type_enc = type_enc, strict = strict,
     lam_trans = lam_trans, uncurried_aliases = uncurried_aliases,
     relevance_thresholds = relevance_thresholds, max_relevant = max_relevant,
     max_mono_iters = max_mono_iters,
     max_new_mono_instances = max_new_mono_instances,  isar_proof = isar_proof,
     isar_shrink_factor = isar_shrink_factor, slice = slice,
     minimize = minimize, timeout = timeout, preplay_timeout = preplay_timeout,
     expect = expect}
  end

fun get_params mode = extract_params mode o default_raw_params
fun default_params thy = get_params Normal thy o map (apsnd single)

(* Sledgehammer the given subgoal *)

val default_minimize_prover = metisN

fun is_raw_param_relevant_for_minimize (name, _) =
  member (op =) params_for_minimize name
fun string_for_raw_param (key, values) =
  key ^ (case implode_param values of "" => "" | value => " = " ^ value)

fun minimize_command override_params i more_override_params prover_name
                     fact_names =
  let
    val params =
      (override_params
       |> filter_out (AList.defined (op =) more_override_params o fst)) @
      more_override_params
      |> filter is_raw_param_relevant_for_minimize
      |> map string_for_raw_param
      |> (if prover_name = default_minimize_prover then I else cons prover_name)
      |> space_implode ", "
  in
    "sledgehammer" ^ " " ^ minN ^
    (if params = "" then "" else enclose " [" "]" params) ^
    " (" ^ space_implode " " fact_names ^ ")" ^
    (if i = 1 then "" else " " ^ string_of_int i)
  end

fun hammer_away override_params subcommand opt_i relevance_override state =
  let
    val ctxt = Proof.context_of state
    val override_params = override_params |> map (normalize_raw_param ctxt)
  in
    if subcommand = runN then
      let val i = the_default 1 opt_i in
        run_sledgehammer (get_params Normal ctxt override_params) Normal i
                         relevance_override (minimize_command override_params i)
                         state
        |> K ()
      end
    else if subcommand = minN then
      run_minimize (get_params Minimize ctxt
                               (("provers", [default_minimize_prover]) ::
                                override_params))
                   (the_default 1 opt_i) (#add relevance_override) state
    else if subcommand = messagesN then
      messages opt_i
    else if subcommand = supported_proversN then
      supported_provers ctxt
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

fun string_for_raw_param (name, value) = name ^ " = " ^ implode_param value

fun sledgehammer_params_trans params =
  Toplevel.theory
      (fold set_default_raw_param params
       #> tap (fn thy =>
                  let val ctxt = Proof_Context.init_global thy in
                    writeln ("Default parameters for Sledgehammer:\n" ^
                             (case default_raw_params ctxt |> rev of
                                [] => "none"
                              | params =>
                                params |> map string_for_raw_param
                                       |> sort_strings |> cat_lines))
                  end))

val parse_query_bang = @{keyword "?"} || @{keyword "!"} || @{keyword "!!"}
val parse_key =
  Scan.repeat1 (Parse.typ_group || parse_query_bang) >> implode_param
val parse_value =
  Scan.repeat1 (Parse.xname || Parse.float_number || parse_query_bang)
val parse_param = parse_key -- Scan.optional (@{keyword "="} |-- parse_value) []
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

val _ =
  Outer_Syntax.improper_command @{command_spec "sledgehammer"}
    "search for first-order proof using automatic theorem provers"
    ((Scan.optional Parse.short_ident runN -- parse_params
      -- parse_relevance_override -- Scan.option Parse.nat) #>> sledgehammer_trans)
val _ =
  Outer_Syntax.command @{command_spec "sledgehammer_params"}
    "set and display the default parameters for Sledgehammer"
    (parse_params #>> sledgehammer_params_trans)

fun try_sledgehammer auto state =
  let
    val ctxt = Proof.context_of state
    val mode = if auto then Auto_Try else Try
    val i = 1
  in
    run_sledgehammer (get_params mode ctxt []) mode i no_relevance_override
                     (minimize_command [] i) state
  end

val setup = Try.register_tool ("sledgehammer", (40, auto, try_sledgehammer))

end;
