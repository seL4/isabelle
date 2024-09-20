(*  Title:      HOL/Tools/Nunchaku/nunchaku_commands.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

Adds the "nunchaku" and "nunchaku_params" commands to Isabelle/Isar's outer syntax.
*)

signature NUNCHAKU_COMMANDS =
sig
  type params = Nunchaku.params

  val default_params: theory -> (string * string) list -> params
end;

structure Nunchaku_Commands : NUNCHAKU_COMMANDS =
struct

open Nunchaku_Util;
open Nunchaku;

type raw_param = string * string list;

val default_default_params =
  [("assms", "true"),
   ("bound_increment", "4"),
   ("debug", "false"),
   ("falsify", "true"),
   ("min_bound", "4"),
   ("max_bound", "none"),
   ("max_genuine", "1"),
   ("max_potential", "1"),
   ("overlord", "false"),
   ("solvers", "cvc4 kodkod paradox smbc"),
   ("specialize", "true"),
   ("spy", "false"),
   ("timeout", "30"),
   ("verbose", "false"),
   ("wf_timeout", "0.5")];

val alias_params =
  [("solver", "solvers")];

val negated_alias_params =
  [("dont_whack", "whack"),
   ("dont_specialize", "specialize"),
   ("dont_spy", "spy"),
   ("no_assms", "assms"),
   ("no_debug", "debug"),
   ("no_overlord", "overlord"),
   ("non_mono", "mono"),
   ("non_wf", "wf"),
   ("quiet", "verbose"),
   ("satisfy", "falsify")];

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) ["atoms", "card", "eval", "expect"] s orelse
  exists (fn p => String.isPrefix (p ^ " ") s)
    ["atoms", "card", "dont_whack", "mono", "non_mono", "non_wf", "wf", "whack"];

fun check_raw_param (s, _) =
  if is_known_raw_param s then () else error ("Unknown parameter: " ^ quote s);

fun unnegate_param_name name =
  (case AList.lookup (op =) negated_alias_params name of
    NONE =>
    if String.isPrefix "dont_" name then SOME (unprefix "dont_" name)
    else if String.isPrefix "non_" name then SOME (unprefix "non_" name)
    else NONE
  | some_name => some_name);

fun normalize_raw_param (name, value) =
  (case AList.lookup (op =) alias_params name of
    SOME alias => [(alias, value)]
  | NONE =>
    (case unnegate_param_name name of
      SOME name' =>
      [(name',
        (case value of
          ["false"] => ["true"]
        | ["true"] => ["false"]
        | [] => ["false"]
        | _ => value))]
    | NONE => [(name, value)]));

structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  fun merge data = AList.merge (op =) (K true) data
);

val set_default_raw_param = Data.map o fold (AList.update (op =)) o normalize_raw_param;
val default_raw_params = Data.get;

fun is_punctuation s = (s = "," orelse s = "-");

fun stringify_raw_param_value [] = ""
  | stringify_raw_param_value [s] = s
  | stringify_raw_param_value (s1 :: s2 :: ss) =
    s1 ^ (if is_punctuation s1 orelse is_punctuation s2 then "" else " ") ^
    stringify_raw_param_value (s2 :: ss);

fun extract_params ctxt mode default_params override_params =
  let
    val override_params = maps normalize_raw_param override_params;
    val raw_params = rev override_params @ rev default_params;
    val raw_lookup = AList.lookup (op =) raw_params;
    val lookup = Option.map stringify_raw_param_value o raw_lookup;
    val lookup_string = the_default "" o lookup;
    val lookup_strings = these o Option.map (space_explode " ") o lookup;

    fun general_lookup_bool option default_value name =
      (case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value);

    val lookup_bool = the o general_lookup_bool false (SOME false);

    fun lookup_int name =
      (case lookup name of
        SOME s =>
        (case Int.fromString s of
          SOME i => i
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned an integer value"))
      | NONE => 0);

    fun int_range_from_string name s =
      (case space_explode "-" s of
         [s] => (s, s)
       | [s1, s2] => (s1, s2)
       | _ => error ("Parameter " ^ quote name ^ " must be assigned a range of integers"))
      |> apply2 Int.fromString;

    fun lookup_assigns read pre of_str =
      (case lookup pre of
        SOME s => [(NONE, of_str s)]
      | NONE => []) @
      map (fn (name, value) => (SOME (read (String.extract (name, size pre + 1, NONE))),
          of_str (stringify_raw_param_value value)))
        (filter (String.isPrefix (pre ^ " ") o fst) raw_params);

    fun lookup_int_range_assigns read pre =
      lookup_assigns read pre (int_range_from_string pre);

    fun lookup_bool_assigns read pre =
      lookup_assigns read pre (the o parse_bool_option false pre);

    fun lookup_bool_option_assigns read pre =
      lookup_assigns read pre (parse_bool_option true pre);

    fun lookup_strings_assigns read pre =
      lookup_assigns read pre (space_explode " ");

    fun lookup_time name =
      (case lookup name of
        SOME s => parse_time name s
      | NONE => Time.zeroTime);

    val read_type_polymorphic =
      Syntax.read_typ ctxt #> Logic.mk_type
      #> singleton (Variable.polymorphic ctxt) #> Logic.dest_type;
    val read_term_polymorphic =
      Syntax.read_term ctxt #> singleton (Variable.polymorphic ctxt);

    val lookup_term_list_option_polymorphic =
      AList.lookup (op =) raw_params #> Option.map (map read_term_polymorphic);

    fun read_const_polymorphic s =
      (case read_term_polymorphic s of
        Const x => x
      | t => error ("Not a constant: " ^ Syntax.string_of_term ctxt t));

    fun lookup_none_option lookup' name =
      (case lookup name of
        SOME "none" => NONE
      | _ => SOME (lookup' name))

    val solvers = lookup_strings "solvers";
    val falsify = lookup_bool "falsify";
    val assms = lookup_bool "assms";
    val spy = getenv "NUNCHAKU_SPY" = "yes" orelse lookup_bool "spy";
    val overlord = lookup_bool "overlord";
    val expect = lookup_string "expect";

    val wfs = lookup_bool_option_assigns read_const_polymorphic "wf";
    val min_bound = lookup_int "min_bound";
    val max_bound = lookup_none_option lookup_int "max_bound";
    val bound_increment = lookup_int "bound_increment";
    val whacks = lookup_bool_assigns read_term_polymorphic "whack";
    val cards = lookup_int_range_assigns read_type_polymorphic "card";
    val monos = lookup_bool_option_assigns read_type_polymorphic "mono";

    val debug = (mode <> Auto_Try andalso lookup_bool "debug");
    val verbose = debug orelse (mode <> Auto_Try andalso lookup_bool "verbose");
    val max_potential = if mode = Normal then Int.max (0, lookup_int "max_potential") else 0;
    val max_genuine = Int.max (0, lookup_int "max_genuine");
    val evals = these (lookup_term_list_option_polymorphic "eval");
    val atomss = lookup_strings_assigns read_type_polymorphic "atoms";

    val specialize = lookup_bool "specialize";
    val multithread = mode = Normal andalso lookup_bool "multithread";

    val timeout = lookup_time "timeout";
    val wf_timeout = lookup_time "wf_timeout";

    val mode_of_operation_params =
      {solvers = solvers, falsify = falsify, assms = assms, spy = spy, overlord = overlord,
       expect = expect};

    val scope_of_search_params =
      {wfs = wfs, whacks = whacks, min_bound = min_bound, max_bound = max_bound,
       bound_increment = bound_increment, cards = cards, monos = monos};

    val output_format_params =
      {verbose = verbose, debug = debug, max_potential = max_potential, max_genuine = max_genuine,
       evals = evals, atomss = atomss};

    val optimization_params =
      {specialize = specialize, multithread = multithread};

    val timeout_params =
      {timeout = timeout, wf_timeout = wf_timeout};
  in
    {mode_of_operation_params = mode_of_operation_params,
     scope_of_search_params = scope_of_search_params,
     output_format_params = output_format_params,
     optimization_params = optimization_params,
     timeout_params = timeout_params}
  end;

fun default_params thy =
  extract_params (Proof_Context.init_global thy) Normal (default_raw_params thy)
  o map (apsnd single);

val parse_key = Scan.repeat1 Parse.embedded >> implode_space;
val parse_value =
  Scan.repeat1 (Parse.minus >> single
    || Scan.repeat1 (Scan.unless Parse.minus (Parse.name || Parse.float_number))
    || \<^keyword>\<open>,\<close> |-- Parse.number >> prefix "," >> single)
  >> flat;
val parse_param = parse_key -- Scan.optional (\<^keyword>\<open>=\<close> |-- parse_value) [];
val parse_params = Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.list parse_param --| \<^keyword>\<open>]\<close>) [];

fun run_chaku override_params mode i state0 =
  let
    val state = Proof.map_contexts (Try0.silence_methods false) state0;
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;
    val _ = List.app check_raw_param override_params;
    val params = extract_params ctxt mode (default_raw_params thy) override_params;
  in
    (if mode = Auto_Try then perhaps o try else fn f => fn x => f x)
      (fn _ => run_chaku_on_subgoal state params mode i) (unknownN, NONE)
    |> `(fn (outcome_code, _) => outcome_code = genuineN)
  end;

fun string_for_raw_param (name, value) =
  name ^ " = " ^ stringify_raw_param_value value;

fun nunchaku_params_trans params =
  Toplevel.theory (fold set_default_raw_param params
    #> tap (fn thy =>
      let val params = rev (default_raw_params thy) in
        List.app check_raw_param params;
        writeln ("Default parameters for Nunchaku:\n" ^
          (params |> map string_for_raw_param |> sort_strings |> cat_lines))
      end));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>nunchaku\<close>
    "try to find a countermodel using Nunchaku"
    (parse_params -- Scan.optional Parse.nat 1 >> (fn (params, i) =>
       Toplevel.keep_proof (fn state =>
         ignore (run_chaku params Normal i (Toplevel.proof_of state)))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>nunchaku_params\<close>
    "set and display the default parameters for Nunchaku"
    (parse_params #>> nunchaku_params_trans);

end;
