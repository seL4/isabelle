(*  Title:      HOL/Tools/Nitpick/nitpick_commands.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Adds the "nitpick" and "nitpick_params" commands to Isabelle/Isar's outer
syntax.
*)

signature NITPICK_COMMANDS =
sig
  type params = Nitpick.params

  val nitpickN : string
  val nitpick_paramsN : string
  val default_params : theory -> (string * string) list -> params
end;

structure Nitpick_Commands : NITPICK_COMMANDS =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Rep
open Nitpick_Nut
open Nitpick

val nitpickN = "nitpick"
val nitpick_paramsN = "nitpick_params"

(* Maximum number of scopes for Auto Nitpick. Be frugal since it has to share
   its time slot with several other automatic tools. *)
val auto_try_max_scopes = 6

type raw_param = string * string list

val default_default_params =
  [("card", "1-10"),
   ("iter", "0,1,2,4,8,12,16,20,24,28"),
   ("bits", "1-10"),
   ("bisim_depth", "9"),
   ("box", "smart"),
   ("finitize", "smart"),
   ("mono", "smart"),
   ("wf", "smart"),
   ("sat_solver", "smart"),
   ("batch_size", "smart"),
   ("falsify", "true"),
   ("user_axioms", "smart"),
   ("assms", "true"),
   ("merge_type_vars", "false"),
   ("binary_ints", "smart"),
   ("destroy_constrs", "true"),
   ("specialize", "true"),
   ("star_linear_preds", "true"),
   ("total_consts", "smart"),
   ("peephole_optim", "true"),
   ("datatype_sym_break", "5"),
   ("kodkod_sym_break", "15"),
   ("timeout", "30"),
   ("tac_timeout", "0.5"),
   ("max_threads", "0"),
   ("debug", "false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("spy", "false"),
   ("show_types", "false"),
   ("show_skolems", "true"),
   ("show_consts", "false"),
   ("format", "1"),
   ("max_potential", "1"),
   ("max_genuine", "1")]

val negated_params =
  [("dont_box", "box"),
   ("dont_finitize", "finitize"),
   ("non_mono", "mono"),
   ("non_wf", "wf"),
   ("satisfy", "falsify"),
   ("no_user_axioms", "user_axioms"),
   ("no_assms", "assms"),
   ("dont_merge_type_vars", "merge_type_vars"),
   ("unary_ints", "binary_ints"),
   ("dont_destroy_constrs", "destroy_constrs"),
   ("dont_specialize", "specialize"),
   ("dont_star_linear_preds", "star_linear_preds"),
   ("partial_consts", "total_consts"),
   ("no_peephole_optim", "peephole_optim"),
   ("no_debug", "debug"),
   ("quiet", "verbose"),
   ("no_overlord", "overlord"),
   ("dont_spy", "spy"),
   ("hide_types", "show_types"),
   ("hide_skolems", "show_skolems"),
   ("hide_consts", "show_consts")]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) negated_params s orelse
  member (op =) ["max", "show_all", "whack", "eval", "need", "atoms",
                 "expect"] s orelse
  exists (fn p => String.isPrefix (p ^ " ") s)
         ["card", "max", "iter", "box", "dont_box", "finitize", "dont_finitize",
          "mono", "non_mono", "wf", "non_wf", "format", "atoms"]

fun check_raw_param (s, _) =
  if is_known_raw_param s then ()
  else error ("Unknown parameter: " ^ quote s)

fun unnegate_param_name name =
  case AList.lookup (op =) negated_params name of
    NONE => if String.isPrefix "dont_" name then SOME (unprefix "dont_" name)
            else if String.isPrefix "non_" name then SOME (unprefix "non_" name)
            else NONE
  | some_name => some_name

fun normalize_raw_param (name, value) =
  case unnegate_param_name name of
    SOME name' => [(name', case value of
                             ["false"] => ["true"]
                           | ["true"] => ["false"]
                           | [] => ["false"]
                           | _ => value)]
  | NONE => if name = "show_all" then
              [("show_types", value), ("show_skolems", value),
               ("show_consts", value)]
            else
              [(name, value)]

structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  val extend = I
  fun merge data = AList.merge (op =) (K true) data
)

val set_default_raw_param =
  Data.map o fold (AList.update (op =)) o normalize_raw_param
val default_raw_params = Data.get

fun is_punctuation s = (s = "," orelse s = "-")

fun stringify_raw_param_value [] = ""
  | stringify_raw_param_value [s] = s
  | stringify_raw_param_value (s1 :: s2 :: ss) =
    s1 ^ (if is_punctuation s1 orelse is_punctuation s2 then "" else " ") ^
    stringify_raw_param_value (s2 :: ss)

fun maxed_int_from_string min_int s = Int.max (min_int, the (Int.fromString s))

fun extract_params ctxt mode default_params override_params =
  let
    val override_params = maps normalize_raw_param override_params
    val raw_params = rev override_params @ rev default_params
    val raw_lookup = AList.lookup (op =) raw_params
    val lookup = Option.map stringify_raw_param_value o raw_lookup
    val lookup_string = the_default "" o lookup
    fun general_lookup_bool option default_value name =
      case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value
    val lookup_bool = the o general_lookup_bool false (SOME false)
    val lookup_bool_option = general_lookup_bool true NONE
    fun do_int name value =
      case value of
        SOME s => (case Int.fromString s of
                     SOME i => i
                   | NONE => error ("Parameter " ^ quote name ^
                                    " must be assigned an integer value"))
      | NONE => 0
    fun lookup_int name = do_int name (lookup name)
    fun lookup_int_option name =
      case lookup name of
        SOME "smart" => NONE
      | value => SOME (do_int name value)
    fun int_range_from_string name min_int s =
      let
        val (k1, k2) =
          (case space_explode "-" s of
             [s] => (s, s)
           | ["", s2] => ("-" ^ s2, "-" ^ s2)
           | [s1, s2] => (s1, s2)
           | _ => raise Option.Option)
          |> apply2 (maxed_int_from_string min_int)
      in if k1 <= k2 then k1 upto k2 else k1 downto k2 end
      handle Option.Option =>
             error ("Parameter " ^ quote name ^
                    " must be assigned a sequence of integers")
    fun int_seq_from_string name min_int s =
      maps (int_range_from_string name min_int) (space_explode "," s)
    fun lookup_int_seq name min_int =
      case lookup name of
        SOME s => (case int_seq_from_string name min_int s of
                     [] => [min_int]
                   | value => value)
      | NONE => [min_int]
    fun lookup_assigns read prefix default convert =
      (NONE, convert (the_default default (lookup prefix)))
      :: map (fn (name, value) =>
                 (SOME (read (String.extract (name, size prefix + 1, NONE))),
                  convert (stringify_raw_param_value value)))
             (filter (String.isPrefix (prefix ^ " ") o fst) raw_params)
    fun lookup_ints_assigns read prefix min_int =
      lookup_assigns read prefix (signed_string_of_int min_int)
                     (int_seq_from_string prefix min_int)
    fun lookup_bool_option_assigns read prefix =
      lookup_assigns read prefix "" (parse_bool_option true prefix)
    fun lookup_strings_assigns read prefix =
      lookup_assigns read prefix "" (space_explode " ")
    fun lookup_time name =
      case lookup name of
        SOME s => parse_time name s
      | NONE => Time.zeroTime
    val read_type_polymorphic =
      Syntax.read_typ ctxt #> Logic.mk_type
      #> singleton (Variable.polymorphic ctxt) #> Logic.dest_type
    val read_term_polymorphic =
      Syntax.read_term ctxt #> singleton (Variable.polymorphic ctxt)
    val lookup_term_list_option_polymorphic =
      AList.lookup (op =) raw_params #> Option.map (map read_term_polymorphic)
    val read_const_polymorphic = read_term_polymorphic #> dest_Const
    val cards_assigns =
      lookup_ints_assigns read_type_polymorphic "card" 1
      |> mode = Auto_Try ? map (apsnd (take auto_try_max_scopes))
    val maxes_assigns = lookup_ints_assigns read_const_polymorphic "max" ~1
    val iters_assigns = lookup_ints_assigns read_const_polymorphic "iter" 0
    val bitss = lookup_int_seq "bits" 1
    val bisim_depths = lookup_int_seq "bisim_depth" ~1
    val boxes = lookup_bool_option_assigns read_type_polymorphic "box"
    val finitizes = lookup_bool_option_assigns read_type_polymorphic "finitize"
    val monos = if mode = Auto_Try then [(NONE, SOME true)]
                else lookup_bool_option_assigns read_type_polymorphic "mono"
    val wfs = lookup_bool_option_assigns read_const_polymorphic "wf"
    val sat_solver = lookup_string "sat_solver"
    val falsify = lookup_bool "falsify"
    val debug = (mode <> Auto_Try andalso lookup_bool "debug")
    val verbose = debug orelse (mode <> Auto_Try andalso lookup_bool "verbose")
    val overlord = lookup_bool "overlord"
    val spy = getenv "NITPICK_SPY" = "yes" orelse lookup_bool "spy"
    val user_axioms = lookup_bool_option "user_axioms"
    val assms = lookup_bool "assms"
    val whacks = lookup_term_list_option_polymorphic "whack" |> these
    val merge_type_vars = lookup_bool "merge_type_vars"
    val binary_ints = lookup_bool_option "binary_ints"
    val destroy_constrs = lookup_bool "destroy_constrs"
    val specialize = lookup_bool "specialize"
    val star_linear_preds = lookup_bool "star_linear_preds"
    val total_consts = lookup_bool_option "total_consts"
    val needs = lookup_term_list_option_polymorphic "need"
    val peephole_optim = lookup_bool "peephole_optim"
    val datatype_sym_break = lookup_int "datatype_sym_break"
    val kodkod_sym_break = lookup_int "kodkod_sym_break"
    val timeout = lookup_time "timeout"
    val tac_timeout = lookup_time "tac_timeout"
    val max_threads =
      if mode = Normal then Int.max (0, lookup_int "max_threads") else 1
    val show_types = debug orelse lookup_bool "show_types"
    val show_skolems = debug orelse lookup_bool "show_skolems"
    val show_consts = debug orelse lookup_bool "show_consts"
    val evals = lookup_term_list_option_polymorphic "eval" |> these
    val formats = lookup_ints_assigns read_term_polymorphic "format" 0
    val atomss = lookup_strings_assigns read_type_polymorphic "atoms"
    val max_potential =
      if mode = Normal then Int.max (0, lookup_int "max_potential") else 0
    val max_genuine = Int.max (0, lookup_int "max_genuine")
    val batch_size =
      case lookup_int_option "batch_size" of
        SOME n => Int.max (1, n)
      | NONE => if debug then 1 else 50
    val expect = lookup_string "expect"
  in
    {cards_assigns = cards_assigns, maxes_assigns = maxes_assigns,
     iters_assigns = iters_assigns, bitss = bitss, bisim_depths = bisim_depths,
     boxes = boxes, finitizes = finitizes, monos = monos, wfs = wfs,
     sat_solver = sat_solver, falsify = falsify, debug = debug,
     verbose = verbose, overlord = overlord, spy = spy,
     user_axioms = user_axioms, assms = assms, whacks = whacks,
     merge_type_vars = merge_type_vars, binary_ints = binary_ints,
     destroy_constrs = destroy_constrs, specialize = specialize,
     star_linear_preds = star_linear_preds, total_consts = total_consts,
     needs = needs, peephole_optim = peephole_optim,
     datatype_sym_break = datatype_sym_break,
     kodkod_sym_break = kodkod_sym_break, timeout = timeout,
     tac_timeout = tac_timeout, max_threads = max_threads,
     show_types = show_types, show_skolems = show_skolems,
     show_consts = show_consts, evals = evals, formats = formats,
     atomss = atomss, max_potential = max_potential, max_genuine = max_genuine,
     batch_size = batch_size, expect = expect}
  end

fun default_params thy =
  extract_params (Proof_Context.init_global thy) Normal (default_raw_params thy)
  o map (apsnd single)

val parse_key = Scan.repeat1 Parse.embedded >> space_implode " "
val parse_value =
  Scan.repeats1 (Parse.minus >> single
                || Scan.repeat1 (Scan.unless Parse.minus
                                             (Parse.name || Parse.float_number))
                || \<^keyword>\<open>,\<close> |-- Parse.number >> prefix "," >> single)
val parse_param = parse_key -- Scan.optional (\<^keyword>\<open>=\<close> |-- parse_value) []
val parse_params =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.list parse_param --| \<^keyword>\<open>]\<close>) []

fun handle_exceptions ctxt f x =
  f x
  handle ARG (loc, details) =>
         error ("Bad argument(s) to " ^ quote loc ^ ": " ^ details)
       | BAD (loc, details) =>
         error ("Internal error (" ^ quote loc ^ "): " ^ details)
       | NOT_SUPPORTED details =>
         (warning ("Unsupported case: " ^ details); x)
       | NUT (loc, us) =>
         error ("Invalid intermediate term" ^ plural_s_for_list us ^
                " (" ^ quote loc ^ "): " ^
                commas (map (string_for_nut ctxt) us))
       | REP (loc, Rs) =>
         error ("Invalid representation" ^ plural_s_for_list Rs ^
                " (" ^ quote loc ^ "): " ^ commas (map string_for_rep Rs))
       | TERM (loc, ts) =>
         error ("Invalid term" ^ plural_s_for_list ts ^
                " (" ^ quote loc ^ "): " ^
                commas (map (Syntax.string_of_term ctxt) ts))
       | TYPE (loc, Ts, ts) =>
         error ("Invalid type" ^ plural_s_for_list Ts ^
                (if null ts then
                   ""
                 else
                   " for term" ^ plural_s_for_list ts ^ " " ^
                   commas (map (quote o Syntax.string_of_term ctxt) ts)) ^
                " (" ^ quote loc ^ "): " ^
                commas (map (Syntax.string_of_typ ctxt) Ts))

fun pick_nits override_params mode i step state =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val _ = List.app check_raw_param override_params
    val params as {debug, ...} =
      extract_params ctxt mode (default_raw_params thy) override_params
    fun go () =
      (unknownN, [])
      |> (if mode = Auto_Try then perhaps o try
          else if debug then fn f => fn x => f x
          else handle_exceptions ctxt)
         (fn _ => pick_nits_in_subgoal state params mode i step)
  in go () end
  |> `(fn (outcome_code, _) => outcome_code = genuineN)

fun string_for_raw_param (name, value) =
  name ^ " = " ^ stringify_raw_param_value value

fun nitpick_params_trans params =
  Toplevel.theory
      (fold set_default_raw_param params
       #> tap (fn thy =>
                  writeln ("Default parameters for Nitpick:\n" ^
                           (case rev (default_raw_params thy) of
                              [] => "none"
                            | params =>
                              (map check_raw_param params;
                               params |> map string_for_raw_param
                                      |> sort_strings |> cat_lines)))))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>nitpick\<close>
    "try to find a counterexample for a given subgoal using Nitpick"
    (parse_params -- Scan.optional Parse.nat 1 >> (fn (params, i) =>
      Toplevel.keep_proof (fn state =>
        ignore (pick_nits params Normal i (Toplevel.proof_position_of state)
          (Toplevel.proof_of state)))))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>nitpick_params\<close>
    "set and display the default parameters for Nitpick"
    (parse_params #>> nitpick_params_trans)

val _ =
  Try.tool_setup
   {name = nitpickN, weight = 50, auto_option = \<^system_option>\<open>auto_nitpick\<close>,
    body = fn auto => pick_nits [] (if auto then Auto_Try else Try) 1 0}

end;
