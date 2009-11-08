(*  Title:      HOL/Nitpick/Tools/nitpick_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Adds the "nitpick" and "nitpick_params" commands to Isabelle/Isar's outer
syntax.
*)

signature NITPICK_ISAR =
sig
  type params = Nitpick.params

  val default_params : theory -> (string * string) list -> params
end

structure Nitpick_Isar : NITPICK_ISAR =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Rep
open Nitpick_Nut
open Nitpick

type raw_param = string * string list

val default_default_params =
  [("card", ["1\<midarrow>8"]),
   ("iter", ["0,1,2,4,8,12,16,24"]),
   ("bisim_depth", ["7"]),
   ("box", ["smart"]),
   ("mono", ["smart"]),
   ("wf", ["smart"]),
   ("sat_solver", ["smart"]),
   ("batch_size", ["smart"]),
   ("auto", ["false"]),
   ("blocking", ["true"]),
   ("falsify", ["true"]),
   ("user_axioms", ["smart"]),
   ("assms", ["true"]),
   ("coalesce_type_vars", ["false"]),
   ("destroy_constrs", ["true"]),
   ("specialize", ["true"]),
   ("skolemize", ["true"]),
   ("star_linear_preds", ["true"]),
   ("uncurry", ["true"]),
   ("fast_descrs", ["true"]),
   ("peephole_optim", ["true"]),
   ("timeout", ["30 s"]),
   ("auto_timeout", ["5 s"]),
   ("tac_timeout", ["500 ms"]),
   ("sym_break", ["20"]),
   ("sharing_depth", ["3"]),
   ("flatten_props", ["false"]),
   ("max_threads", ["0"]),
   ("verbose", ["false"]),
   ("debug", ["false"]),
   ("overlord", ["false"]),
   ("show_all", ["false"]),
   ("show_skolems", ["true"]),
   ("show_datatypes", ["false"]),
   ("show_consts", ["false"]),
   ("format", ["1"]),
   ("max_potential", ["1"]),
   ("max_genuine", ["1"]),
   ("check_potential", ["false"]),
   ("check_genuine", ["false"])]

val negated_params =
  [("dont_box", "box"),
   ("non_mono", "mono"),
   ("non_wf", "wf"),
   ("no_auto", "auto"),
   ("non_blocking", "blocking"),
   ("satisfy", "falsify"),
   ("no_user_axioms", "user_axioms"),
   ("no_assms", "assms"),
   ("dont_coalesce_type_vars", "coalesce_type_vars"),
   ("dont_destroy_constrs", "destroy_constrs"),
   ("dont_specialize", "specialize"),
   ("dont_skolemize", "skolemize"),
   ("dont_star_linear_preds", "star_linear_preds"),
   ("dont_uncurry", "uncurry"),
   ("full_descrs", "fast_descrs"),
   ("no_peephole_optim", "peephole_optim"),
   ("dont_flatten_props", "flatten_props"),
   ("quiet", "verbose"),
   ("no_debug", "debug"),
   ("no_overlord", "overlord"),
   ("dont_show_all", "show_all"),
   ("hide_skolems", "show_skolems"),
   ("hide_datatypes", "show_datatypes"),
   ("hide_consts", "show_consts"),
   ("trust_potential", "check_potential"),
   ("trust_genuine", "check_genuine")]

(* string -> bool *)
fun is_known_raw_param s =
  AList.defined (op =) default_default_params s
  orelse AList.defined (op =) negated_params s
  orelse s mem ["max", "eval", "expect"]
  orelse exists (fn p => String.isPrefix (p ^ " ") s)
                ["card", "max", "iter", "box", "dont_box", "mono", "non_mono",
                 "wf", "non_wf", "format"]

(* string * 'a -> unit *)
fun check_raw_param (s, _) =
  if is_known_raw_param s then ()
  else error ("Unknown parameter " ^ quote s ^ ".")  

(* string -> string option *)
fun unnegate_param_name name =
  case AList.lookup (op =) negated_params name of
    NONE => if String.isPrefix "dont_" name then SOME (unprefix "dont_" name)
            else if String.isPrefix "non_" name then SOME (unprefix "non_" name)
            else NONE
  | some_name => some_name
(* raw_param -> raw_param *)
fun unnegate_raw_param (name, value) =
  case unnegate_param_name name of
    SOME name' => (name', case value of
                            ["false"] => ["true"]
                          | ["true"] => ["false"]
                          | [] => ["false"]
                          | _ => value)
  | NONE => (name, value)

structure TheoryData = Theory_Data(
  type T = {params: raw_param list, registered_auto: bool}
  val empty = {params = rev default_default_params, registered_auto = false}
  val extend = I
  fun merge ({params = ps1, registered_auto = a1},
               {params = ps2, registered_auto = a2}) : T =
    {params = AList.merge (op =) (op =) (ps1, ps2),
     registered_auto = a1 orelse a2})

(* raw_param -> theory -> theory *)
fun set_default_raw_param param thy =
  let val {params, registered_auto} = TheoryData.get thy in
    TheoryData.put
      {params = AList.update (op =) (unnegate_raw_param param) params,
       registered_auto = registered_auto} thy
  end
(* theory -> raw_param list *)
val default_raw_params = #params o TheoryData.get

(* theory -> theory *)
fun set_registered_auto thy =
  TheoryData.put {params = default_raw_params thy, registered_auto = true} thy
(* theory -> bool *)
val is_registered_auto = #registered_auto o TheoryData.get

(* string -> bool *)
fun is_punctuation s = (s = "," orelse s = "-" orelse s = "\<midarrow>")

(* string list -> string *)
fun stringify_raw_param_value [] = ""
  | stringify_raw_param_value [s] = s
  | stringify_raw_param_value (s1 :: s2 :: ss) =
    s1 ^ (if is_punctuation s1 orelse is_punctuation s2 then "" else " ") ^
    stringify_raw_param_value (s2 :: ss)

(* bool -> string -> string -> bool option *)
fun bool_option_from_string option name s =
  (case s of
     "smart" => if option then NONE else raise Option
   | "false" => SOME false
   | "true" => SOME true
   | "" => SOME true
   | s => raise Option)
  handle Option.Option =>
         let val ss = map quote ((option ? cons "smart") ["true", "false"]) in
           error ("Parameter " ^ quote name ^ " must be assigned " ^
                  space_implode " " (serial_commas "or" ss) ^ ".")
         end
(* bool -> raw_param list -> bool option -> string -> bool option *)
fun general_lookup_bool option raw_params default_value name =
  case AList.lookup (op =) raw_params name of
    SOME s => s |> stringify_raw_param_value
                |> bool_option_from_string option name
  | NONE => default_value

(* int -> string -> int *)
fun maxed_int_from_string min_int s = Int.max (min_int, the (Int.fromString s))

(* Proof.context -> bool -> raw_param list -> raw_param list -> params *)
fun extract_params ctxt auto default_params override_params =
  let
    val override_params = map unnegate_raw_param override_params
    val raw_params = rev override_params @ rev default_params
    val lookup =
      Option.map stringify_raw_param_value o AList.lookup (op =) raw_params
    (* string -> string *)
    fun lookup_string name = the_default "" (lookup name)
    (* string -> bool *)
    val lookup_bool = the o general_lookup_bool false raw_params (SOME false)
    (* string -> bool option *)
    val lookup_bool_option = general_lookup_bool true raw_params NONE
    (* string -> string option -> int *)
    fun do_int name value =
      case value of
        SOME s => (case Int.fromString s of
                     SOME i => i
                   | NONE => error ("Parameter " ^ quote name ^
                                    " must be assigned an integer value."))
      | NONE => 0
    (* string -> int *)
    fun lookup_int name = do_int name (lookup name)
    (* string -> int option *)
    fun lookup_int_option name =
      case lookup name of
        SOME "smart" => NONE
      | value => SOME (do_int name value)
    (* string -> int -> string -> int list *)
    fun int_range_from_string name min_int s =
      let
        val (k1, k2) =
          (case space_explode "-" s of
             [s] => the_default (s, s) (first_field "\<midarrow>" s)
           | ["", s2] => ("-" ^ s2, "-" ^ s2)
           | [s1, s2] => (s1, s2)
           | _ => raise Option)
          |> pairself (maxed_int_from_string min_int)
      in if k1 <= k2 then k1 upto k2 else k1 downto k2 end
      handle Option.Option =>
             error ("Parameter " ^ quote name ^
                    " must be assigned a sequence of integers.")
    (* string -> int -> string -> int list *)
    fun int_seq_from_string name min_int s =
      maps (int_range_from_string name min_int) (space_explode "," s)
    (* string -> int -> int list *)
    fun lookup_int_seq name min_int =
      case lookup name of
        SOME s => (case int_seq_from_string name min_int s of
                     [] => [min_int]
                   | value => value)
      | NONE => [min_int]
    (* (string -> 'a) -> int -> string -> ('a option * int list) list *)
    fun lookup_ints_assigns read prefix min_int =
      (NONE, lookup_int_seq prefix min_int)
      :: map (fn (name, value) =>
                 (SOME (read (String.extract (name, size prefix + 1, NONE))),
                  value |> stringify_raw_param_value
                        |> int_seq_from_string name min_int))
             (filter (String.isPrefix (prefix ^ " ") o fst) raw_params)
    (* (string -> 'a) -> string -> ('a option * bool option) list *)
    fun lookup_bool_option_assigns read prefix =
      (NONE, lookup_bool_option prefix)
      :: map (fn (name, value) =>
                 (SOME (read (String.extract (name, size prefix + 1, NONE))),
                  value |> stringify_raw_param_value
                        |> bool_option_from_string true name))
             (filter (String.isPrefix (prefix ^ " ") o fst) raw_params)
    (* string -> Time.time option *)
    fun lookup_time name =
      case lookup name of
        NONE => NONE
      | SOME "none" => NONE
      | SOME s =>
        let
          val msecs =
            case space_explode " " s of
              [s1, "min"] => 60000 * the (Int.fromString s1)
            | [s1, "s"] => 1000 * the (Int.fromString s1)
            | [s1, "ms"] => the (Int.fromString s1)
            | _ => 0
        in
          if msecs <= 0 then
            error ("Parameter " ^ quote name ^ " must be assigned a positive \
                   \time value (e.g., \"60 s\", \"200 ms\") or \"none\".")
          else
            SOME (Time.fromMilliseconds msecs)
        end
    (* string -> term list *)
    val lookup_term_list =
      AList.lookup (op =) raw_params #> these #> Syntax.read_terms ctxt
    val read_type_polymorphic =
      Syntax.read_typ ctxt #> Logic.mk_type
      #> singleton (Variable.polymorphic ctxt) #> Logic.dest_type
    (* string -> term *)
    val read_term_polymorphic =
      Syntax.read_term ctxt #> singleton (Variable.polymorphic ctxt)
    (* string -> styp *)
    val read_const_polymorphic = read_term_polymorphic #> dest_Const
    val cards_assigns = lookup_ints_assigns read_type_polymorphic "card" 1
    val maxes_assigns = lookup_ints_assigns read_const_polymorphic "max" ~1
    val iters_assigns = lookup_ints_assigns read_const_polymorphic "iter" 0
    val bisim_depths = lookup_int_seq "bisim_depth" ~1
    val boxes =
      lookup_bool_option_assigns read_type_polymorphic "box" @
      map_filter (fn (SOME T, _) =>
                     if is_fun_type T orelse is_pair_type T then
                       SOME (SOME T, SOME true)
                     else
                       NONE
                   | (NONE, _) => NONE) cards_assigns
    val monos = lookup_bool_option_assigns read_type_polymorphic "mono"
    val wfs = lookup_bool_option_assigns read_const_polymorphic "wf"
    val sat_solver = lookup_string "sat_solver"
    val blocking = not auto andalso lookup_bool "blocking"
    val falsify = lookup_bool "falsify"
    val debug = not auto andalso lookup_bool "debug"
    val verbose = debug orelse (not auto andalso lookup_bool "verbose")
    val overlord = lookup_bool "overlord"
    val user_axioms = lookup_bool_option "user_axioms"
    val assms = lookup_bool "assms"
    val coalesce_type_vars = lookup_bool "coalesce_type_vars"
    val destroy_constrs = lookup_bool "destroy_constrs"
    val specialize = lookup_bool "specialize"
    val skolemize = lookup_bool "skolemize"
    val star_linear_preds = lookup_bool "star_linear_preds"
    val uncurry = lookup_bool "uncurry"
    val fast_descrs = lookup_bool "fast_descrs"
    val peephole_optim = lookup_bool "peephole_optim"
    val timeout = if auto then lookup_time "auto_timeout"
                  else lookup_time "timeout"
    val tac_timeout = lookup_time "tac_timeout"
    val sym_break = Int.max (0, lookup_int "sym_break")
    val sharing_depth = Int.max (1, lookup_int "sharing_depth")
    val flatten_props = lookup_bool "flatten_props"
    val max_threads = Int.max (0, lookup_int "max_threads")
    val show_all = debug orelse lookup_bool "show_all"
    val show_skolems = show_all orelse lookup_bool "show_skolems"
    val show_datatypes = show_all orelse lookup_bool "show_datatypes"
    val show_consts = show_all orelse lookup_bool "show_consts"
    val formats = lookup_ints_assigns read_term_polymorphic "format" 0
    val evals = lookup_term_list "eval"
    val max_potential = if auto then 0
                        else Int.max (0, lookup_int "max_potential")
    val max_genuine = Int.max (0, lookup_int "max_genuine")
    val check_potential = lookup_bool "check_potential"
    val check_genuine = lookup_bool "check_genuine"
    val batch_size = case lookup_int_option "batch_size" of
                       SOME n => Int.max (1, n)
                     | NONE => if debug then 1 else 64
    val expect = lookup_string "expect"
  in
    {cards_assigns = cards_assigns, maxes_assigns = maxes_assigns,
     iters_assigns = iters_assigns, bisim_depths = bisim_depths, boxes = boxes,
     monos = monos, wfs = wfs, sat_solver = sat_solver, blocking = blocking,
     falsify = falsify, debug = debug, verbose = verbose, overlord = overlord,
     user_axioms = user_axioms, assms = assms,
     coalesce_type_vars = coalesce_type_vars, destroy_constrs = destroy_constrs,
     specialize = specialize, skolemize = skolemize,
     star_linear_preds = star_linear_preds, uncurry = uncurry,
     fast_descrs = fast_descrs, peephole_optim = peephole_optim,
     timeout = timeout, tac_timeout = tac_timeout, sym_break = sym_break,
     sharing_depth = sharing_depth, flatten_props = flatten_props,
     max_threads = max_threads, show_skolems = show_skolems,
     show_datatypes = show_datatypes, show_consts = show_consts,
     formats = formats, evals = evals, max_potential = max_potential,
     max_genuine = max_genuine, check_potential = check_potential,
     check_genuine = check_genuine, batch_size = batch_size, expect = expect}
  end

(* theory -> (string * string) list -> params *)
fun default_params thy =
  extract_params (ProofContext.init thy) false (default_raw_params thy)
  o map (apsnd single)

(* OuterParse.token list -> string * OuterParse.token list *)
val scan_key = Scan.repeat1 OuterParse.typ_group >> space_implode " "

(* OuterParse.token list -> string list * OuterParse.token list *)
val scan_value =
  Scan.repeat1 (OuterParse.minus >> single
                || Scan.repeat1 (Scan.unless OuterParse.minus OuterParse.name)
                || OuterParse.$$$ "," |-- OuterParse.number >> prefix ","
                   >> single) >> flat

(* OuterParse.token list -> raw_param * OuterParse.token list *)
val scan_param =
  scan_key -- (Scan.option (OuterParse.$$$ "=" |-- scan_value) >> these)
(* OuterParse.token list -> raw_param list option * OuterParse.token list *)
val scan_params = Scan.option (OuterParse.$$$ "[" |-- OuterParse.list scan_param
                               --| OuterParse.$$$ "]")

(* Proof.context -> ('a -> 'a) -> 'a -> 'a *)
fun handle_exceptions ctxt f x =
  f x
  handle ARG (loc, details) =>
         error ("Bad argument(s) to " ^ quote loc ^ ": " ^ details ^ ".")
       | BAD (loc, details) =>
         error ("Internal error (" ^ quote loc ^ "): " ^ details ^ ".")
       | LIMIT (_, details) =>
         (warning ("Limit reached: " ^ details ^ "."); x)
       | NOT_SUPPORTED details =>
         (warning ("Unsupported case: " ^ details ^ "."); x)
       | NUT (loc, us) =>
         error ("Invalid intermediate term" ^ plural_s_for_list us ^
                " (" ^ quote loc ^ "): " ^
                commas (map (string_for_nut ctxt) us) ^ ".")
       | REP (loc, Rs) =>
         error ("Invalid representation" ^ plural_s_for_list Rs ^
                " (" ^ quote loc ^ "): " ^ commas (map string_for_rep Rs) ^ ".")
       | TERM (loc, ts) =>
         error ("Invalid term" ^ plural_s_for_list ts ^
                " (" ^ quote loc ^ "): " ^
                commas (map (Syntax.string_of_term ctxt) ts) ^ ".")
       | TYPE (loc, Ts, ts) =>
         error ("Invalid type" ^ plural_s_for_list Ts ^
                (if null ts then
                   ""
                 else
                   " for term" ^ plural_s_for_list ts ^ " " ^
                   commas (map (quote o Syntax.string_of_term ctxt) ts)) ^
                " (" ^ quote loc ^ "): " ^
                commas (map (Syntax.string_of_typ ctxt) Ts) ^ ".")
       | Kodkod.SYNTAX (_, details) =>
         (warning ("Ill-formed Kodkodi output: " ^ details ^ "."); x)
       | Refute.REFUTE (loc, details) =>
         error ("Unhandled Refute error (" ^ quote loc ^ "): " ^ details ^ ".")

(* raw_param list -> bool -> int -> Proof.state -> Proof.state *)
fun pick_nits override_params auto subgoal state =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val thm = #goal (Proof.raw_goal state)
    val _ = List.app check_raw_param override_params
    val params as {blocking, debug, ...} =
      extract_params ctxt auto (default_raw_params thy) override_params
    (* unit -> Proof.state *)
    fun go () =
      (if auto then perhaps o try
       else if debug then fn f => fn x => f x
       else handle_exceptions ctxt)
      (fn state => pick_nits_in_subgoal state params auto subgoal |> snd)
      state
  in
    if auto orelse blocking then
      go ()
    else
      (SimpleThread.fork true (fn () => (go (); ()));
       state)
  end

(* (TableFun().key * string list) list option * int option
   -> Toplevel.transition -> Toplevel.transition *)
fun nitpick_trans (opt_params, opt_subgoal) =
  Toplevel.keep (K ()
      o pick_nits (these opt_params) false (the_default 1 opt_subgoal)
      o Toplevel.proof_of)

(* raw_param -> string *)
fun string_for_raw_param (name, value) =
  name ^ " = " ^ stringify_raw_param_value value

(* bool -> Proof.state -> Proof.state *)
fun pick_nits_auto interactive state =
  let val thy = Proof.theory_of state in
    ((interactive andalso not (!Toplevel.quiet)
      andalso the (general_lookup_bool false (default_raw_params thy)
                  (SOME false) "auto"))
     ? pick_nits [] true 0) state
  end

(* theory -> theory *)
fun register_auto thy =
  (not (is_registered_auto thy)
   ? (set_registered_auto
      #> Context.theory_map (Specification.add_theorem_hook pick_nits_auto)))
  thy

(* (TableFun().key * string) list option -> Toplevel.transition
   -> Toplevel.transition *)
fun nitpick_params_trans opt_params =
  Toplevel.theory
      (fn thy =>
          let val thy = fold set_default_raw_param (these opt_params) thy in
            writeln ("Default parameters for Nitpick:\n" ^
                     (case rev (default_raw_params thy) of
                        [] => "none"
                      | params =>
                        (map check_raw_param params;
                         params |> map string_for_raw_param |> sort_strings
                                |> cat_lines)));
            register_auto thy
          end)

(* OuterParse.token list
   -> (Toplevel.transition -> Toplevel.transition) * OuterParse.token list *)
fun scan_nitpick_command tokens =
  (scan_params -- Scan.option OuterParse.nat) tokens |>> nitpick_trans
fun scan_nitpick_params_command tokens =
  scan_params tokens |>> nitpick_params_trans

val _ = OuterSyntax.improper_command "nitpick"
            "try to find a counterexample for a given subgoal using Kodkod"
            OuterKeyword.diag scan_nitpick_command
val _ = OuterSyntax.command "nitpick_params"
            "set and display the default parameters for Nitpick"
            OuterKeyword.thy_decl scan_nitpick_params_command

end;
