(*  Title:      Pure/Isar/isar_output.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Isar theory output.
*)

signature ISAR_OUTPUT =
sig
  val add_commands: (string * (Args.src -> Toplevel.state -> string)) list -> unit
  val add_options: (string * (string -> (unit -> string) -> unit -> string)) list -> unit
  val print_antiquotations: unit -> unit
  val boolean: string -> bool
  val integer: string -> int
  val args: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    (Args.src -> Proof.context -> 'a -> string) -> Args.src -> Toplevel.state -> string
  datatype markup = Markup | MarkupEnv | Verbatim
  val interest_level: int ref
  val modes: string list ref
  val parse_thy: (markup -> OuterLex.token list -> OuterLex.token * OuterLex.token list) ->
    Scan.lexicon -> Toplevel.transition list -> (OuterLex.token, 'a) Source.source ->
      (Toplevel.transition * (Toplevel.state -> Buffer.T -> Buffer.T)) list * Buffer.T
  val display: bool ref
  val quotes: bool ref
  val indent: int ref
  val source: bool ref
  val output_with: (Proof.context -> 'a -> Pretty.T) -> Args.src ->
    Proof.context -> 'a -> string
end;

structure IsarOutput: ISAR_OUTPUT =
struct

structure T = OuterLex;
structure P = OuterParse;


(** maintain global commands **)

local

val global_commands =
  ref (Symtab.empty: (Args.src -> Toplevel.state -> string) Symtab.table);

val global_options =
  ref (Symtab.empty: (string -> (unit -> string) -> unit -> string) Symtab.table);


fun add_item kind (tab, (name, x)) =
 (if is_none (Symtab.lookup (tab, name)) then ()
  else warning ("Redefined antiquotation output " ^ kind ^ ": " ^ quote name);
  Symtab.update ((name, x), tab));

fun add_items kind xs tab = foldl (add_item kind) (tab, xs);

in

val add_commands = Library.change global_commands o (add_items "command");
val add_options = Library.change global_options o (add_items "option");

fun command src =
  let val ((name, _), pos) = Args.dest_src src in
    (case Symtab.lookup (! global_commands, name) of
      None => error ("Unknown antiquotation command: " ^ quote name ^ Position.str_of pos)
    | Some f => transform_failure (curry Comment.OUTPUT_FAIL (name, pos)) (f src))
  end;

fun option (name, s) f () =
  (case Symtab.lookup (! global_options, name) of
    None => error ("Unknown antiquotation option: " ^ quote name)
  | Some opt => opt s f ());

fun options [] f = f
  | options (opt :: opts) f = option opt (options opts f);


fun print_antiquotations () =
 [Pretty.big_list "antiquotation commands:" (map Pretty.str (Symtab.keys (! global_commands))),
  Pretty.big_list "antiquotation options:" (map Pretty.str (Symtab.keys (! global_options)))]
 |> Pretty.chunks |> Pretty.writeln;

end;



(** syntax of antiquotations **)

(* option values *)

fun boolean "" = true
  | boolean "true" = true
  | boolean "false" = false
  | boolean s = error ("Bad boolean value: " ^ quote s);

fun integer s =
  let
    fun int ss =
      (case Term.read_int ss of (i, []) => i | _ => error ("Bad integer value: " ^ quote s));
  in (case Symbol.explode s of "-" :: ss => ~ (int ss) | ss => int ss) end;


(* args syntax *)

fun syntax (scan: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list))) =
  Args.syntax "antiquotation" scan;

fun args scan f src state : string =
  let val (ctxt, x) = syntax scan src (Toplevel.context_of state)
  in f src ctxt x end;


(* outer syntax *)

local

val property = P.xname -- Scan.optional (P.$$$ "=" |-- P.!!! P.xname) "";
val properties = Scan.optional (P.$$$ "[" |-- P.!!! (P.enum "," property --| P.$$$ "]")) [];

val antiq = P.position P.xname -- properties -- P.arguments --| Scan.ahead P.eof
  >> (fn (((x, pos), y), z) => (y, Args.src ((x, z), pos)));

fun antiq_args_aux keyword_lexicon (str, pos) =
  Source.of_string str
  |> Symbol.source false
  |> T.source false (K (keyword_lexicon, Scan.empty_lexicon)) pos
  |> T.source_proper
  |> Source.source T.stopper (Scan.error (Scan.bulk (P.!!! antiq))) None
  |> Source.exhaust;

in

fun antiq_args lex (s, pos) =
  (case antiq_args_aux lex (s, pos) of [x] => x | _ => raise ERROR) handle ERROR =>
    error ("Malformed antiquotation: " ^ quote ("@{" ^ s ^ "}") ^ Position.str_of pos);

end;


(* eval_antiquote *)

val modes = ref ([]: string list);

fun eval_antiquote lex state (str, pos) =
  let
    fun expand (Antiquote.Text s) = s
      | expand (Antiquote.Antiq x) =
          let val (opts, src) = antiq_args lex x in
            options opts (fn () => command src state) ();  (*preview errors!*)
            Library.setmp print_mode (! modes @ Latex.modes @ ! print_mode)
              (options opts (fn () => command src state)) ()
          end;
    val ants = Antiquote.antiquotes_of (str, pos);
  in
    if Toplevel.is_toplevel state andalso exists Antiquote.is_antiq ants then
      error ("Cannot expand antiquotations at top-level" ^ Position.str_of pos)
    else implode (map expand ants)
  end;



(** present theory source **)

(* present_tokens *)

val interest_level = ref 0;

fun present_tokens lex (flag, toks) state =
  Buffer.add (case flag of None => "" | Some b => Latex.flag_markup b) o
   (toks
    |> mapfilter (fn (tk, i) => if i > ! interest_level then None else Some tk)
    |> map (apsnd (eval_antiquote lex state))
    |> Latex.output_tokens
    |> Buffer.add);


(* parse_thy *)

datatype markup = Markup | MarkupEnv | Verbatim;

local

val opt_newline = Scan.option (Scan.one T.is_newline);

fun check_level i =
  if i > 0 then Scan.succeed ()
  else Scan.fail_with (K "Bad nesting of meta-comments");

val ignore =
  Scan.depend (fn i => opt_newline |-- P.position (Scan.one T.is_begin_ignore) >> pair (i + 1)) ||
  Scan.depend (fn i => P.position (Scan.one T.is_end_ignore) --|
    (opt_newline -- check_level i) >> pair (i - 1));

val ignore_cmd = Scan.state -- ignore
  >> (fn (i, (x, pos)) => (false, (None, ((Latex.Basic x, ("", pos)), i))));


val is_improper = not o (T.is_proper orf T.is_begin_ignore orf T.is_end_ignore);
val improper = Scan.any is_improper;

val improper_keep_indent = Scan.repeat
  (Scan.unless (Scan.one T.is_indent -- Scan.one T.is_proper) (Scan.one is_improper));

val improper_end =
  (improper -- P.semicolon) |-- improper_keep_indent ||
  improper_keep_indent;


val stopper =
  ((false, (None, ((Latex.Basic (#1 T.stopper), ("", Position.none)), 0))),
    fn (_, (_, ((Latex.Basic x, _), _))) => (#2 T.stopper x) | _ => false);

in

fun parse_thy markup lex trs src =
  let
    val text = P.position P.text;
    val token = Scan.depend (fn i =>
     (improper |-- markup Markup -- P.!!!! (improper |-- text --| improper_end)
        >> (fn (x, y) => (true, (Some true, ((Latex.Markup (T.val_of x), y), i)))) ||
      improper |-- markup MarkupEnv -- P.!!!! (improper |-- text --| improper_end)
        >> (fn (x, y) => (true, (Some true, ((Latex.MarkupEnv (T.val_of x), y), i)))) ||
      (P.$$$ "--" |-- P.!!!! (improper |-- text))
        >> (fn y => (false, (None, ((Latex.Markup "cmt", y), i)))) ||
      (improper -- markup Verbatim) |-- P.!!!! (improper |-- text --| improper_end)
        >> (fn y => (true, (None, ((Latex.Verbatim, y), i)))) ||
      P.position (Scan.one T.not_eof)
        >> (fn (x, pos) => (T.is_kind T.Command x, (Some false, ((Latex.Basic x, ("", pos)), i)))))
      >> pair i);

    val body = Scan.any (not o fst andf not o #2 stopper);
    val section = body -- Scan.one fst -- body
      >> (fn ((b1, c), b2) => (#1 (#2 c), map (snd o snd) (b1 @ (c :: b2))));

    val cmds =
      src
      |> Source.filter (not o T.is_semicolon)
      |> Source.source' 0 T.stopper (Scan.error (Scan.bulk (ignore_cmd || token))) None
      |> Source.source stopper (Scan.error (Scan.bulk section)) None
      |> Source.exhaust;
  in
    if length cmds = length trs then
      (trs ~~ map (present_tokens lex) cmds, Buffer.empty)
    else error "Messed-up outer syntax for presentation"
  end;

end;



(** setup default output **)

(* options *)

val display = ref false;
val quotes = ref false;
val indent = ref 0;
val source = ref false;

val _ = add_options
 [("show_types", Library.setmp Syntax.show_types o boolean),
  ("show_sorts", Library.setmp Syntax.show_sorts o boolean),
  ("eta_contract", Library.setmp Syntax.eta_contract o boolean),
  ("long_names", Library.setmp NameSpace.long_names o boolean),
  ("display", Library.setmp display o boolean),
  ("quotes", Library.setmp quotes o boolean),
  ("mode", fn s => fn f => fn () => Library.setmp print_mode (s :: ! print_mode) f ()),
  ("margin", Pretty.setmp_margin o integer),
  ("indent", Library.setmp indent o integer),
  ("source", Library.setmp source o boolean),
  ("goals_limit", Library.setmp goals_limit o integer)];


(* commands *)

fun cond_quote prt =
  if ! quotes then Pretty.quote prt else prt;

fun cond_display prt =
  if ! display then
    Pretty.string_of (Pretty.indent (! indent) prt)
    |> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
  else
    Pretty.str_of prt
    |> enclose "\\isa{" "}";

fun tweak_line s =
  if ! display then s else Symbol.strip_blanks s;

val pretty_text = Pretty.chunks o map Pretty.str o map tweak_line o Library.split_lines;

val pretty_source =
  pretty_text o space_implode " " o map Args.string_of o #2 o #1 o Args.dest_src;

fun pretty_term ctxt = ProofContext.pretty_term ctxt o ProofContext.extern_skolem ctxt;

fun pretty_thms ctxt thms =
  Pretty.chunks (map (pretty_term ctxt o Thm.prop_of) thms);

fun pretty_prf full ctxt thms =    (* FIXME context syntax!? *)
  Pretty.chunks (map (ProofSyntax.pretty_proof_of full) thms);

fun output_with pretty src ctxt x =
  let
    val prt = pretty ctxt x;      (*always pretty in order to catch errors!*)
    val prt' = if ! source then pretty_source src else prt;
  in cond_display (cond_quote prt') end;

fun output_goals main_goal src state = args (Scan.succeed ()) (output_with (fn _ => fn _ =>
  Pretty.chunks (Proof.pretty_goals main_goal (Toplevel.proof_of state
      handle Toplevel.UNDEF => error "No proof state")))) src state;

val _ = add_commands
 [("text", args (Scan.lift Args.name) (output_with (K pretty_text))),
  ("thm", args Attrib.local_thmss (output_with pretty_thms)),
  ("prf", args Attrib.local_thmss (output_with (pretty_prf false))),
  ("full_prf", args Attrib.local_thmss (output_with (pretty_prf true))),
  ("prop", args Args.local_prop (output_with pretty_term)),
  ("term", args Args.local_term (output_with pretty_term)),
  ("typ", args Args.local_typ_no_norm (output_with ProofContext.pretty_typ)),
  ("goals", output_goals true),
  ("subgoals", output_goals false)];

end;
