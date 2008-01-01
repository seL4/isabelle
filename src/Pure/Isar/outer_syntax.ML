(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax. Note: the syntax for files is
statically determined at the very beginning; for interactive processing
it may change dynamically.
*)

signature BASIC_OUTER_SYNTAX =
sig
  structure Isar:
    sig
      val state: unit -> Toplevel.state
      val exn: unit -> (exn * string) option
      val context: unit -> Proof.context
      val goal: unit -> thm list * thm
      val main: unit -> unit
      val loop: unit -> unit
      val sync_main: unit -> unit
      val sync_loop: unit -> unit
      val secure_main: unit -> unit
      val toplevel: (unit -> 'a) -> 'a
    end;
end;

signature OUTER_SYNTAX =
sig
  include BASIC_OUTER_SYNTAX
  type parser_fn = OuterLex.token list ->
    (Toplevel.transition -> Toplevel.transition) * OuterLex.token list
  val get_lexicons: unit -> Scan.lexicon * Scan.lexicon
  val command_keyword: string -> OuterKeyword.T option
  val is_keyword: string -> bool
  val keywords: string list -> unit
  val command: string -> string -> OuterKeyword.T -> parser_fn -> unit
  val markup_command: ThyOutput.markup -> string -> string -> OuterKeyword.T -> parser_fn -> unit
  val improper_command: string -> string -> OuterKeyword.T -> parser_fn -> unit
  val dest_keywords: unit -> string list
  val dest_parsers: unit -> (string * string * string * bool) list
  val print_outer_syntax: unit -> unit
  val report: unit -> unit
  val check_text: string * Position.T -> Toplevel.node option -> unit
  val scan: string -> OuterLex.token list
  val read: OuterLex.token list -> (string * OuterLex.token list * Toplevel.transition) list
  val parse: Position.T -> string -> Toplevel.transition list
  val isar: bool -> unit Toplevel.isar
end;

structure OuterSyntax : OUTER_SYNTAX  =
struct

structure T = OuterLex;
structure P = OuterParse;


(** outer syntax **)

(* diagnostics *)

fun report_keyword name =
  Pretty.markup (Markup.keyword_decl name)
    [Pretty.str ("Outer syntax keyword: " ^ quote name)];

fun report_command name kind =
  Pretty.markup (Markup.command_decl name kind)
    [Pretty.str ("Outer syntax command: " ^ quote name ^ " (" ^ kind ^ ")")];


(* parsers *)

type parser_fn = T.token list -> (Toplevel.transition -> Toplevel.transition) * T.token list;

datatype parser = Parser of
 {comment: string,
  kind: OuterKeyword.T,
  markup: ThyOutput.markup option,
  int_only: bool,
  parse: parser_fn};

fun make_parser comment kind markup int_only parse =
  Parser {comment = comment, kind = kind, markup = markup, int_only = int_only, parse = parse};


(* parse command *)

local

fun terminate false = Scan.succeed ()
  | terminate true = P.group "end of input" (Scan.option P.sync -- P.semicolon >> K ());

fun trace false parse = parse
  | trace true parse = Scan.trace parse >> (fn (f, toks) => f o Toplevel.source toks);

fun body cmd do_trace (name, _) =
  (case cmd name of
    SOME (Parser {int_only, parse, ...}) =>
      P.!!! (Scan.prompt (name ^ "# ") (trace do_trace (P.tags |-- parse) >> pair int_only))
  | NONE => sys_error ("no parser for outer syntax command " ^ quote name));

in

fun parse_command do_terminate do_trace cmd =
  P.semicolon >> K NONE ||
  P.sync >> K NONE ||
  (P.position P.command :-- body cmd do_trace) --| terminate do_terminate
    >> (fn ((name, pos), (int_only, f)) =>
      SOME (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
        Toplevel.interactive int_only |> f));

end;



(** global outer syntax **)

local

val global_lexicons = ref (Scan.empty_lexicon, Scan.empty_lexicon);
val global_parsers = ref (Symtab.empty: parser Symtab.table);
val global_markups = ref ([]: (string * ThyOutput.markup) list);

fun change_lexicons f = CRITICAL (fn () =>
  let val lexs = f (! global_lexicons) in
    (case (op inter_string) (pairself Scan.dest_lexicon lexs) of
      [] => global_lexicons := lexs
    | bads => error ("Clash of outer syntax commands and keywords: " ^ commas_quote bads))
  end);

fun change_parsers f = CRITICAL (fn () =>
 (change global_parsers f;
  global_markups :=
    Symtab.fold (fn (name, Parser {markup = SOME m, ...}) => cons (name, m) | _ => I)
      (! global_parsers) []));

in

(* access current syntax *)

fun get_lexicons () = CRITICAL (fn () => ! global_lexicons);
fun get_parsers () = CRITICAL (fn () => ! global_parsers);
fun get_markups () = CRITICAL (fn () => ! global_markups);

fun get_parser () = Symtab.lookup (get_parsers ());

fun command_keyword name =
  (case Symtab.lookup (get_parsers ()) name of
    SOME (Parser {kind, ...}) => SOME kind
  | NONE => NONE);

fun command_tags name = these ((Option.map OuterKeyword.tags_of) (command_keyword name));

fun is_markup kind name = AList.lookup (op =) (get_markups ()) name = SOME kind;


(* augment syntax *)

fun keywords names =
 (change_lexicons (apfst (Scan.extend_lexicon (map Symbol.explode names)));
  List.app (Pretty.writeln o report_keyword) names);


fun add_parser (name, parser as Parser {kind, ...}) =
 (if not (Symtab.defined (get_parsers ()) name) then ()
  else warning ("Redefining outer syntax command " ^ quote name);
  change_parsers (Symtab.update (name, parser));
  change_lexicons (apsnd (Scan.extend_lexicon [Symbol.explode name]));
  Pretty.writeln (report_command name (OuterKeyword.kind_of kind)));

fun command name comment kind parse =
  add_parser (name, make_parser comment kind NONE false parse);

fun markup_command markup name comment kind parse =
  add_parser (name, make_parser comment kind (SOME markup) false parse);

fun improper_command name comment kind parse =
  add_parser (name, make_parser comment kind NONE true parse);

end;


(* inspect syntax *)

fun is_keyword s = Scan.is_literal (#1 (get_lexicons ())) (Symbol.explode s);
fun dest_keywords () = Scan.dest_lexicon (#1 (get_lexicons ()));

fun dest_parsers () =
  get_parsers () |> Symtab.dest |> sort_wrt #1
  |> map (fn (name, Parser {comment, kind, int_only, ...}) =>
    (name, comment, OuterKeyword.kind_of kind, int_only));

fun print_outer_syntax () =
  let
    fun pretty_cmd (name, comment, _, _) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = List.partition #4 (dest_parsers ());
  in
    [Pretty.strs ("syntax keywords:" :: map quote (dest_keywords ())),
      Pretty.big_list "commands:" (map pretty_cmd cmds),
      Pretty.big_list "interactive-only commands:" (map pretty_cmd int_cmds)]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun report () =
  (map report_keyword (dest_keywords ()) @
    map (fn (name, _, kind, _) => report_command name kind) (dest_parsers ()))
  |> Pretty.chunks |> Pretty.writeln;



(** toplevel parsing **)

(* basic sources *)

fun toplevel_source term do_trace do_recover cmd src =
  let
    val no_terminator =
      Scan.unless P.semicolon (Scan.one (T.not_sync andf T.not_eof));
    fun recover int =
      (int, fn _ => Scan.prompt "recover# " (Scan.repeat no_terminator) >> K [NONE]);
  in
    src
    |> T.source_proper
    |> Source.source T.stopper
      (Scan.bulk (P.$$$ "--" -- P.!!! P.text >> K NONE || P.not_eof >> SOME))
        (Option.map recover do_recover)
    |> Source.map_filter I
    |> Source.source T.stopper
        (Scan.bulk (fn xs => P.!!! (parse_command term do_trace (cmd ())) xs))
        (Option.map recover do_recover)
    |> Source.map_filter I
  end;


(* off-line scanning/parsing *)

(*tokens*)
fun scan str =
  Source.of_string str
  |> Symbol.source false
  |> T.source (SOME false) get_lexicons Position.none
  |> Source.exhaust;

(*commands from tokens, with trace*)
fun read toks =
  Source.of_list toks
  |> toplevel_source false true NONE get_parser
  |> Source.exhaust
  |> map (fn tr => (Toplevel.name_of tr, the (Toplevel.source_of tr), tr));

(*commands from string, without trace*)
fun parse pos str =
  Source.of_string str
  |> Symbol.source false
  |> T.source (SOME false) get_lexicons pos
  |> toplevel_source false false NONE get_parser
  |> Source.exhaust;


(* interactive source of toplevel transformers *)

fun isar term =
  Source.tty
  |> Symbol.source true
  |> T.source (SOME true) get_lexicons Position.none
  |> toplevel_source term false (SOME true) get_parser;



(** read theory **)

(* check_text *)

fun check_text s state = (ThyOutput.eval_antiquote (#1 (get_lexicons ())) state s; ());


(* load_thy *)

local

fun try_ml_file dir name time =
  let val path = ThyLoad.ml_path name in
    if is_none (ThyLoad.check_file dir path) then ()
    else
      let
        val _ = legacy_feature ("loading attached ML script " ^ quote (Path.implode path));
        val tr = Toplevel.imperative (fn () =>
          ML_Context.setmp (SOME (Context.Theory (ThyInfo.get_theory name)))
            (fn () => ThyInfo.load_file time path) ());
        val tr_name = if time then "time_use" else "use";
      in Toplevel.excursion [Toplevel.empty |> Toplevel.name tr_name |> tr] end
  end;

fun run_thy dir name pos text time =
  let
    val text_src = Source.of_list (Library.untabify text);

    val _ = Present.init_theory name;
    val _ = Present.verbatim_source name (fn () => Source.exhaust (Symbol.source false text_src));
    val toks = text_src
      |> Symbol.source false
      |> T.source NONE (K (get_lexicons ())) pos
      |> Source.exhausted;
    val trs = toks
      |> toplevel_source false false NONE (K (get_parser ()))
      |> Source.exhaust;

    val _ = if time then writeln ("\n**** Starting theory " ^ quote name ^ " ****") else ();
    val _ = cond_timeit time "" (fn () =>
      ThyOutput.process_thy (#1 (get_lexicons ())) command_tags is_markup trs toks
      |> Buffer.content
      |> Present.theory_output name);
    val _ = if time then writeln ("**** Finished theory " ^ quote name ^ " ****\n") else ();
  in () end;

fun load_thy dir name pos text time =
 (run_thy dir name pos text time;
  try_ml_file dir name time);

in

val _ = ThyLoad.load_thy_fn := load_thy;

end;



(** the read-eval-print loop **)

(* main loop *)

fun gen_loop secure do_terminate =
 (CRITICAL (fn () => ML_Context.set_context NONE);
  Toplevel.loop secure (isar do_terminate));

fun gen_main secure do_terminate =
 (Toplevel.init_state ();
  writeln (Session.welcome ());
  gen_loop secure do_terminate);

structure Isar =
struct
  val state = Toplevel.get_state;
  val exn = Toplevel.exn;

  fun context () =
    Toplevel.context_of (state ())
      handle Toplevel.UNDEF => error "Unknown context";

  fun goal () =
    #2 (Proof.get_goal (Toplevel.proof_of (state ())))
      handle Toplevel.UNDEF => error "No goal present";

  fun main () = gen_main (Secure.is_secure ()) false;
  fun loop () = gen_loop (Secure.is_secure ()) false;
  fun sync_main () = gen_main (Secure.is_secure ()) true;
  fun sync_loop () = gen_loop (Secure.is_secure ()) true;
  fun secure_main () = gen_main true true;
  val toplevel = Toplevel.program;
end;

end;

structure ThyLoad: THY_LOAD = ThyLoad;
structure BasicOuterSyntax: BASIC_OUTER_SYNTAX = OuterSyntax;
open BasicOuterSyntax;
