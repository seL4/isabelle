(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.
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
      val toplevel: (unit -> 'a) -> 'a
    end;
end;

signature OUTER_SYNTAX =
sig
  include BASIC_OUTER_SYNTAX
  type token
  type parser
  val get_lexicons: unit -> Scan.lexicon * Scan.lexicon
  val command_keyword: string -> OuterKeyword.T option
  val command: string -> string -> OuterKeyword.T ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val markup_command: ThyOutput.markup -> string -> string -> OuterKeyword.T ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val improper_command: string -> string -> OuterKeyword.T ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val is_keyword: string -> bool
  val dest_keywords: unit -> string list
  val dest_parsers: unit -> (string * string * string * bool) list
  val print_outer_syntax: unit -> unit
  val print_commands: Toplevel.transition -> Toplevel.transition
  val add_keywords: string list -> unit
  val add_parsers: parser list -> unit
  val check_text: string * Position.T -> Toplevel.node option -> unit
  val isar: bool -> unit Toplevel.isar
  val scan: string -> OuterLex.token list
  val read: OuterLex.token list -> (string * OuterLex.token list * Toplevel.transition) list
end;

structure OuterSyntax : OUTER_SYNTAX  =
struct

structure T = OuterLex;
structure P = OuterParse;


(** outer syntax **)

(* parsers *)

type token = T.token;
type parser_fn = token list -> (Toplevel.transition -> Toplevel.transition) * token list;

datatype parser =
  Parser of string * (string * OuterKeyword.T * ThyOutput.markup option) * bool * parser_fn;

fun parser int_only markup name comment kind parse =
  Parser (name, (comment, kind, markup), int_only, parse);


(* parse command *)

local

fun terminate false = Scan.succeed ()
  | terminate true = P.group "end of input" (Scan.option P.sync -- P.semicolon >> K ());

fun trace false parse = parse
  | trace true parse = Scan.trace parse >> (fn (f, toks) => f o Toplevel.source toks);

fun body cmd do_trace (name, _) =
  (case cmd name of
    SOME (int_only, parse) =>
      P.!!! (Scan.prompt (name ^ "# ") (trace do_trace (P.tags |-- parse) >> pair int_only))
  | NONE => sys_error ("no parser for outer syntax command " ^ quote name));

in

fun command do_terminate do_trace cmd =
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
val global_parsers =
  ref (Symtab.empty: (((string * OuterKeyword.T) * (bool * parser_fn)) * ThyOutput.markup option)
    Symtab.table);
val global_markups = ref ([]: (string * ThyOutput.markup) list);

fun change_lexicons f =
  let val lexs = f (! global_lexicons) in
    (case (op inter_string) (pairself Scan.dest_lexicon lexs) of
      [] => global_lexicons := lexs
    | bads => error ("Clash of outer syntax commands and keywords: " ^ commas_quote bads))
  end;

fun make_markups () = global_markups :=
  Symtab.fold (fn (name, (_, SOME m)) => cons (name, m) | _ => I) (! global_parsers) [];

fun change_parsers f = (Library.change global_parsers f; make_markups ());

in


(* access current syntax *)

(*Note: the syntax for files is statically determined at the very
  beginning; for interactive processing it may change dynamically.*)

fun get_lexicons () = ! global_lexicons;
fun get_parsers () = ! global_parsers;
fun get_parser () = Option.map (#2 o #1) o Symtab.lookup (get_parsers ());

fun command_keyword name =
  Option.map (fn (((_, k), _), _) => k) (Symtab.lookup (get_parsers ()) name);
fun command_tags name = these ((Option.map OuterKeyword.tags_of) (command_keyword name));

fun is_markup kind name = (AList.lookup (op =) (! global_markups) name = SOME kind);


(* augment syntax *)

fun add_keywords keywords =
  change_lexicons (apfst (Scan.extend_lexicon (map Symbol.explode keywords)));

fun add_parser (Parser (name, (comment, kind, markup), int_only, parse)) tab =
 (if not (Symtab.defined tab name) then ()
  else warning ("Redefined outer syntax command " ^ quote name);
  Symtab.update (name, (((comment, kind), (int_only, parse)), markup)) tab);

fun add_parsers parsers =
  (change_parsers (fold add_parser parsers);
    change_lexicons (apsnd (Scan.extend_lexicon
      (map (fn Parser (name, _, _, _) => Symbol.explode name) parsers))));

end;


(* print syntax *)

fun is_keyword s = Scan.is_literal (#1 (get_lexicons ())) (Symbol.explode s);
fun dest_keywords () = Scan.dest_lexicon (#1 (get_lexicons ()));

fun dest_parsers () =
  get_parsers () |> Symtab.dest |> sort_wrt #1
  |> map (fn (name, (((cmt, kind), (int_only, _)), _)) =>
    (name, cmt, OuterKeyword.kind_of kind, int_only));

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

val print_commands = Toplevel.imperative print_outer_syntax;



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
    |> Source.source T.stopper (Scan.bulk (fn xs => P.!!! (command term do_trace (cmd ())) xs))
        (Option.map recover do_recover)
    |> Source.map_filter I
  end;


(* interactive source of toplevel transformers *)

fun isar term =
  Source.tty
  |> Symbol.source true
  |> T.source (SOME true) get_lexicons Position.none
  |> toplevel_source term false (SOME true) get_parser;


(* scan text *)

fun scan str =
  Source.of_string str
  |> Symbol.source false
  |> T.source (SOME false) get_lexicons Position.none
  |> Source.exhaust;


(* read tokens with trace *)

fun read toks =
  Source.of_list toks
  |> toplevel_source false true (SOME false) get_parser
  |> Source.exhaust
  |> map (fn tr => (Toplevel.name_of tr, the (Toplevel.source_of tr), tr));



(** read theory **)

(* check_text *)

fun check_text s state = (ThyOutput.eval_antiquote (#1 (get_lexicons ())) state s; ());


(* load_thy *)

local

fun try_ml_file dirs name time =
  let val path = ThyLoad.ml_path name in
    if is_none (ThyLoad.check_file dirs path) then ()
    else
      let
        val _ = legacy_feature ("loading attached ML script " ^ quote (Path.implode path));
        val tr = Toplevel.imperative (fn () => ThyInfo.load_file time path);
        val tr_name = if time then "time_use" else "use";
      in Toplevel.excursion [Toplevel.empty |> Toplevel.name tr_name |> tr] end
  end;

fun run_thy dirs name time =
  let
    val master as ((path, _), _) = ThyLoad.check_thy dirs name false;
    val text = Source.of_list (Library.untabify (explode (File.read path)));

    val _ = Present.init_theory name;
    val _ = Present.verbatim_source name (fn () => Source.exhaust (Symbol.source false text));
    val toks = text
      |> Symbol.source false
      |> T.source NONE (K (get_lexicons ())) (Position.path path)
      |> Source.exhausted;
    val trs = toks
      |> toplevel_source false false NONE (K (get_parser ()))
      |> Source.exhaust;

    val _ = if time then writeln ("\n**** Starting theory " ^ quote name ^ " ****") else ();
    val _ = cond_timeit time (fn () =>
      ThyOutput.process_thy (#1 (get_lexicons ())) command_tags is_markup trs toks
      |> Buffer.content
      |> Present.theory_output name);
    val _ = if time then writeln ("**** Finished theory " ^ quote name ^ " ****\n") else ();

  in master end;

fun load_thy dirs name ml time =
  let
    val master = run_thy dirs name time;
    val _ = ML_Context.set_context (SOME (Context.Theory (ThyInfo.get_theory name)));
    val _ = if ml then try_ml_file dirs name time else ();
  in master end;

in

val _ = ThyLoad.load_thy_fn := load_thy;

end;



(** the read-eval-print loop **)

(* main loop *)

fun gen_loop term =
 (ML_Context.set_context NONE;
  Toplevel.loop (isar term));

fun gen_main term =
 (Toplevel.init_state ();
  writeln (Session.welcome ());
  gen_loop term);

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

  fun main () = gen_main false;
  fun loop () = gen_loop false;
  fun sync_main () = gen_main true;
  fun sync_loop () = gen_loop true;
  val toplevel = Toplevel.program;
end;


(*final declarations of this structure!*)
val command = parser false NONE;
val markup_command = parser false o SOME;
val improper_command = parser true NONE;

end;

structure ThyLoad: THY_LOAD = ThyLoad;
structure BasicOuterSyntax: BASIC_OUTER_SYNTAX = OuterSyntax;
open BasicOuterSyntax;
