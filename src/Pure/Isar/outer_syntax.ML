(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.
*)

signature BASIC_OUTER_SYNTAX =
sig
  structure Isar:
    sig
      val main: unit -> unit
      val loop: unit -> unit
      val sync_main: unit -> unit
      val sync_loop: unit -> unit
    end;
end;

signature OUTER_SYNTAX =
sig
  include BASIC_OUTER_SYNTAX
  type token
  type parser
  val command: string -> string -> OuterKeyword.T ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val markup_command: IsarOutput.markup -> string -> string -> OuterKeyword.T ->
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
  val check_text: string * Position.T -> bool -> Toplevel.state -> unit
  val deps_thy: string -> bool -> Path.T -> string list * Path.T list
  val load_thy: string -> bool -> bool -> Path.T -> unit
  val isar: bool -> bool -> unit Toplevel.isar
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
  Parser of string * (string * OuterKeyword.T * IsarOutput.markup option) * bool * parser_fn;

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
      P.!!! (Scan.prompt (name ^ "# ") (trace do_trace parse >> pair int_only))
  | NONE => sys_error ("no parser for outer syntax command " ^ quote name));

in

fun command do_terminate do_trace cmd =
  P.semicolon >> K NONE ||
  P.sync >> K NONE ||
  ((P.position P.command --| P.tags) :-- body cmd do_trace) --| terminate do_terminate
    >> (fn ((name, pos), (int_only, f)) =>
      SOME (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
        Toplevel.interactive int_only |> f));

end;



(** global outer syntax **)

local

val global_lexicons = ref (Scan.empty_lexicon, Scan.empty_lexicon);
val global_parsers =
  ref (Symtab.empty: (((string * OuterKeyword.T) * (bool * parser_fn)) * IsarOutput.markup option)
    Symtab.table);
val global_markups = ref ([]: (string * IsarOutput.markup) list);

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
fun get_parser () = Option.map (#2 o #1) o curry Symtab.lookup (get_parsers ());

fun command_tags name =
  (case Symtab.lookup (get_parsers (), name) of
    SOME (((_, k), _), _) => OuterKeyword.tags_of k
  | NONE => []);

fun is_markup kind name = (assoc_string (! global_markups, name) = SOME kind);


(* augment syntax *)

fun add_keywords keywords = change_lexicons (apfst (fn lex =>
  (Scan.extend_lexicon lex (map Symbol.explode keywords))));

fun add_parser (Parser (name, (comment, kind, markup), int_only, parse)) tab =
 (if not (Symtab.defined tab name) then ()
  else warning ("Redefined outer syntax command " ^ quote name);
  Symtab.update ((name, (((comment, kind), (int_only, parse)), markup)), tab));

fun add_parsers parsers =
  (change_parsers (fold add_parser parsers);
    change_lexicons (apsnd (fn lex => Scan.extend_lexicon lex
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
      Pretty.big_list "proper commands:" (map pretty_cmd cmds),
      Pretty.big_list "improper commands (interactive-only):" (map pretty_cmd int_cmds)]
    |> Pretty.chunks |> Pretty.writeln
  end;

val print_commands = Toplevel.imperative print_outer_syntax;



(** toplevel parsing **)

(* basic sources *)

fun toplevel_source term do_trace do_recover cmd src =
  let
    val no_terminator =
      Scan.unless P.semicolon (Scan.one (T.not_sync andf T.not_eof));
    fun recover x = (Scan.prompt "recover# " (Scan.repeat no_terminator) >> K [NONE]) x;
  in
    src
    |> T.source_proper
    |> Source.source T.stopper
      (Scan.bulk (P.$$$ "--" -- P.!!! P.text >> K NONE || P.not_eof >> SOME))
      (if do_recover then SOME recover else NONE)
    |> Source.mapfilter I
    |> Source.source T.stopper (Scan.bulk (fn xs => P.!!! (command term do_trace (cmd ())) xs))
      (if do_recover then SOME recover else NONE)
    |> Source.mapfilter I
  end;


(* interactive source of toplevel transformers *)

fun isar term no_pos =
  Source.tty
  |> Symbol.source true
  |> T.source true get_lexicons
    (if no_pos then Position.none else Position.line_name 1 "stdin")
  |> toplevel_source term false true get_parser;


(* scan text *)

fun scan str =
  Source.of_string str
  |> Symbol.source false
  |> T.source true get_lexicons Position.none
  |> Source.exhaust;


(* read tokens with trace *)

fun read toks =
  Source.of_list toks
  |> toplevel_source false true true get_parser
  |> Source.exhaust
  |> map (fn tr => (Toplevel.name_of tr, the (Toplevel.source_of tr), tr));



(** read theory **)

(* check_text *)

fun check_text s true state = (IsarOutput.eval_antiquote (#1 (get_lexicons ())) state s; ())
  | check_text _ false _ = ();


(* deps_thy *)

fun deps_thy name ml path =
  let
    val src = Source.of_string (File.read path);
    val pos = Path.position path;
    val (name', parents, files) = ThyHeader.scan (src, pos);
    val ml_path = ThyLoad.ml_path name;
    val ml_file = if ml andalso is_some (ThyLoad.check_file NONE ml_path) then [ml_path] else [];
  in
    if name <> name' then
      error ("Filename " ^ quote (Path.pack path) ^
        " does not agree with theory name " ^ quote name')
    else (parents, map (Path.unpack o #1) files @ ml_file)
  end;


(* load_thy *)

local

fun try_ml_file name time =
  let
    val path = ThyLoad.ml_path name;
    val tr = Toplevel.imperative (fn () => ThyInfo.load_file time path);
    val tr_name = if time then "time_use" else "use";
  in
    if is_none (ThyLoad.check_file NONE path) then ()
    else Toplevel.excursion [Toplevel.empty |> Toplevel.name tr_name |> tr]
  end;

fun run_thy name path =
  let
    val pos = Path.position path;
    val text = Library.untabify (explode (File.read path));
    val text_src = Source.of_list text;
    fun present_text () = Source.exhaust (Symbol.source false text_src);
  in
    Present.init_theory name;
    Present.verbatim_source name present_text;
    if ThyHeader.is_old (text_src, pos) then (ThySyn.load_thy name text;
      Present.old_symbol_source name present_text)   (*note: text presented twice*)
    else
      let
        val tok_src = text_src
          |> Symbol.source false
          |> T.source false (K (get_lexicons ())) pos
          |> Source.exhausted;
        val trs =
          tok_src
          |> toplevel_source false false false (K (get_parser ()))
          |> Source.exhaust;
      in
        IsarOutput.present_thy (#1 (get_lexicons ())) command_tags is_markup trs tok_src
        |> Buffer.content
        |> Present.theory_output name
      end
  end;

in

fun load_thy name ml time path =
 (if time then
    timeit (fn () =>
     (writeln ("\n**** Starting theory " ^ quote name ^ " ****");
      run_thy name path;
      writeln ("**** Finished theory " ^ quote name ^ " ****\n")))
  else run_thy name path;
  Context.context (ThyInfo.get_theory name);
  if ml then try_ml_file name time else ());

end;



(** the read-eval-print loop **)

(* main loop *)

fun gen_loop term no_pos =
 (Context.reset_context ();
  Toplevel.loop (isar term no_pos);
  ml_prompts "ML> " "ML# ");

fun gen_main term no_pos =
 (Toplevel.set_state Toplevel.toplevel;
  writeln (Session.welcome ());
  gen_loop term no_pos);

structure Isar =
struct
  fun main () = gen_main false false;
  fun loop () = gen_loop false false;
  fun sync_main () = gen_main true true;
  fun sync_loop () = gen_loop true true;
end;


(*final declarations of this structure!*)
val command = parser false NONE;
val markup_command = parser false o SOME;
val improper_command = parser true NONE;

end;

(*setup theory syntax dependent operations*)
ThyLoad.deps_thy_fn := OuterSyntax.deps_thy;
ThyLoad.load_thy_fn := OuterSyntax.load_thy;
structure ThyLoad: THY_LOAD = ThyLoad;

structure BasicOuterSyntax: BASIC_OUTER_SYNTAX = OuterSyntax;
open BasicOuterSyntax;
open Isar;
