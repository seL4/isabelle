(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The global Isabelle/Isar outer syntax.
*)

signature BASIC_OUTER_SYNTAX =
sig
  val main: unit -> unit
  val loop: unit -> unit
  val sync_main: unit -> unit
  val sync_loop: unit -> unit
end;

signature OUTER_SYNTAX =
sig
  include BASIC_OUTER_SYNTAX
  structure Keyword:
    sig
      val control: string
      val diag: string
      val thy_begin: string
      val thy_switch: string
      val thy_end: string
      val thy_heading: string
      val thy_decl: string
      val thy_script: string
      val thy_goal: string
      val qed: string
      val qed_block: string
      val qed_global: string
      val prf_heading: string
      val prf_goal: string
      val prf_block: string
      val prf_open: string
      val prf_close: string
      val prf_chain: string
      val prf_decl: string
      val prf_asm: string
      val prf_asm_goal: string
      val prf_script: string
      val kinds: string list
    end
  type token
  type parser
  val command: string -> string -> string ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val markup_command: IsarOutput.markup -> string -> string -> string ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val improper_command: string -> string -> string ->
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
  val isar_readstring: Position.T -> string -> (string list) Toplevel.isar
  val read: string -> (string * OuterLex.token list * Toplevel.transition) list
end;

structure OuterSyntax: OUTER_SYNTAX =
struct

structure T = OuterLex;
structure P = OuterParse;


(** outer syntax **)

(* command keyword classification *)

structure Keyword =
struct
  val control = "control";
  val diag = "diag";
  val thy_begin = "theory-begin";
  val thy_switch = "theory-switch";
  val thy_end = "theory-end";
  val thy_heading = "theory-heading";
  val thy_decl = "theory-decl";
  val thy_script = "theory-script";
  val thy_goal = "theory-goal";
  val qed = "qed";
  val qed_block = "qed-block";
  val qed_global = "qed-global";
  val prf_heading = "proof-heading";
  val prf_goal = "proof-goal";
  val prf_block = "proof-block";
  val prf_open = "proof-open";
  val prf_close = "proof-close";
  val prf_chain = "proof-chain";
  val prf_decl = "proof-decl";
  val prf_asm = "proof-asm";
  val prf_asm_goal = "proof-asm-goal";
  val prf_script = "proof-script";

  val kinds = [control, diag, thy_begin, thy_switch, thy_end, thy_heading, thy_decl, thy_script,
    thy_goal, qed, qed_block, qed_global, prf_heading, prf_goal, prf_block, prf_open, prf_close,
    prf_chain, prf_decl, prf_asm, prf_asm_goal, prf_script];
end;


(* parsers *)

type token = T.token;
type parser_fn = token list -> (Toplevel.transition -> Toplevel.transition) * token list;

datatype parser =
  Parser of string * (string * string * IsarOutput.markup option) * bool * parser_fn;

fun parser int_only markup name comment kind parse =
  Parser (name, (comment, kind, markup), int_only, parse);


(* parse command *)

local

fun terminate false = Scan.succeed ()
  | terminate true = P.group "end of input" (Scan.option P.sync -- P.semicolon >> K ());

fun trace false parse = parse
  | trace true parse = Scan.trace parse >> (fn (f, toks) => f o Toplevel.source toks);

fun body cmd trc (name, _) =
  (case cmd name of
    Some (int_only, parse) =>
      P.!!! (Scan.prompt (name ^ "# ") (trace trc parse >> pair int_only))
  | None => sys_error ("no parser for outer syntax command " ^ quote name));

in

fun command do_terminate do_trace cmd =
  P.semicolon >> K None ||
  P.sync >> K None ||
  (P.position P.command :-- body cmd do_trace) --| terminate do_terminate
    >> (fn ((name, pos), (int_only, f)) =>
      Some (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
        Toplevel.interactive int_only |> f));

end;



(** global outer syntax **)

local

val global_lexicons = ref (Scan.empty_lexicon, Scan.empty_lexicon);
val global_parsers =
  ref (Symtab.empty: (((string * string) * (bool * parser_fn)) * IsarOutput.markup option)
    Symtab.table);
val global_markups = ref ([]: (string * IsarOutput.markup) list);

fun change_lexicons f =
  let val lexs = f (! global_lexicons) in
    (case (op inter_string) (pairself Scan.dest_lexicon lexs) of
      [] => global_lexicons := lexs
    | bads => error ("Clash of outer syntax commands and keywords: " ^ commas_quote bads))
  end;

fun get_markup (ms, (name, (_, Some m))) = (name, m) :: ms
  | get_markup (ms, _) = ms;

fun make_markups () = global_markups := Symtab.foldl get_markup ([], ! global_parsers);
fun change_parsers f = (Library.change global_parsers f; make_markups ());

in


(* access current syntax *)

(*Note: the syntax for files is statically determined at the very
  beginning; for interactive processing it may change dynamically.*)

fun get_lexicons () = ! global_lexicons;
fun get_parsers () = ! global_parsers;
fun get_parser () = apsome (#2 o #1) o curry Symtab.lookup (! global_parsers);

fun is_markup kind name =
  (case assoc (! global_markups, name) of Some k => k = kind | None => false);
fun markup kind = Scan.one (T.is_kind T.Command andf is_markup kind o T.val_of);


(* augment syntax *)

fun add_keywords keywords = change_lexicons (apfst (fn lex =>
  (Scan.extend_lexicon lex (map Symbol.explode keywords))));

fun add_parser (tab, Parser (name, (comment, kind, markup), int_only, parse)) =
 (if is_none (Symtab.lookup (tab, name)) then ()
  else warning ("Redefined outer syntax command " ^ quote name);
  Symtab.update ((name, (((comment, kind), (int_only, parse)), markup)), tab));

fun add_parsers parsers =
  (change_parsers (fn tab => foldl add_parser (tab, parsers));
    change_lexicons (apsnd (fn lex => Scan.extend_lexicon lex
      (map (fn Parser (name, _, _, _) => Symbol.explode name) parsers))));

end;


(* print syntax *)

fun is_keyword s = Scan.is_literal (#1 (get_lexicons ())) (Symbol.explode s);
fun dest_keywords () = Scan.dest_lexicon (#1 (get_lexicons ()));

fun dest_parsers () =
  map (fn (name, (((cmt, kind), (int_only, _)), _)) => (name, cmt, kind, int_only))
    (Symtab.dest (get_parsers ()));

fun print_outer_syntax () =
  let
    fun pretty_cmd (name, comment, _, _) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = partition #4 (dest_parsers ());
  in
    [Pretty.strs ("syntax keywords:" :: map quote (dest_keywords ())),
      Pretty.big_list "proper commands:" (map pretty_cmd cmds),
      Pretty.big_list "improper commands (interactive-only):" (map pretty_cmd int_cmds)]
    |> Pretty.chunks |> Pretty.writeln
  end;

val print_commands = Toplevel.imperative print_outer_syntax;



(** toplevel parsing **)

(* basic sources *)

fun toplevel_source term trc do_recover cmd src =
  let
    val no_terminator =
      Scan.unless P.semicolon (Scan.one (T.not_sync andf T.not_eof));
    fun recover x = (Scan.prompt "recover# " (Scan.repeat no_terminator) >> K [None]) x;
  in
    src
    |> T.source_proper
    |> Source.source T.stopper
      (Scan.bulk (P.$$$ "--" -- P.!!! P.text >> K None || P.not_eof >> Some))
      (if do_recover then Some recover else None)
    |> Source.mapfilter I
    |> Source.source T.stopper (Scan.bulk (fn xs => P.!!! (command term trc (cmd ())) xs))
      (if do_recover then Some recover else None)
    |> Source.mapfilter I
  end;


(* interactive source of toplevel transformers *)

fun isar term no_pos =
  Source.tty
  |> Symbol.source true
  |> T.source true get_lexicons
    (if no_pos then Position.none else Position.line_name 1 "stdin")
  |> toplevel_source term false true get_parser;


(* string source of transformers with trace (for Proof General) *)

fun isar_readstring pos str =
  Source.of_string str
  |> Symbol.source false
  |> T.source false get_lexicons pos
  |> toplevel_source false true true get_parser;


(* read text -- with trace of source *)

fun read str =
  Source.of_string str
  |> Symbol.source false
  |> T.source false get_lexicons Position.none
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
    val ml_file = if ml andalso is_some (ThyLoad.check_file ml_path) then [ml_path] else [];
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
    if is_none (ThyLoad.check_file path) then ()
    else Toplevel.excursion [Toplevel.empty |> Toplevel.name tr_name |> tr]
  end;

fun parse_thy src =
  src
  |> toplevel_source false false false (K (get_parser ()))
  |> Source.exhaust;

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
        val out = Toplevel.excursion_result
          (IsarOutput.parse_thy markup (#1 (get_lexicons ()))
            (parse_thy tok_src) tok_src);
      in Present.theory_output name (Buffer.content out) end
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
  Toplevel.loop (isar term no_pos));

fun gen_main term no_pos =
 (Toplevel.set_state Toplevel.toplevel;
  writeln (Session.welcome ());
  gen_loop term no_pos);

fun main () = gen_main false false;
fun loop () = gen_loop false false;
fun sync_main () = gen_main true true;
fun sync_loop () = gen_loop true true;


(*final declarations of this structure!*)
val command = parser false None;
val markup_command = parser false o Some;
val improper_command = parser true None;


end;

(*setup theory syntax dependent operations*)
ThyLoad.deps_thy_fn := OuterSyntax.deps_thy;
ThyLoad.load_thy_fn := OuterSyntax.load_thy;
structure ThyLoad: THY_LOAD = ThyLoad;

structure BasicOuterSyntax: BASIC_OUTER_SYNTAX = OuterSyntax;
open BasicOuterSyntax;
