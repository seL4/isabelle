(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.

Note: the syntax for files is statically determined at the very
beginning; for interactive processing it may change dynamically.
*)

signature OUTER_SYNTAX =
sig
  type parser_fn = OuterLex.token list ->
    (Toplevel.transition -> Toplevel.transition) * OuterLex.token list
  val command: string -> string -> OuterKeyword.T -> parser_fn -> unit
  val markup_command: ThyOutput.markup -> string -> string -> OuterKeyword.T -> parser_fn -> unit
  val improper_command: string -> string -> OuterKeyword.T -> parser_fn -> unit
  val local_theory: string -> string -> OuterKeyword.T ->
    (OuterParse.token list -> (local_theory -> local_theory) * OuterLex.token list) -> unit
  val local_theory_to_proof': string -> string -> OuterKeyword.T ->
    (OuterParse.token list -> (bool -> local_theory -> Proof.state) * OuterLex.token list) -> unit
  val local_theory_to_proof: string -> string -> OuterKeyword.T ->
    (OuterParse.token list -> (local_theory -> Proof.state) * OuterLex.token list) -> unit
  val print_outer_syntax: unit -> unit
  val scan: string -> OuterLex.token list
  val parse: Position.T -> string -> Toplevel.transition list
  val prepare_command: Markup.property list -> string * Position.T -> Toplevel.transition
  val process_file: Path.T -> theory -> theory
  type isar
  val isar: bool -> isar
  val load_thy: Path.T -> string -> Position.T -> string list -> bool -> unit
end;

structure OuterSyntax: OUTER_SYNTAX =
struct

structure T = OuterLex;
structure P = OuterParse;


(** outer syntax **)

(* parsers *)

type parser_fn = T.token list -> (Toplevel.transition -> Toplevel.transition) * T.token list;

datatype parser = Parser of
 {comment: string,
  markup: ThyOutput.markup option,
  int_only: bool,
  parse: parser_fn};

fun make_parser comment markup int_only parse =
  Parser {comment = comment, markup = markup, int_only = int_only, parse = parse};


(* parse command *)

local

fun terminate false = Scan.succeed ()
  | terminate true = P.group "end of input" (Scan.option P.sync -- P.semicolon >> K ());

fun body cmd (name, _) =
  (case cmd name of
    SOME (Parser {int_only, parse, ...}) =>
      P.!!! (Scan.prompt (name ^ "# ") (P.tags |-- parse >> pair int_only))
  | NONE => sys_error ("no parser for outer syntax command " ^ quote name));

in

fun parse_command do_terminate cmd =
  P.semicolon >> K NONE ||
  P.sync >> K NONE ||
  (P.position P.command :-- body cmd) --| terminate do_terminate
    >> (fn ((name, pos), (int_only, f)) =>
      SOME (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
        Toplevel.interactive int_only |> f));

end;



(** global outer syntax **)

local

val global_parsers = ref (Symtab.empty: parser Symtab.table);
val global_markups = ref ([]: (string * ThyOutput.markup) list);

fun change_parsers f = CRITICAL (fn () =>
 (change global_parsers f;
  global_markups :=
    Symtab.fold (fn (name, Parser {markup = SOME m, ...}) => cons (name, m) | _ => I)
      (! global_parsers) []));

in

(* access current syntax *)

fun get_parsers () = CRITICAL (fn () => ! global_parsers);
fun get_markups () = CRITICAL (fn () => ! global_markups);

fun get_parser () = Symtab.lookup (get_parsers ());

fun is_markup kind name = AList.lookup (op =) (get_markups ()) name = SOME kind;


(* augment syntax *)

fun add_parser name kind parser = CRITICAL (fn () =>
 (OuterKeyword.command name kind;
  if not (Symtab.defined (get_parsers ()) name) then ()
  else warning ("Redefining outer syntax command " ^ quote name);
  change_parsers (Symtab.update (name, parser))));

fun command name comment kind parse =
  add_parser name kind (make_parser comment NONE false parse);

fun markup_command markup name comment kind parse =
  add_parser name kind (make_parser comment (SOME markup) false parse);

fun improper_command name comment kind parse =
  add_parser name kind (make_parser comment NONE true parse);

end;


(* local_theory commands *)

fun local_theory_command do_print trans name comment kind parse =
  command name comment kind (P.opt_target -- parse
    >> (fn (loc, f) => (if do_print then Toplevel.print else I) o trans loc f));

val local_theory           = local_theory_command false Toplevel.local_theory;
val local_theory_to_proof' = local_theory_command true Toplevel.local_theory_to_proof';
val local_theory_to_proof  = local_theory_command true Toplevel.local_theory_to_proof;


(* inspect syntax *)

fun dest_parsers () =
  get_parsers () |> Symtab.dest |> sort_wrt #1
  |> map (fn (name, Parser {comment, int_only, ...}) => (name, comment, int_only));

fun print_outer_syntax () =
  let
    fun pretty_cmd (name, comment, _) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = List.partition #3 (dest_parsers ());
  in
    [Pretty.strs ("syntax keywords:" :: map quote (OuterKeyword.dest_keywords ())),
      Pretty.big_list "commands:" (map pretty_cmd cmds),
      Pretty.big_list "interactive-only commands:" (map pretty_cmd int_cmds)]
    |> Pretty.chunks |> Pretty.writeln
  end;



(** toplevel parsing **)

(* basic sources *)

fun toplevel_source term do_recover cmd src =
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
        (Scan.bulk (fn xs => P.!!! (parse_command term (cmd ())) xs))
        (Option.map recover do_recover)
    |> Source.map_filter I
  end;


(* off-line scanning/parsing *)

fun scan str =
  Source.of_string str
  |> Symbol.source false
  |> T.source (SOME false) OuterKeyword.get_lexicons Position.none
  |> Source.exhaust;

fun parse pos str =
  Source.of_string str
  |> Symbol.source false
  |> T.source (SOME false) OuterKeyword.get_lexicons pos
  |> toplevel_source false NONE get_parser
  |> Source.exhaust;

fun prepare_command props (str, pos) =
  let val pos' = Position.of_properties (props |> Position.default_properties pos) in
    (case parse pos' str of
      [transition] => transition
    | _ => error "exactly one command expected")
  end;


(* process file *)

fun process_file path thy =
  let
    val result = ref thy;
    val trs = parse (Path.position path) (File.read path);
    val init = Toplevel.init_theory "" (K thy) (fn thy' => result := thy');
    val _ = Toplevel.excursion (init Toplevel.empty :: trs @ [Toplevel.exit Toplevel.empty]);
  in ! result end;


(* interactive source of toplevel transformers *)

type isar =
  (Toplevel.transition, (Toplevel.transition option,
    (OuterLex.token, (OuterLex.token option, (OuterLex.token, (OuterLex.token,
      Position.T * (Symbol.symbol, (string, unit) Source.source) Source.source)
          Source.source) Source.source) Source.source) Source.source) Source.source) Source.source;

fun isar term : isar =
  Source.tty
  |> Symbol.source true
  |> T.source (SOME true) OuterKeyword.get_lexicons Position.none
  |> toplevel_source term (SOME true) get_parser;


(* load_thy *)

fun load_thy dir name pos text time =
  let
    val text_src = Source.of_list (Library.untabify text);
    val (lexs, parser) = CRITICAL (fn () => (OuterKeyword.get_lexicons (), get_parser ()));

    val _ = Present.init_theory name;
    val _ = Present.verbatim_source name (fn () => Source.exhaust (Symbol.source false text_src));
    val toks = text_src
      |> Symbol.source false
      |> T.source NONE (K lexs) pos
      |> Source.exhausted;
    val trs = toks
      |> toplevel_source false NONE (K parser)
      |> Source.exhaust;

    val _ = if time then writeln ("\n**** Starting theory " ^ quote name ^ " ****") else ();
    val _ = cond_timeit time "" (fn () =>
      ThyOutput.process_thy (#1 lexs) OuterKeyword.command_tags is_markup trs toks
      |> Buffer.content
      |> Present.theory_output name);
    val _ = if time then writeln ("**** Finished theory " ^ quote name ^ " ****\n") else ();
  in () end;

end;

