(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.
*)

signature BASIC_OUTER_SYNTAX =
sig
  val main: unit -> unit
  val loop: unit -> unit
  val help: unit -> unit
end;

signature OUTER_SYNTAX =
sig
  include BASIC_OUTER_SYNTAX
  type token
  type parser
  val parser: bool -> string -> string ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val print_outer_syntax: unit -> unit
  val add_keywords: string list -> unit
  val add_parsers: parser list -> unit
  val get_header: Position.T -> (string, 'a) Source.source -> (bstring * bstring list) option
  val read_text: Position.T -> (string, 'a) Source.source -> Toplevel.transition list
  val read_file: string -> Toplevel.transition list
  val isar: Toplevel.isar
end;

structure OuterSyntax: OUTER_SYNTAX =
struct

open OuterParse;


(** outer syntax **)

(* parsers *)

type token = OuterLex.token;
type parser_fn = token list -> (Toplevel.transition -> Toplevel.transition) * token list;

datatype parser =
  Parser of string * string * bool * parser_fn;

fun parser int_only name comment parse = Parser (name, comment, int_only, parse);


(* parse command *)

fun command_name cmd =
  group "command"
    (position (Scan.one (OuterLex.keyword_pred (is_some o cmd)) >> OuterLex.val_of));

fun command_body cmd (name, _) =
  let val (int_only, parse) = the (cmd name)
  in !!! (Scan.prompt (name ^ "# ") (parse >> pair int_only)) end;

fun command cmd =
  $$$ ";" >> K None ||
  command_name cmd :-- command_body cmd >> (fn ((name, pos), (int_only, f)) =>
    Some (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
      Toplevel.interactive int_only |> f));



(** global syntax state **)

val global_lexicon = ref Scan.empty_lexicon;
val global_parsers = ref (Symtab.empty: (string * (bool * parser_fn)) Symtab.table);


(* print syntax *)

fun print_outer_syntax () =
  let
    val keywords = map implode (Scan.dest_lexicon (! global_lexicon));
    fun pretty_cmd (name, (comment, _)) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = partition (#1 o #2 o #2) (Symtab.dest (! global_parsers));
  in
    Pretty.writeln (Pretty.strs ("keywords:" :: map quote keywords));
    Pretty.writeln (Pretty.big_list "general commands:" (map pretty_cmd cmds));
    Pretty.writeln (Pretty.big_list "interactive commands:" (map pretty_cmd int_cmds))
  end;


(* augment syntax *)

fun add_keywords keywords =
  global_lexicon := Scan.extend_lexicon (! global_lexicon) (map Symbol.explode keywords);

fun add_parser (tab, Parser (name, comment, int_only, parse)) =
 (if is_none (Symtab.lookup (tab, name)) then ()
  else warning ("Redefined outer syntax command " ^ quote name);
  Symtab.update ((name, (comment, (int_only, parse))), tab));

fun add_parsers parsers =
  (global_parsers := foldl add_parser (! global_parsers, parsers);
    add_keywords (map (fn Parser (name, _, _, _) => name) parsers));


(* get current lexer / parser *)

(*Note: the syntax for files is statically determined at the very
  beginning; for interactive processing it may change dynamically.*)

fun get_lexicon () = ! global_lexicon;
fun get_parser () = apsome snd o curry Symtab.lookup (! global_parsers);



(** read theory **)

(* source *)

fun no_command cmd =
  Scan.one ((not o OuterLex.keyword_pred ((is_some o cmd) orf equal ";")) andf OuterLex.not_eof);

fun recover cmd =
  Scan.prompt "recover# " (Scan.one OuterLex.not_eof -- Scan.repeat (no_command cmd));

fun source do_recover cmd src =
  src
  |> Source.source OuterLex.stopper (Scan.bulk (fn xs => !!! (command (cmd ())) xs))
    (if do_recover then Some (fn xs => recover (cmd ()) xs) else None)
  |> Source.mapfilter I;


(* detect header *)

val head_lexicon =
  Scan.make_lexicon (map Symbol.explode ["+", ":", "=", "theory"]);

val head_parser =
  $$$ "theory" |-- !!! (name -- ($$$ "=" |-- enum "+" name --| (Scan.ahead eof || $$$ ":")));

fun get_header pos src =
  src
  |> Symbol.source false
  |> OuterLex.source false (K head_lexicon) pos
  |> Source.source OuterLex.stopper (Scan.single (Scan.option head_parser)) None
  |> (fst o the o Source.get_single);


(* read text (including header) *)

fun read_text pos src =
  src
  |> Symbol.source false
  |> OuterLex.source false (K (get_lexicon ())) pos
  |> source false (K (get_parser ()))
  |> Source.exhaust;

fun read_file name = read_text (Position.line_name 1 (quote name)) (Source.of_file name);


(* interactive source of state transformers *)

val isar =
  Source.tty
  |> Symbol.source true
  |> OuterLex.source true get_lexicon (Position.line_name 1 "stdin")
  |> source true get_parser;



(** the read-eval-print loop **)

fun loop () = (Context.reset_context (); Toplevel.loop isar);

fun main () =
 (Toplevel.set_state Toplevel.toplevel;
  ml_prompts "ML> " "ML# ";
  writeln ("\n\n" ^ Context.welcome ());
  loop ());


(* help *)

fun help () =
  writeln ("This is Isabelle's underlying ML system (" ^ ml_system ^ ");\n\
    \invoke 'loop();' to enter the Isar loop.");


end;


structure BasicOuterSyntax: BASIC_OUTER_SYNTAX = OuterSyntax;
open BasicOuterSyntax;
