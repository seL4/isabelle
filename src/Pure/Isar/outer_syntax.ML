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
  val commands: unit -> string list
  val add_keywords: string list -> unit
  val add_parsers: parser list -> unit
  val deps_thy: string -> bool -> Path.T -> string list * Path.T list
  val load_thy: string -> bool -> bool -> Path.T -> unit
  val isar: Toplevel.isar
end;

structure OuterSyntax: OUTER_SYNTAX =
struct


(** outer syntax **)

(* parsers *)

type token = OuterLex.token;
type parser_fn = token list -> (Toplevel.transition -> Toplevel.transition) * token list;

datatype parser =
  Parser of string * string * bool * parser_fn;

fun parser int_only name comment parse = Parser (name, comment, int_only, parse);


(* parse command *)

local open OuterParse in

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

end;



(** global syntax state **)

val global_lexicon = ref Scan.empty_lexicon;
val global_parsers = ref (Symtab.empty: (string * (bool * parser_fn)) Symtab.table);

fun commands () = Symtab.keys (! global_parsers);


(* print syntax *)

fun print_outer_syntax () =
  let
    val keywords = map implode (Scan.dest_lexicon (! global_lexicon));
    fun pretty_cmd (name, (comment, _)) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = partition (#1 o #2 o #2) (Symtab.dest (! global_parsers));
  in
    Pretty.writeln (Pretty.strs ("syntax keywords:" :: map quote keywords));
    Pretty.writeln (Pretty.big_list "proper commands:" (map pretty_cmd cmds));
    Pretty.writeln (Pretty.big_list "improper commands (interactive-only):"
      (map pretty_cmd int_cmds))
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
  |> Source.source OuterLex.stopper (Scan.bulk (fn xs => OuterParse.!!! (command (cmd ())) xs))
    (if do_recover then Some (fn xs => recover (cmd ()) xs) else None)
  |> Source.mapfilter I;


(* detect header *)

fun scan_header get_lexicon scan (src, pos) =
  src
  |> Symbol.source false
  |> OuterLex.source false get_lexicon pos
  |> Source.source OuterLex.stopper (Scan.single scan) None
  |> (fst o the o Source.get_single);

val check_header_lexicon = Scan.make_lexicon [Symbol.explode "theory"];

fun is_old_theory src =
  is_none (scan_header (K check_header_lexicon) (Scan.option (OuterParse.$$$ "theory")) src);

fun warn_theory_style path is_old =
  let
    val style = if is_old then "old" else "new";
    val _ = warning ("Assuming " ^ style ^ "-style theory format for " ^ quote (Path.pack path));
  in is_old end;


(* deps_thy --- inspect theory header *)

val new_header_lexicon =
  Scan.make_lexicon (map Symbol.explode ["+", ":", "=", "files", "theory"]);

local open OuterParse in

val new_header =
  $$$ "theory" |-- !!! (name -- ($$$ "=" |-- enum1 "+" name) --
    Scan.optional ($$$ "files" |-- !!! (Scan.repeat1 name)) [] --| (Scan.ahead eof || $$$ ":"));

val old_header =
  name -- ($$$ "=" |-- name -- Scan.repeat ($$$ "+" |-- name))
  >> (fn (A, (B, Bs)) => ((A, B :: Bs), []));

end;

fun deps_thy name ml path =
  let
    val src = Source.of_file path;
    val is_old = warn_theory_style path (is_old_theory src);
    val ((name', parents), files) =
      (*Note: old style headers dynamically depend on the current lexicon :-( *)
      if is_old then scan_header ThySyn.get_lexicon (Scan.error old_header) src
      else scan_header (K new_header_lexicon) (Scan.error new_header) src;

    val ml_path = ThyLoad.ml_path name;
    val ml_file = if not ml orelse is_none (ThyLoad.check_file ml_path) then [] else [ml_path];
  in
    if name <> name' then
      error ("Filename " ^ quote (Path.pack path) ^ " does not match theory name " ^ quote name)
    else (parents, map Path.unpack files @ ml_file)
  end;


(* load_thy --- read text (including header) *)

fun try_ml_file name ml =
  let
    val path = ThyLoad.ml_path name;
    val tr = Toplevel.imperative (fn () => ThyInfo.load_file path);
  in
    if not ml orelse is_none (ThyLoad.check_file path) then ()
    else Toplevel.excursion [Toplevel.empty |> Toplevel.name "use" |> tr]
  end;

fun parse_thy (src, pos) =
  src
  |> Symbol.source false
  |> OuterLex.source false (K (get_lexicon ())) pos
  |> source false (K (get_parser ()))
  |> Source.exhaust;

fun read_thy name ml path =
  let
    val (src, pos) = Source.of_file path;
    val _ =
      if is_old_theory (src, pos) then ThySyn.load_thy name (Source.exhaust src)
      else (Toplevel.excursion (parse_thy (src, pos))
        handle exn => error (Toplevel.exn_message exn));
    val theory = ThyInfo.get_theory name;
  in Context.setmp theory try_ml_file name ml end;

fun load_thy name ml time path =
  if not time then read_thy name ml path
  else timeit (fn () =>
   (writeln ("\n**** Starting Theory " ^ quote name ^ " ****");
    setmp Goals.proof_timing true (read_thy name ml) path;
    writeln ("**** Finished Theory " ^ quote name ^ " ****\n")));


(* interactive source of state transformers *)

val isar =
  Source.tty
  |> Symbol.source true
  |> OuterLex.source true get_lexicon (Position.line_name 1 "stdin")
  |> source true get_parser;



(** the read-eval-print loop **)

(* main loop *)

fun loop () = (Context.reset_context (); Toplevel.loop isar);

fun main () =
 (Toplevel.set_state Toplevel.toplevel;
  ml_prompts "ML> " "ML# ";
  writeln (Session.welcome ());
  loop ());


(* help *)

fun help () =
  writeln ("This is Isabelle's underlying ML system (" ^ ml_system ^ ");\n\
    \invoke 'loop();' to enter the Isar loop.");


end;

(*setup theory syntax dependent operations*)
ThyLoad.deps_thy_fn := OuterSyntax.deps_thy;
ThyLoad.load_thy_fn := OuterSyntax.load_thy;
structure ThyLoad: THY_LOAD = ThyLoad;

structure BasicOuterSyntax: BASIC_OUTER_SYNTAX = OuterSyntax;
open BasicOuterSyntax;
