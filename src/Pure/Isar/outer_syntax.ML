(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.

TODO:
  - cleanup;
  - avoid string constants;
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
  structure Keyword:
    sig
      val control: string
      val diag: string
      val thy_begin: string
      val thy_end: string
      val thy_heading: string
      val thy_decl: string
      val thy_goal: string
      val qed: string
      val prf_goal: string
      val prf_block: string
      val prf_chain: string
      val prf_decl: string
      val prf_script: string
      val kinds: string list
    end
  type token
  type parser
  val command: string -> string -> string ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val improper_command: string -> string -> string ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val dest_syntax: unit -> string list * (string * string) list
  val print_outer_syntax: unit -> unit
  val add_keywords: string list -> unit
  val add_parsers: parser list -> unit
  val theory_header: token list -> (string * string list * (string * bool) list) * token list
  val deps_thy: string -> bool -> Path.T -> string list * Path.T list
  val load_thy: string -> bool -> bool -> Path.T -> unit
  val isar: Toplevel.isar
end;

structure OuterSyntax: OUTER_SYNTAX =
struct


(** outer syntax **)

(* command keyword classification *)

structure Keyword =
struct
  val control = "control";
  val diag = "diag";
  val thy_begin = "theory-begin";
  val thy_end = "theory-end";
  val thy_heading = "theory-heading";
  val thy_decl = "theory-decl";
  val thy_goal = "theory-goal";
  val qed = "qed";
  val prf_goal = "proof-goal";
  val prf_block = "proof-block";
  val prf_chain = "proof-chain";
  val prf_decl = "proof-decl";
  val prf_script = "proof-script";

  val kinds = [control, diag, thy_begin, thy_end, thy_heading, thy_decl, thy_goal, qed,
    prf_goal, prf_block, prf_chain, prf_decl, prf_script];
end;


(* parsers *)

type token = OuterLex.token;
type parser_fn = token list -> (Toplevel.transition -> Toplevel.transition) * token list;

datatype parser =
  Parser of string * (string * string) * bool * parser_fn;

fun parser int_only name comment kind parse = Parser (name, (comment, kind), int_only, parse);


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
val global_parsers = ref (Symtab.empty: ((string * string) * (bool * parser_fn)) Symtab.table);


(* print syntax *)

fun dest_syntax () =
  (map implode (Scan.dest_lexicon (! global_lexicon)),
    map (fn (name, ((_, kind), _)) => (name, kind)) (Symtab.dest (! global_parsers)));

fun print_outer_syntax () =
  let
    val keywords = map implode (Scan.dest_lexicon (! global_lexicon));
    fun pretty_cmd (name, ((comment, _), _)) =
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

(* theory keyword *)

val theoryN = "theory";
val theory_keyword = OuterParse.$$$ theoryN;


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

val check_header_lexicon = Scan.make_lexicon [Symbol.explode theoryN];

fun is_old_theory src =
  is_none (scan_header (K check_header_lexicon) (Scan.option theory_keyword) src);

fun warn_theory_style path is_old =
  let
    val style = if is_old then "old" else "new";
    val _ = warning ("Assuming " ^ style ^ "-style theory format for " ^ quote (Path.pack path));
  in is_old end;


(* deps_thy --- inspect theory header *)

val header_lexicon =
  Scan.make_lexicon (map Symbol.explode ["(", ")", "+", ":", "=", "files", theoryN]);

local open OuterParse in

val file_name = ($$$ "(" |-- !!! (name --| $$$ ")")) >> rpair false || name >> rpair true;

val theory_head =
  (name -- ($$$ "=" |-- enum1 "+" name) --
    Scan.optional ($$$ "files" |-- !!! (Scan.repeat1 file_name)) [])
  >> (fn ((A, Bs), files) => (A, Bs, files));

val theory_header = theory_head --| (Scan.ahead eof || $$$ ":");
val only_header = theory_keyword |-- theory_head --| Scan.ahead eof;
val new_header = theory_keyword |-- !!! theory_header;

val old_header =
  name -- ($$$ "=" |-- name -- Scan.repeat ($$$ "+" |-- name))
  >> (fn (A, (B, Bs)) => (A, B :: Bs, []: (string * bool) list));

end;

fun deps_thy name ml path =
  let
    val src = File.source path;
    val is_old = warn_theory_style path (is_old_theory src);
    val (name', parents, files) =
      (*Note: old style headers dynamically depend on the current lexicon :-( *)
      if is_old then scan_header ThySyn.get_lexicon (Scan.error old_header) src
      else scan_header (K header_lexicon) (Scan.error new_header) src;

    val ml_path = ThyLoad.ml_path name;
    val ml_file = if not ml orelse is_none (ThyLoad.check_file ml_path) then [] else [ml_path];
  in
    if name <> name' then
      error ("Filename " ^ quote (Path.pack path) ^ " does not match theory name " ^ quote name)
    else (parents, map (Path.unpack o #1) files @ ml_file)
  end;


(* load_thy --- read text (including header) *)

fun try_ml_file name ml time =
  let
    val path = ThyLoad.ml_path name;
    val tr = Toplevel.imperative (fn () => ThyInfo.load_file time path);
    val tr_name = if time then "time_use" else "use";
  in
    if not ml orelse is_none (ThyLoad.check_file path) then ()
    else Toplevel.excursion [Toplevel.empty |> Toplevel.name tr_name |> tr]
  end;

fun parse_thy (src, pos) =
  let
    val lex_src =
      src
      |> Symbol.source false
      |> OuterLex.source false (K (get_lexicon ())) pos;
    val only_head =
      lex_src
      |> Source.source OuterLex.stopper (Scan.single (Scan.option only_header)) None
      |> (fst o the o Source.get_single);
  in
    (case only_head of
      None =>
        lex_src
        |> source false (K (get_parser ()))
        |> Source.exhaust
    | Some spec =>
        [Toplevel.empty |> Toplevel.name theoryN |> IsarThy.theory spec,
          Toplevel.empty |> Toplevel.name "end" |> Toplevel.exit])
  end;

fun run_thy name path =
  let val (src, pos) = File.source path in
    Present.theory_source name src;
    if is_old_theory (src, pos) then ThySyn.load_thy name (Source.exhaust src)
    else (Toplevel.excursion (parse_thy (src, pos))
      handle exn => error (Toplevel.exn_message exn))
  end;

fun load_thy name ml time path =
 (if time then
    timeit (fn () =>
     (writeln ("\n**** Starting theory " ^ quote name ^ " ****");
      setmp Goals.proof_timing true (run_thy name) path;
      writeln ("**** Finished theory " ^ quote name ^ " ****\n")))
  else run_thy name path;
  Context.context (ThyInfo.get_theory name);
  try_ml_file name ml time);


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


(*final declarations of this structure!*)
val command = parser false;
val improper_command = parser true;


end;

(*setup theory syntax dependent operations*)
ThyLoad.deps_thy_fn := OuterSyntax.deps_thy;
ThyLoad.load_thy_fn := OuterSyntax.load_thy;
structure ThyLoad: THY_LOAD = ThyLoad;

structure BasicOuterSyntax: BASIC_OUTER_SYNTAX = OuterSyntax;
open BasicOuterSyntax;
