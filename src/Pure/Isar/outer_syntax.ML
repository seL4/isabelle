(*  Title:      Pure/Isar/outer_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.
*)

signature BASIC_OUTER_SYNTAX =
sig
  val main: unit -> unit
  val loop: unit -> unit
  val sync_main: unit -> unit
  val sync_loop: unit -> unit
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
      val thy_switch: string
      val thy_end: string
      val thy_heading: string
      val thy_decl: string
      val thy_goal: string
      val qed: string
      val qed_block: string
      val prf_goal: string
      val prf_block: string
      val prf_chain: string
      val prf_decl: string
      val prf_asm: string
      val prf_script: string
      val kinds: string list
    end
  type token
  type parser
  val command: string -> string -> string ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val improper_command: string -> string -> string ->
    (token list -> (Toplevel.transition -> Toplevel.transition) * token list) -> parser
  val dest_keywords: unit -> string list
  val dest_parsers: unit -> (string * string * string * bool) list
  val print_outer_syntax: unit -> unit
  val add_keywords: string list -> unit
  val add_parsers: parser list -> unit
  val theory_header: token list -> (string * string list * (string * bool) list) * token list
  val deps_thy: string -> Path.T -> string list * Path.T list
  val load_thy: string -> bool -> bool -> Path.T -> unit
  val isar: bool -> Toplevel.isar
end;

structure OuterSyntax: OUTER_SYNTAX =
struct

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
  val thy_goal = "theory-goal";
  val qed = "qed";
  val qed_block = "qed-block";
  val prf_goal = "proof-goal";
  val prf_block = "proof-block";
  val prf_chain = "proof-chain";
  val prf_decl = "proof-decl";
  val prf_asm = "proof-asm";
  val prf_script = "proof-script";

  val kinds = [control, diag, thy_begin, thy_switch, thy_end, thy_heading, thy_decl, thy_goal,
    qed, qed_block, prf_goal, prf_block, prf_chain, prf_decl, prf_asm, prf_script];
end;


(* parsers *)

type token = OuterLex.token;
type parser_fn = token list -> (Toplevel.transition -> Toplevel.transition) * token list;

datatype parser =
  Parser of string * (string * string) * bool * parser_fn;

fun parser int_only name comment kind parse = Parser (name, (comment, kind), int_only, parse);


(* parse command *)

local

fun command_body cmd (name, _) =
  (case cmd name of
    Some (int_only, parse) => P.!!! (Scan.prompt (name ^ "# ") (parse >> pair int_only))
  | None => sys_error ("no parser for outer syntax command " ^ quote name));

fun terminator false = Scan.succeed ()
  | terminator true = P.group "terminator" (Scan.option P.sync -- P.$$$ ";" >> K ());

in

fun command term cmd =
  P.$$$ ";" >> K None ||
  P.sync >> K None ||
  (P.position P.command :-- command_body cmd) --| terminator term
    >> (fn ((name, pos), (int_only, f)) =>
      Some (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
        Toplevel.interactive int_only |> f));

end;



(** global syntax state **)

local

val global_lexicons = ref (Scan.empty_lexicon, Scan.empty_lexicon);
val global_parsers = ref (Symtab.empty: ((string * string) * (bool * parser_fn)) Symtab.table);

fun change_lexicons f =
  let val lexs = f (! global_lexicons) in
    (case (op inter_string) (pairself Scan.dest_lexicon lexs) of
      [] => global_lexicons := lexs
    | bads => error ("Clash of outer syntax commands and keywords: " ^ commas_quote bads))
  end;

fun change_parsers f = global_parsers := f (! global_parsers);

in

(* get current lexers / parsers *)

(*Note: the syntax for files is statically determined at the very
  beginning; for interactive processing it may change dynamically.*)

fun get_lexicons () = ! global_lexicons;
fun get_parsers () = ! global_parsers;
fun get_parser () = apsome snd o curry Symtab.lookup (! global_parsers);


(* augment syntax *)

fun add_keywords keywords = change_lexicons (apfst (fn lex =>
  (Scan.extend_lexicon lex (map Symbol.explode keywords))));

fun add_parser (tab, Parser (name, comment, int_only, parse)) =
 (if is_none (Symtab.lookup (tab, name)) then ()
  else warning ("Redefined outer syntax command " ^ quote name);
  Symtab.update ((name, (comment, (int_only, parse))), tab));

fun add_parsers parsers =
  (change_parsers (fn tab => foldl add_parser (tab, parsers));
    change_lexicons (apsnd (fn lex => Scan.extend_lexicon lex
      (map (fn Parser (name, _, _, _) => Symbol.explode name) parsers))));

end;


(* print syntax *)

fun dest_keywords () = Scan.dest_lexicon (#1 (get_lexicons ()));

fun dest_parsers () =
  map (fn (name, ((cmt, kind), (int_only, _))) => (name, cmt, kind, int_only))
    (Symtab.dest (get_parsers ()));

fun print_outer_syntax () =
  let
    fun pretty_cmd (name, comment, _, _) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = partition #4 (dest_parsers ());
  in
    Pretty.writeln (Pretty.strs ("syntax keywords:" :: map quote (dest_keywords ())));
    Pretty.writeln (Pretty.big_list "proper commands:" (map pretty_cmd cmds));
    Pretty.writeln (Pretty.big_list "improper commands (interactive-only):"
      (map pretty_cmd int_cmds))
  end;



(** read theory **)

(* theory keyword *)

val theoryN = "theory";
val theory_keyword = OuterParse.$$$ theoryN;


(* source *)

local

val no_terminator =
  Scan.unless (P.$$$ ";") (Scan.one (OuterLex.not_sync andf OuterLex.not_eof));

val recover = Scan.prompt "recover# " (Scan.repeat no_terminator);

in

fun source term do_recover cmd src =
  src
  |> Source.source OuterLex.stopper
    (Scan.bulk (fn xs => OuterParse.!!! (command term (cmd ())) xs))
    (if do_recover then Some recover else None)
  |> Source.mapfilter I;

end;


(* detect header *)

fun scan_header get_lex scan (src, pos) =
  src
  |> Symbol.source false
  |> OuterLex.source false (fn () => (get_lex (), Scan.empty_lexicon)) pos
  |> Source.source OuterLex.stopper (Scan.single scan) None
  |> (fst o the o Source.get_single);

val check_header_lexicon = Scan.make_lexicon [Symbol.explode theoryN];

fun is_old_theory src =
  is_none (scan_header (K check_header_lexicon) (Scan.option theory_keyword) src);


(* deps_thy --- inspect theory header *)

val header_lexicon =
  Scan.make_lexicon (map Symbol.explode ["(", ")", "+", ":", "=", "files", theoryN]);

local

val file_name =
  (P.$$$ "(" |-- P.!!! (P.name --| P.$$$ ")")) >> rpair false || P.name >> rpair true;

val theory_head =
  (P.name -- (P.$$$ "=" |-- P.enum1 "+" P.name) --
    Scan.optional (P.$$$ "files" |-- P.!!! (Scan.repeat1 file_name)) [])
  >> (fn ((A, Bs), files) => (A, Bs, files));

in

val theory_header = theory_head --| (Scan.ahead P.eof || P.$$$ ":");
val only_header = theory_keyword |-- theory_head --| Scan.ahead P.eof;
val new_header = theory_keyword |-- P.!!! theory_header;

val old_header =
  P.name -- (P.$$$ "=" |-- P.name -- Scan.repeat (P.$$$ "+" |-- P.name))
  >> (fn (A, (B, Bs)) => (A, B :: Bs, []: (string * bool) list));

end;

fun deps_thy name path =
  let
    val src = File.source path;
    val (name', parents, files) =
      (*Note: old style headers dynamically depend on the current lexicon :-( *)
      if is_old_theory src then scan_header ThySyn.get_lexicon (Scan.error old_header) src
      else scan_header (K header_lexicon) (Scan.error new_header) src;

    val ml_path = ThyLoad.ml_path name;
    val ml_file = if is_none (ThyLoad.check_file ml_path) then [] else [ml_path];
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
    else Toplevel.excursion_error [Toplevel.empty |> Toplevel.name tr_name |> tr]
  end;

fun parse_thy (src, pos) =
  let
    val lex_src =
      src
      |> Symbol.source false
      |> OuterLex.source false (K (get_lexicons ())) pos;
    val only_head =
      lex_src
      |> Source.source OuterLex.stopper (Scan.single (Scan.option only_header)) None
      |> (fst o the o Source.get_single);
  in
    (case only_head of
      None =>
        lex_src
        |> source false false (K (get_parser ()))
        |> Source.exhaust
    | Some spec =>
        [Toplevel.empty |> Toplevel.name theoryN |> IsarThy.theory spec,
          Toplevel.empty |> Toplevel.name "end" |> Toplevel.exit])
  end;

fun run_thy name path =
  let val (src, pos) = File.source path in
    Present.theory_source name src;
    if is_old_theory (src, pos) then ThySyn.load_thy name (Source.exhaust src)
    else Toplevel.excursion_error (parse_thy (src, pos))
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

fun isar term =
  Source.tty
  |> Symbol.source true
  |> OuterLex.source true get_lexicons (Position.line_name 1 "stdin")
  |> source term true get_parser;



(** the read-eval-print loop **)

(* main loop *)

fun gen_loop term = (Context.reset_context (); Toplevel.loop (isar term));

fun gen_main term =
 (Toplevel.set_state Toplevel.toplevel;
  ml_prompts "ML> " "ML# ";
  writeln (Session.welcome ());
  gen_loop term);

fun main () = gen_main false;
fun loop () = gen_loop false;
fun sync_main () = gen_main true;
fun sync_loop () = gen_loop true;


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
