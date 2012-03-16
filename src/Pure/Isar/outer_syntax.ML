(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.

Note: the syntax for files is statically determined at the very
beginning; for interactive processing it may change dynamically.
*)

signature OUTER_SYNTAX =
sig
  type outer_syntax
  val is_markup: outer_syntax -> Thy_Output.markup -> string -> bool
  val get_syntax: unit -> (Scan.lexicon * Scan.lexicon) * outer_syntax
  val command: string -> string -> Keyword.T ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val markup_command: Thy_Output.markup -> string -> string -> Keyword.T ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val improper_command: string -> string -> Keyword.T ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val internal_command: string ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val local_theory': string -> string -> Keyword.T ->
    (bool -> local_theory -> local_theory) parser -> unit
  val local_theory: string -> string -> Keyword.T ->
    (local_theory -> local_theory) parser -> unit
  val local_theory_to_proof': string -> string -> Keyword.T ->
    (bool -> local_theory -> Proof.state) parser -> unit
  val local_theory_to_proof: string -> string -> Keyword.T ->
    (local_theory -> Proof.state) parser -> unit
  val print_outer_syntax: unit -> unit
  val scan: Position.T -> string -> Token.T list
  val parse: Position.T -> string -> Toplevel.transition list
  val process_file: Path.T -> theory -> theory
  type isar
  val isar: TextIO.instream -> bool -> isar
  val read_span: outer_syntax -> Token.T list -> Toplevel.transition * bool
  val read_element: outer_syntax -> (unit -> theory) -> Thy_Syntax.element ->
    (Toplevel.transition * Toplevel.transition list) list
end;

structure Outer_Syntax: OUTER_SYNTAX =
struct

(** outer syntax **)

(* command parsers *)

datatype command = Command of
 {comment: string,
  markup: Thy_Output.markup option,
  int_only: bool,
  parse: (Toplevel.transition -> Toplevel.transition) parser};

fun make_command comment markup int_only parse =
  Command {comment = comment, markup = markup, int_only = int_only, parse = parse};


(* parse command *)

local

fun terminate false = Scan.succeed ()
  | terminate true =
      Parse.group (fn () => "end of input")
        (Scan.option Parse.sync -- Parse.semicolon >> K ());

fun body cmd (name, _) =
  (case cmd name of
    SOME (Command {int_only, parse, ...}) =>
      Parse.!!! (Scan.prompt (name ^ "# ") (Parse.tags |-- parse >> pair int_only))
  | NONE => raise Fail ("No parser for outer syntax command " ^ quote name));

in

fun parse_command do_terminate cmd =
  Parse.semicolon >> K NONE ||
  Parse.sync >> K NONE ||
  (Parse.position Parse.command :-- body cmd) --| terminate do_terminate
    >> (fn ((name, pos), (int_only, f)) =>
      SOME (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
        Toplevel.interactive int_only |> f));

end;


(* type outer_syntax *)

datatype outer_syntax = Outer_Syntax of
 {commands: command Symtab.table,
  markups: (string * Thy_Output.markup) list};

fun make_outer_syntax commands markups =
  Outer_Syntax {commands = commands, markups = markups};

val empty_outer_syntax = make_outer_syntax Symtab.empty [];


fun map_commands f (Outer_Syntax {commands, ...}) =
  let
    val commands' = f commands;
    val markups' =
      Symtab.fold (fn (name, Command {markup = SOME m, ...}) => cons (name, m) | _ => I)
        commands' [];
  in make_outer_syntax commands' markups' end;

fun dest_commands (Outer_Syntax {commands, ...}) =
  commands |> Symtab.dest |> sort_wrt #1
  |> map (fn (name, Command {comment, int_only, ...}) => (name, comment, int_only));

fun lookup_commands (Outer_Syntax {commands, ...}) = Symtab.lookup commands;

fun is_markup (Outer_Syntax {markups, ...}) kind name =
  AList.lookup (op =) markups name = SOME kind;



(** global outer syntax **)

local

(*synchronized wrt. Keywords*)
val global_outer_syntax = Unsynchronized.ref empty_outer_syntax;

fun add_command name kind cmd = CRITICAL (fn () =>
  let
    val thy = ML_Context.the_global_context ();
    val _ =
      (case try (Thy_Header.the_keyword thy) name of
        SOME k =>
          if k = SOME kind then ()
          else error ("Inconsistent outer syntax keyword declaration " ^ quote name)
      | NONE =>
          if Context.theory_name thy = Context.PureN then Keyword.declare name (SOME kind)
          else error ("Undeclared outer syntax command " ^ quote name));
  in
    Unsynchronized.change global_outer_syntax (map_commands (fn commands =>
     (if not (Symtab.defined commands name) then ()
      else warning ("Redefining outer syntax command " ^ quote name);
      Symtab.update (name, cmd) commands)))
  end);

in

fun get_syntax () = CRITICAL (fn () => (Keyword.get_lexicons (), ! global_outer_syntax));

fun lookup_commands_dynamic () = lookup_commands (! global_outer_syntax);

fun command name comment kind parse =
  add_command name kind (make_command comment NONE false parse);

fun markup_command markup name comment kind parse =
  add_command name kind (make_command comment (SOME markup) false parse);

fun improper_command name comment kind parse =
  add_command name kind (make_command comment NONE true parse);

fun internal_command name parse =
  command name "(internal)" Keyword.control (parse >> (fn tr => Toplevel.no_timing o tr));

end;


(* local_theory commands *)

fun local_theory_command do_print trans name comment kind parse =
  command name comment kind (Parse.opt_target -- parse
    >> (fn (loc, f) => (if do_print then Toplevel.print else I) o trans loc f));

val local_theory' = local_theory_command false Toplevel.local_theory';
val local_theory = local_theory_command false Toplevel.local_theory;
val local_theory_to_proof' = local_theory_command true Toplevel.local_theory_to_proof';
val local_theory_to_proof = local_theory_command true Toplevel.local_theory_to_proof;


(* inspect syntax *)

fun print_outer_syntax () =
  let
    val ((keywords, _), outer_syntax) =
      CRITICAL (fn () => (Keyword.dest (), #2 (get_syntax ())));
    fun pretty_cmd (name, comment, _) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = List.partition #3 (dest_commands outer_syntax);
  in
    [Pretty.strs ("syntax keywords:" :: map quote keywords),
      Pretty.big_list "commands:" (map pretty_cmd cmds),
      Pretty.big_list "interactive-only commands:" (map pretty_cmd int_cmds)]
    |> Pretty.chunks |> Pretty.writeln
  end;



(** toplevel parsing **)

(* basic sources *)

fun toplevel_source term do_recover cmd src =
  let
    val no_terminator =
      Scan.unless Parse.semicolon (Scan.one (Token.not_sync andf Token.not_eof));
    fun recover int =
      (int, fn _ => Scan.prompt "recover# " (Scan.repeat no_terminator) >> K [NONE]);
  in
    src
    |> Token.source_proper
    |> Source.source Token.stopper
      (Scan.bulk (Parse.$$$ "--" -- Parse.!!! Parse.doc_source >> K NONE || Parse.not_eof >> SOME))
        (Option.map recover do_recover)
    |> Source.map_filter I
    |> Source.source Token.stopper
        (Scan.bulk (fn xs => Parse.!!! (parse_command term (cmd ())) xs))
        (Option.map recover do_recover)
    |> Source.map_filter I
  end;


(* off-line scanning/parsing *)

fun scan pos str =
  Source.of_string str
  |> Symbol.source
  |> Token.source {do_recover = SOME false} Keyword.get_lexicons pos
  |> Source.exhaust;

fun parse pos str =
  Source.of_string str
  |> Symbol.source
  |> Token.source {do_recover = SOME false} Keyword.get_lexicons pos
  |> toplevel_source false NONE lookup_commands_dynamic
  |> Source.exhaust;


(* process file *)

fun process_file path thy =
  let
    val trs = parse (Path.position path) (File.read path);
    val init = Toplevel.init_theory (K thy) Toplevel.empty;
    val result = fold Toplevel.command (init :: trs) Toplevel.toplevel;
  in
    (case (Toplevel.is_theory result, Toplevel.generic_theory_of result) of
      (true, Context.Theory thy') => thy'
    | _ => error "Bad result state: global theory expected")
  end;


(* interactive source of toplevel transformers *)

type isar =
  (Toplevel.transition, (Toplevel.transition option,
    (Token.T, (Token.T option, (Token.T, (Token.T,
      (Symbol_Pos.T, Position.T * (Symbol.symbol, (string, unit) Source.source)
  Source.source) Source.source) Source.source) Source.source)
  Source.source) Source.source) Source.source) Source.source;

fun isar in_stream term : isar =
  Source.tty in_stream
  |> Symbol.source
  |> Token.source {do_recover = SOME true} Keyword.get_lexicons Position.none
  |> toplevel_source term (SOME true) lookup_commands_dynamic;


(* read toplevel commands -- fail-safe *)

val not_singleton = "Exactly one command expected";

fun read_span outer_syntax toks =
  let
    val commands = lookup_commands outer_syntax;
    val range_pos = Position.set_range (Token.range toks);
    val _ = Position.reports (maps Thy_Syntax.reports_of_token toks);
  in
    (case Source.exhaust (toplevel_source false NONE (K commands) (Source.of_list toks)) of
      [tr] =>
        if Keyword.is_control (Toplevel.name_of tr) then
          (Toplevel.malformed (Toplevel.pos_of tr) "Illegal control command", true)
        else (tr, true)
    | [] => (Toplevel.ignored range_pos, false)
    | _ => (Toplevel.malformed range_pos not_singleton, true))
    handle ERROR msg => (Toplevel.malformed range_pos msg, true)
  end;

fun read_element outer_syntax init {head, proof, proper_proof} =
  let
    val read = read_span outer_syntax o Thy_Syntax.span_content;
    val (tr, proper_head) = read head |>> Toplevel.modify_init init;
    val proof_trs = map read proof |> filter #2 |> map #1;
  in
    if proper_head andalso proper_proof then [(tr, proof_trs)]
    else map (rpair []) (if proper_head then tr :: proof_trs else proof_trs)
  end;

end;

