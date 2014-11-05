(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.

Note: the syntax for files is statically determined at the very
beginning; for interactive processing it may change dynamically.
*)

signature OUTER_SYNTAX =
sig
  type syntax
  val batch_mode: bool Unsynchronized.ref
  val is_markup: syntax -> Thy_Output.markup -> string -> bool
  val get_syntax: unit -> Keyword.keywords * syntax
  val check_syntax: unit -> unit
  type command_spec = (string * Keyword.T) * Position.T
  val command: command_spec -> string ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val markup_command: Thy_Output.markup -> command_spec -> string ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val local_theory': command_spec -> string ->
    (bool -> local_theory -> local_theory) parser -> unit
  val local_theory: command_spec -> string ->
    (local_theory -> local_theory) parser -> unit
  val local_theory_to_proof': command_spec -> string ->
    (bool -> local_theory -> Proof.state) parser -> unit
  val local_theory_to_proof: command_spec -> string ->
    (local_theory -> Proof.state) parser -> unit
  val help_syntax: string list -> unit
  val print_syntax: unit -> unit
  val scan: Keyword.keywords -> Position.T -> string -> Token.T list
  val parse: Keyword.keywords * syntax -> Position.T -> string -> Toplevel.transition list
  val parse_spans: Token.T list -> Command_Span.span list
  val side_comments: Token.T list -> Token.T list
  val command_reports: syntax -> Token.T -> Position.report_text list
  val read_spans: syntax -> Token.T list -> Toplevel.transition list
end;

structure Outer_Syntax: OUTER_SYNTAX =
struct

(** outer syntax **)

(* command parsers *)

datatype command = Command of
 {comment: string,
  markup: Thy_Output.markup option,
  parse: (Toplevel.transition -> Toplevel.transition) parser,
  pos: Position.T,
  id: serial};

fun new_command comment markup parse pos =
  Command {comment = comment, markup = markup, parse = parse, pos = pos, id = serial ()};

fun command_markup def (name, Command {pos, id, ...}) =
  Markup.properties (Position.entity_properties_of def id pos)
    (Markup.entity Markup.commandN name);

fun pretty_command (cmd as (name, Command {comment, ...})) =
  Pretty.block
    (Pretty.marks_str
      ([Active.make_markup Markup.sendbackN {implicit = true, properties = [Markup.padding_line]},
        command_markup false cmd], name) :: Pretty.str ":" :: Pretty.brk 2 :: Pretty.text comment);


(* type syntax *)

datatype syntax = Syntax of
 {commands: command Symtab.table,
  markups: (string * Thy_Output.markup) list};

fun make_syntax commands markups =
  Syntax {commands = commands, markups = markups};

val empty_syntax = make_syntax Symtab.empty [];


fun map_commands f (Syntax {commands, ...}) =
  let
    val commands' = f commands;
    val markups' =
      Symtab.fold (fn (name, Command {markup = SOME m, ...}) => cons (name, m) | _ => I)
        commands' [];
  in make_syntax commands' markups' end;

fun dest_commands (Syntax {commands, ...}) =
  commands |> Symtab.dest |> sort_wrt #1;

fun lookup_commands (Syntax {commands, ...}) = Symtab.lookup commands;

fun is_markup (Syntax {markups, ...}) kind name =
  AList.lookup (op =) markups name = SOME kind;



(** global outer syntax **)

type command_spec = (string * Keyword.T) * Position.T;

val batch_mode = Unsynchronized.ref false;

local

(*synchronized wrt. Keywords*)
val global_syntax = Unsynchronized.ref empty_syntax;

fun add_command (name, kind) cmd = CRITICAL (fn () =>
  let
    val context = ML_Context.the_generic_context ();
    val thy = Context.theory_of context;
    val Command {pos, ...} = cmd;
    val command_name = quote (Markup.markup Markup.keyword1 name);
    val _ =
      (case try (Thy_Header.the_keyword thy) name of
        SOME spec =>
          if Option.map #1 spec = SOME (Keyword.kind_files_of kind) then ()
          else error ("Inconsistent outer syntax keyword declaration " ^
            command_name ^ Position.here pos)
      | NONE =>
          if Context.theory_name thy = Context.PureN
          then Keyword.define (name, SOME kind)
          else error ("Undeclared outer syntax command " ^ command_name ^ Position.here pos));
    val _ = Context_Position.report_generic context pos (command_markup true (name, cmd));
  in
    Unsynchronized.change global_syntax (map_commands (fn commands =>
     (if not (Symtab.defined commands name) then ()
      else if ! batch_mode then
        error ("Attempt to redefine outer syntax command " ^ command_name)
      else
        warning ("Redefining outer syntax command " ^ command_name ^
          Position.here (Position.thread_data ()));
      Symtab.update (name, cmd) commands)))
  end);

in

fun get_syntax () = CRITICAL (fn () => (Keyword.get_keywords (), ! global_syntax));

fun check_syntax () =
  let
    val (keywords, syntax) = CRITICAL (fn () => (Keyword.get_keywords (), ! global_syntax));
    val major = Keyword.major_keywords keywords;
  in
    (case subtract (op =) (map #1 (dest_commands syntax)) (Scan.dest_lexicon major) of
      [] => ()
    | missing => error ("Missing outer syntax command(s) " ^ commas_quote missing))
  end;

fun command (spec, pos) comment parse =
  add_command spec (new_command comment NONE parse pos);

fun markup_command markup (spec, pos) comment parse =
  add_command spec (new_command comment (SOME markup) parse pos);

end;


(* local_theory commands *)

fun local_theory_command trans command_spec comment parse =
  command command_spec comment (Parse.opt_target -- parse >> (fn (loc, f) => trans loc f));

val local_theory' = local_theory_command Toplevel.local_theory';
val local_theory = local_theory_command Toplevel.local_theory;
val local_theory_to_proof' = local_theory_command Toplevel.local_theory_to_proof';
val local_theory_to_proof = local_theory_command Toplevel.local_theory_to_proof;


(* inspect syntax *)

fun help_syntax pats =
  dest_commands (#2 (get_syntax ()))
  |> filter (fn (name, _) => forall (fn pat => match_string pat name) pats)
  |> map pretty_command
  |> Pretty.writeln_chunks;

fun print_syntax () =
  let
    val (keywords, syntax) = CRITICAL (fn () => (Keyword.get_keywords (), #2 (get_syntax ())));
    val minor = Scan.dest_lexicon (Keyword.minor_keywords keywords);
    val commands = dest_commands syntax;
  in
    [Pretty.strs ("keywords:" :: map quote minor),
      Pretty.big_list "commands:" (map pretty_command commands)]
    |> Pretty.writeln_chunks
  end;



(** toplevel parsing **)

(* parse commands *)

local

fun parse_command syntax =
  Parse.position Parse.command :|-- (fn (name, pos) =>
    let
      val tr0 = Toplevel.empty |> Toplevel.name name |> Toplevel.position pos;
    in
      (case lookup_commands syntax name of
        SOME (Command {parse, ...}) => Parse.!!! (Parse.tags |-- parse) >> (fn f => f tr0)
      | NONE =>
          Scan.succeed
            (tr0 |> Toplevel.imperative (fn () =>
              error ("Bad parser for outer syntax command " ^ quote name ^ Position.here pos))))
    end);

val parse_cmt = Parse.$$$ "--" -- Parse.!!! Parse.document_source;

in

fun commands_source syntax =
  Token.source_proper #>
  Source.source Token.stopper (Scan.bulk (parse_cmt >> K NONE || Parse.not_eof >> SOME)) #>
  Source.map_filter I #>
  Source.source Token.stopper (Scan.bulk (fn xs => Parse.!!! (parse_command syntax) xs));

end;


(* off-line scanning/parsing *)

fun scan keywords pos =
  Source.of_string #>
  Symbol.source #>
  Token.source (K keywords) pos #>
  Source.exhaust;

fun parse (keywords, syntax) pos str =
  Source.of_string str
  |> Symbol.source
  |> Token.source (K keywords) pos
  |> commands_source syntax
  |> Source.exhaust;


(* parse spans *)

local

fun ship span =
  let
    val kind =
      if not (null span) andalso Token.is_command (hd span) andalso not (exists Token.is_error span)
      then Command_Span.Command_Span (Token.content_of (hd span), Token.pos_of (hd span))
      else if forall Token.is_improper span then Command_Span.Ignored_Span
      else Command_Span.Malformed_Span;
  in cons (Command_Span.Span (kind, span)) end;

fun flush (result, content, improper) =
  result
  |> not (null content) ? ship (rev content)
  |> not (null improper) ? ship (rev improper);

fun parse tok (result, content, improper) =
  if Token.is_command tok then (flush (result, content, improper), [tok], [])
  else if Token.is_improper tok then (result, content, tok :: improper)
  else (result, tok :: (improper @ content), []);

in

fun parse_spans toks =
  fold parse toks ([], [], []) |> flush |> rev;

end;


(* side-comments *)

fun cmts (t1 :: t2 :: toks) =
      if Token.keyword_with (fn s => s = "--") t1 then t2 :: cmts toks
      else cmts (t2 :: toks)
  | cmts _ = [];

val side_comments = filter Token.is_proper #> cmts;


(* read commands *)

fun command_reports syntax tok =
  if Token.is_command tok then
    let val name = Token.content_of tok in
      (case lookup_commands syntax name of
        NONE => []
      | SOME cmd => [((Token.pos_of tok, command_markup false (name, cmd)), "")])
    end
  else [];

fun read_spans syntax toks =
  Source.of_list toks
  |> commands_source syntax
  |> Source.exhaust;

end;

