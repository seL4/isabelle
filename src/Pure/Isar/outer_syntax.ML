(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar outer syntax.
*)

signature OUTER_SYNTAX =
sig
  datatype markup = Markup | Markup_Env | Verbatim
  val is_markup: theory -> markup -> string -> bool
  val help_syntax: theory -> string list -> unit
  val print_syntax: theory -> unit
  type command_spec = string * Position.T
  val command: command_spec -> string ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val markup_command: markup -> command_spec -> string ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val local_theory': command_spec -> string ->
    (bool -> local_theory -> local_theory) parser -> unit
  val local_theory: command_spec -> string ->
    (local_theory -> local_theory) parser -> unit
  val local_theory_to_proof': command_spec -> string ->
    (bool -> local_theory -> Proof.state) parser -> unit
  val local_theory_to_proof: command_spec -> string ->
    (local_theory -> Proof.state) parser -> unit
  val scan: Keyword.keywords -> Position.T -> string -> Token.T list
  val parse: theory -> Position.T -> string -> Toplevel.transition list
  val parse_tokens: theory -> Token.T list -> Toplevel.transition list
  val parse_spans: Token.T list -> Command_Span.span list
  val side_comments: Token.T list -> Token.T list
  val command_reports: theory -> Token.T -> Position.report_text list
end;

structure Outer_Syntax: OUTER_SYNTAX =
struct

(** outer syntax **)

(* errors *)

fun err_command msg name ps =
  error (msg ^ quote (Markup.markup Markup.keyword1 name) ^ Position.here_list ps);

fun err_dup_command name ps =
  err_command "Duplicate outer syntax command " name ps;


(* command parsers *)

datatype markup = Markup | Markup_Env | Verbatim;

datatype command = Command of
 {comment: string,
  markup: markup option,
  parse: (Toplevel.transition -> Toplevel.transition) parser,
  pos: Position.T,
  id: serial};

fun eq_command (Command {id = id1, ...}, Command {id = id2, ...}) = id1 = id2;

fun new_command comment markup parse pos =
  Command {comment = comment, markup = markup, parse = parse, pos = pos, id = serial ()};

fun command_pos (Command {pos, ...}) = pos;

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
  markups: (string * markup) list};

fun make_syntax (commands, markups) =
  Syntax {commands = commands, markups = markups};

structure Data = Theory_Data
(
  type T = syntax;
  val empty = make_syntax (Symtab.empty, []);
  val extend = I;
  fun merge (Syntax {commands = commands1, markups = markups1},
      Syntax {commands = commands2, markups = markups2}) =
    let
      val commands' = (commands1, commands2)
        |> Symtab.join (fn name => fn (cmd1, cmd2) =>
          if eq_command (cmd1, cmd2) then raise Symtab.SAME
          else err_dup_command name [command_pos cmd1, command_pos cmd2]);
      val markups' = AList.merge (op =) (K true) (markups1, markups2);
    in make_syntax (commands', markups') end;
);


(* inspect syntax *)

val get_syntax = Data.get;

val dest_commands =
  get_syntax #> (fn Syntax {commands, ...} => commands |> Symtab.dest |> sort_wrt #1);

val lookup_commands =
  get_syntax #> (fn Syntax {commands, ...} => Symtab.lookup commands);

val is_markup =
  get_syntax #> (fn Syntax {markups, ...} => fn kind => fn name =>
    AList.lookup (op =) markups name = SOME kind);

fun help_syntax thy pats =
  dest_commands thy
  |> filter (fn (name, _) => forall (fn pat => match_string pat name) pats)
  |> map pretty_command
  |> Pretty.writeln_chunks;

fun print_syntax thy =
  let
    val keywords = Thy_Header.get_keywords thy;
    val minor = Scan.dest_lexicon (Keyword.minor_keywords keywords);
    val commands = dest_commands thy;
  in
    [Pretty.strs ("keywords:" :: map quote minor),
      Pretty.big_list "commands:" (map pretty_command commands)]
    |> Pretty.writeln_chunks
  end;


(* build syntax *)

fun add_command name cmd thy = thy |> Data.map (fn Syntax {commands, ...} =>
  let
    val keywords = Thy_Header.get_keywords thy;
    val _ =
      Keyword.is_command keywords name orelse
        err_command "Undeclared outer syntax command " name [command_pos cmd];

    val _ =
      (case Symtab.lookup commands name of
        NONE => ()
      | SOME cmd' => err_dup_command name [command_pos cmd, command_pos cmd']);

    val _ =
      Context_Position.report_generic (ML_Context.the_generic_context ())
        (command_pos cmd) (command_markup true (name, cmd));

    val commands' = Symtab.update (name, cmd) commands;
    val markups' =
      Symtab.fold (fn (name, Command {markup = SOME m, ...}) => cons (name, m) | _ => I)
        commands' [];
  in make_syntax (commands', markups') end);

val _ = Theory.setup (Theory.at_end (fn thy =>
  let
    val keywords = Thy_Header.get_keywords thy;
    val major = Keyword.major_keywords keywords;
    val _ =
      (case subtract (op =) (map #1 (dest_commands thy)) (Scan.dest_lexicon major) of
        [] => ()
      | missing => error ("Missing outer syntax command(s) " ^ commas_quote missing))
  in NONE end));


(* implicit theory setup *)

type command_spec = string * Position.T;

fun command (name, pos) comment parse =
  Theory.setup (add_command name (new_command comment NONE parse pos));

fun markup_command markup (name, pos) comment parse =
  Theory.setup (add_command name (new_command comment (SOME markup) parse pos));

fun local_theory_command trans command_spec comment parse =
  command command_spec comment (Parse.opt_target -- parse >> (fn (loc, f) => trans loc f));

val local_theory' = local_theory_command Toplevel.local_theory';
val local_theory = local_theory_command Toplevel.local_theory;
val local_theory_to_proof' = local_theory_command Toplevel.local_theory_to_proof';
val local_theory_to_proof = local_theory_command Toplevel.local_theory_to_proof;



(** toplevel parsing **)

(* scan tokens *)

fun scan keywords pos =
  Source.of_string #>
  Symbol.source #>
  Token.source keywords pos #>
  Source.exhaust;


(* parse commands *)

local

fun parse_command thy =
  Parse.position Parse.command_ :|-- (fn (name, pos) =>
    let
      val tr0 = Toplevel.empty |> Toplevel.name name |> Toplevel.position pos;
    in
      (case lookup_commands thy name of
        SOME (Command {parse, ...}) => Parse.!!! (Parse.tags |-- parse) >> (fn f => f tr0)
      | NONE =>
          Scan.succeed
            (tr0 |> Toplevel.imperative (fn () =>
              err_command "Bad parser for outer syntax command " name [pos])))
    end);

val parse_cmt = Parse.$$$ "--" -- Parse.!!! Parse.document_source;

in

fun commands_source thy =
  Token.source_proper #>
  Source.source Token.stopper (Scan.bulk (parse_cmt >> K NONE || Parse.not_eof >> SOME)) #>
  Source.map_filter I #>
  Source.source Token.stopper (Scan.bulk (fn xs => Parse.!!! (parse_command thy) xs));

end;

fun parse thy pos str =
  Source.of_string str
  |> Symbol.source
  |> Token.source (Thy_Header.get_keywords thy) pos
  |> commands_source thy
  |> Source.exhaust;

fun parse_tokens thy toks =
  Source.of_list toks
  |> commands_source thy
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

fun command_reports thy tok =
  if Token.is_command tok then
    let val name = Token.content_of tok in
      (case lookup_commands thy name of
        NONE => []
      | SOME cmd => [((Token.pos_of tok, command_markup false (name, cmd)), "")])
    end
  else [];

end;

