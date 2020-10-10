(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar outer syntax.
*)

signature OUTER_SYNTAX =
sig
  val help: theory -> string list -> unit
  val print_commands: theory -> unit
  type command_keyword = string * Position.T
  val command: command_keyword -> string ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val maybe_begin_local_theory: command_keyword -> string ->
    (local_theory -> local_theory) parser -> (theory -> local_theory) parser -> unit
  val local_theory': command_keyword -> string ->
    (bool -> local_theory -> local_theory) parser -> unit
  val local_theory: command_keyword -> string ->
    (local_theory -> local_theory) parser -> unit
  val local_theory_to_proof': command_keyword -> string ->
    (bool -> local_theory -> Proof.state) parser -> unit
  val local_theory_to_proof: command_keyword -> string ->
    (local_theory -> Proof.state) parser -> unit
  val bootstrap: bool Config.T
  val parse_spans: Token.T list -> Command_Span.span list
  val make_span: Token.T list -> Command_Span.span
  val parse_span: theory -> (unit -> theory) -> Token.T list -> Toplevel.transition
  val parse_text: theory -> (unit -> theory) -> Position.T -> string -> Toplevel.transition list
  val command_reports: theory -> Token.T -> Position.report_text list
  val check_command: Proof.context -> command_keyword -> string
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

datatype command_parser =
  Parser of (Toplevel.transition -> Toplevel.transition) parser |
  Restricted_Parser of
    (bool * Position.T) option -> (Toplevel.transition -> Toplevel.transition) parser;

datatype command = Command of
 {comment: string,
  command_parser: command_parser,
  pos: Position.T,
  id: serial};

fun eq_command (Command {id = id1, ...}, Command {id = id2, ...}) = id1 = id2;

fun new_command comment command_parser pos =
  Command {comment = comment, command_parser = command_parser, pos = pos, id = serial ()};

fun command_pos (Command {pos, ...}) = pos;

fun command_markup def (name, Command {pos, id, ...}) =
  Markup.properties (Position.entity_properties_of def id pos)
    (Markup.entity Markup.commandN name);

fun pretty_command (cmd as (name, Command {comment, ...})) =
  Pretty.block
    (Pretty.marks_str
      ([Active.make_markup Markup.sendbackN {implicit = true, properties = [Markup.padding_line]},
        command_markup false cmd], name) :: Pretty.str ":" :: Pretty.brk 2 :: Pretty.text comment);


(* theory data *)

structure Data = Theory_Data
(
  type T = command Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T =
    data |> Symtab.join (fn name => fn (cmd1, cmd2) =>
      if eq_command (cmd1, cmd2) then raise Symtab.SAME
      else err_dup_command name [command_pos cmd1, command_pos cmd2]);
);

val get_commands = Data.get;
val dest_commands = get_commands #> Symtab.dest #> sort_by #1;
val lookup_commands = Symtab.lookup o get_commands;

fun help thy pats =
  dest_commands thy
  |> filter (fn (name, _) => forall (fn pat => match_string pat name) pats)
  |> map pretty_command
  |> Pretty.writeln_chunks;

fun print_commands thy =
  let
    val keywords = Thy_Header.get_keywords thy;
    val minor = Scan.dest_lexicon (Keyword.minor_keywords keywords);
    val commands = dest_commands thy;
  in
    [Pretty.strs ("keywords:" :: map quote minor),
      Pretty.big_list "commands:" (map pretty_command commands)]
    |> Pretty.writeln_chunks
  end;


(* maintain commands *)

fun add_command name cmd thy =
  if member (op =) Thy_Header.bootstrap_thys (Context.theory_name thy) then thy
  else
    let
      val _ =
        Keyword.is_command (Thy_Header.get_keywords thy) name orelse
          err_command "Undeclared outer syntax command " name [command_pos cmd];
      val _ =
        (case lookup_commands thy name of
          NONE => ()
        | SOME cmd' => err_dup_command name [command_pos cmd, command_pos cmd']);
      val _ =
        Context_Position.report_generic (Context.the_generic_context ())
          (command_pos cmd) (command_markup true (name, cmd));
    in Data.map (Symtab.update (name, cmd)) thy end;

val _ = Theory.setup (Theory.at_end (fn thy =>
  let
    val command_keywords =
      Scan.dest_lexicon (Keyword.major_keywords (Thy_Header.get_keywords thy));
    val _ =
      (case subtract (op =) (map #1 (dest_commands thy)) command_keywords of
        [] => ()
      | missing => error ("Missing outer syntax command(s) " ^ commas_quote missing))
  in NONE end));


(* implicit theory setup *)

type command_keyword = string * Position.T;

fun raw_command (name, pos) comment command_parser =
  let val setup = add_command name (new_command comment command_parser pos)
  in Context.>> (Context.mapping setup (Local_Theory.background_theory setup)) end;

fun command (name, pos) comment parse =
  raw_command (name, pos) comment (Parser parse);

fun maybe_begin_local_theory command_keyword comment parse_local parse_global =
  raw_command command_keyword comment
    (Restricted_Parser (fn restricted =>
      Parse.opt_target -- parse_local
        >> (fn (target, f) => Toplevel.local_theory restricted target f) ||
      (if is_some restricted then Scan.fail
       else parse_global >> Toplevel.begin_main_target true)));

fun local_theory_command trans command_keyword comment parse =
  raw_command command_keyword comment
    (Restricted_Parser (fn restricted =>
      Parse.opt_target -- parse >> (fn (target, f) => trans restricted target f)));

val local_theory' = local_theory_command Toplevel.local_theory';
val local_theory = local_theory_command Toplevel.local_theory;
val local_theory_to_proof' = local_theory_command Toplevel.local_theory_to_proof';
val local_theory_to_proof = local_theory_command Toplevel.local_theory_to_proof;



(** toplevel parsing **)

(* parse spans *)

local

fun ship span =
  let
    val kind =
      if forall Token.is_ignored span then Command_Span.Ignored_Span
      else if exists Token.is_error span then Command_Span.Malformed_Span
      else
        (case find_first Token.is_command span of
          NONE => Command_Span.Malformed_Span
        | SOME cmd => Command_Span.Command_Span (Token.content_of cmd, Token.pos_of cmd));
  in cons (Command_Span.Span (kind, span)) end;

fun flush (result, content, ignored) =
  result
  |> not (null content) ? ship (rev content)
  |> not (null ignored) ? ship (rev ignored);

fun parse tok (result, content, ignored) =
  if Token.is_ignored tok then (result, content, tok :: ignored)
  else if Token.is_command_modifier tok orelse
    Token.is_command tok andalso
      (not (exists Token.is_command_modifier content) orelse exists Token.is_command content)
  then (flush (result, content, ignored), [tok], [])
  else (result, tok :: (ignored @ content), []);

in

fun parse_spans toks =
  fold parse toks ([], [], []) |> flush |> rev;

end;

fun make_span toks =
  (case parse_spans toks of
    [span] => span
  | _ => Command_Span.Span (Command_Span.Malformed_Span, toks));


(* parse commands *)

val bootstrap = Config.declare_bool ("Outer_Syntax.bootstrap", \<^here>) (K true);

local

val before_command =
  Scan.option (Parse.position (Parse.private >> K true || Parse.qualified >> K false));

fun parse_command thy markers =
  Scan.ahead (before_command |-- Parse.position Parse.command) :|-- (fn (name, pos) =>
    let
      val keywords = Thy_Header.get_keywords thy;
      val tr0 =
        Toplevel.empty
        |> Toplevel.name name
        |> Toplevel.position pos
        |> Keyword.is_proof_open keywords name ? Toplevel.skip_proof_open
        |> Keyword.is_proof_close keywords name ? Toplevel.skip_proof_close;
      val command_markers =
        Parse.command |-- Document_Source.old_tags >>
          (fn tags => Toplevel.markers (map Document_Marker.legacy_tag tags @ markers) tr0);
    in
      (case lookup_commands thy name of
        SOME (Command {command_parser = Parser parse, ...}) =>
          Parse.!!! (command_markers -- parse) >> (op |>)
      | SOME (Command {command_parser = Restricted_Parser parse, ...}) =>
          before_command :|-- (fn restricted =>
            Parse.!!! (command_markers -- parse restricted)) >> (op |>)
      | NONE =>
          Scan.fail_with (fn _ => fn _ =>
            let
              val msg =
                if Config.get_global thy bootstrap
                then "missing theory context for command "
                else "undefined command ";
            in msg ^ quote (Markup.markup Markup.keyword1 name) end))
    end);

in

fun parse_span thy init span =
  let
    val range = Token.range_of span;
    val core_range = Token.core_range_of span;

    val markers = map Token.input_of (filter Token.is_document_marker span);
    fun parse () =
      filter Token.is_proper span
      |> Source.of_list
      |> Source.source Token.stopper (Scan.bulk (fn xs => Parse.!!! (parse_command thy markers) xs))
      |> Source.exhaust;
  in
    (case parse () of
      [tr] => Toplevel.modify_init init tr
    | [] => Toplevel.ignored (#1 range)
    | _ => Toplevel.malformed (#1 core_range) "Exactly one command expected")
    handle ERROR msg => Toplevel.malformed (#1 core_range) msg
  end;

fun parse_text thy init pos text =
  Symbol_Pos.explode (text, pos)
  |> Token.tokenize (Thy_Header.get_keywords thy) {strict = false}
  |> parse_spans
  |> map (Command_Span.content #> parse_span thy init);

end;


(* check commands *)

fun command_reports thy tok =
  if Token.is_command tok then
    let val name = Token.content_of tok in
      (case lookup_commands thy name of
        NONE => []
      | SOME cmd => [((Token.pos_of tok, command_markup false (name, cmd)), "")])
    end
  else [];

fun check_command ctxt (name, pos) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val keywords = Thy_Header.get_keywords thy;
  in
    if Keyword.is_command keywords name then
      let
        val markup =
          Token.explode0 keywords name
          |> maps (command_reports thy)
          |> map (#2 o #1);
        val _ = Context_Position.reports ctxt (map (pair pos) markup);
      in name end
    else
      let
        val completion_report =
          Completion.make_report (name, pos)
            (fn completed =>
              Keyword.dest_commands keywords
              |> filter completed
              |> sort_strings
              |> map (fn a => (a, (Markup.commandN, a))));
      in error ("Bad command " ^ quote name ^ Position.here pos ^ completion_report) end
  end;


(* 'ML' command -- required for bootstrapping Isar *)

val _ =
  command ("ML", \<^here>) "ML text within theory or local theory"
    (Parse.ML_source >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source) #>
          Local_Theory.propagate_ml_env)));

end;
