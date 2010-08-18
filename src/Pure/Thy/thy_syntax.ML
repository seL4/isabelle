(*  Title:      Pure/Thy/thy_syntax.ML
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*)

signature THY_SYNTAX =
sig
  val token_source: Scan.lexicon * Scan.lexicon -> Position.T -> (string, 'a) Source.source ->
    (Token.T, (Symbol_Pos.T, Position.T * (Symbol.symbol, (string, 'a)
      Source.source) Source.source) Source.source) Source.source
  val parse_tokens: Scan.lexicon * Scan.lexicon -> Position.T -> string -> Token.T list
  val present_token: Token.T -> output
  val report_token: Token.T -> unit
  datatype span_kind = Command of string | Ignored | Malformed
  type span
  val span_kind: span -> span_kind
  val span_content: span -> Token.T list
  val span_range: span -> Position.range
  val span_source: (Token.T, 'a) Source.source -> (span, (Token.T, 'a) Source.source) Source.source
  val parse_spans: Scan.lexicon * Scan.lexicon -> Position.T -> string -> span list
  val present_span: span -> output
  val report_span: span -> unit
  val atom_source: (span, 'a) Source.source ->
    (span * span list * bool, (span, 'a) Source.source) Source.source
end;

structure Thy_Syntax: THY_SYNTAX =
struct

(** tokens **)

(* parse *)

fun token_source lexs pos src =
  Symbol.source {do_recover = true} src
  |> Token.source {do_recover = SOME false} (K lexs) pos;

fun parse_tokens lexs pos str =
  Source.of_string str
  |> token_source lexs pos
  |> Source.exhaust;


(* present *)

local

val token_kind_markup =
 fn Token.Command       => Markup.command
  | Token.Keyword       => Markup.keyword
  | Token.Ident         => Markup.ident
  | Token.LongIdent     => Markup.ident
  | Token.SymIdent      => Markup.ident
  | Token.Var           => Markup.var
  | Token.TypeIdent     => Markup.tfree
  | Token.TypeVar       => Markup.tvar
  | Token.Nat           => Markup.ident
  | Token.String        => Markup.string
  | Token.AltString     => Markup.altstring
  | Token.Verbatim      => Markup.verbatim
  | Token.Space         => Markup.empty
  | Token.Comment       => Markup.comment
  | Token.InternalValue => Markup.empty
  | Token.Malformed     => Markup.malformed
  | Token.Error _       => Markup.malformed
  | Token.Sync          => Markup.control
  | Token.EOF           => Markup.control;

fun token_markup tok =
  if Token.keyword_with (not o Syntax.is_identifier) tok then Markup.operator
  else
    let
      val kind = Token.kind_of tok;
      val props =
        if kind = Token.Command
        then Markup.properties [(Markup.nameN, Token.content_of tok)]
        else I;
    in props (token_kind_markup kind) end;

in

fun present_token tok =
  Markup.enclose (token_markup tok) (Output.output (Token.unparse tok));

fun report_token tok =
  Position.report (token_markup tok) (Token.position_of tok);

end;



(** spans **)

(* type span *)

datatype span_kind = Command of string | Ignored | Malformed;
datatype span = Span of span_kind * Token.T list;

fun span_kind (Span (k, _)) = k;
fun span_content (Span (_, toks)) = toks;

fun span_range span =
  (case span_content span of
    [] => (Position.none, Position.none)
  | toks =>
      let
        val start_pos = Token.position_of (hd toks);
        val end_pos = Token.end_position_of (List.last toks);
      in (start_pos, end_pos) end);


(* parse *)

local

val is_whitespace = Token.is_kind Token.Space orf Token.is_kind Token.Comment;

val body =
  Scan.unless (Scan.many is_whitespace -- Scan.ahead (Parse.command || Parse.eof)) Parse.not_eof;

val span =
  Scan.ahead Parse.command -- Parse.not_eof -- Scan.repeat body
    >> (fn ((name, c), bs) => Span (Command name, c :: bs)) ||
  Scan.many1 is_whitespace >> (fn toks => Span (Ignored, toks)) ||
  Scan.repeat1 body >> (fn toks => Span (Malformed, toks));

in

fun span_source src = Source.source Token.stopper (Scan.bulk span) NONE src;

end;

fun parse_spans lexs pos str =
  Source.of_string str
  |> token_source lexs pos
  |> span_source
  |> Source.exhaust;


(* present *)

local

fun kind_markup (Command name) = Markup.command_span name
  | kind_markup Ignored = Markup.ignored_span
  | kind_markup Malformed = Markup.malformed_span;

in

fun present_span span =
  Markup.enclose (kind_markup (span_kind span)) (implode (map present_token (span_content span)));

fun report_span span =
  Position.report (kind_markup (span_kind span)) (Position.encode_range (span_range span));

end;



(** specification atoms: commands with optional proof **)

(* scanning spans *)

val eof = Span (Command "", []);

fun is_eof (Span (Command "", _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper = Scan.stopper (K eof) is_eof;


(* atom_source *)

local

fun command_with pred = Scan.one (fn (Span (Command name, _)) => pred name | _ => false);

val proof = Scan.pass 1 (Scan.repeat (Scan.depend (fn d =>
  if d <= 0 then Scan.fail
  else
    command_with Keyword.is_qed_global >> pair ~1 ||
    command_with Keyword.is_proof_goal >> pair (d + 1) ||
    (if d = 0 then Scan.fail else command_with Keyword.is_qed >> pair (d - 1)) ||
    Scan.unless (command_with Keyword.is_theory) (Scan.one not_eof) >> pair d)) -- Scan.state);

val atom =
  command_with Keyword.is_theory_goal -- proof >> (fn (a, (bs, d)) => (a, bs, d >= 0)) ||
  Scan.one not_eof >> (fn a => (a, [], true));

in

fun atom_source src = Source.source stopper (Scan.bulk atom) NONE src;

end;

end;
