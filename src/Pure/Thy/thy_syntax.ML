(*  Title:      Pure/Thy/thy_syntax.ML
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*)

signature THY_SYNTAX =
sig
  val token_source: Scan.lexicon * Scan.lexicon -> Position.T -> (string, 'a) Source.source ->
    (OuterLex.token, (Symbol_Pos.T, Position.T * (Symbol.symbol, (string, 'a)
      Source.source) Source.source) Source.source) Source.source
  val parse_tokens: Scan.lexicon * Scan.lexicon -> Position.T -> string -> OuterLex.token list
  val present_token: OuterLex.token -> output
  val report_token: OuterLex.token -> unit
  datatype span_kind = Command of string | Ignored | Malformed
  type span
  val span_kind: span -> span_kind
  val span_content: span -> OuterLex.token list
  val span_range: span -> Position.range
  val span_source: (OuterLex.token, 'a) Source.source ->
    (span, (OuterLex.token, 'a) Source.source) Source.source
  val parse_spans: Scan.lexicon * Scan.lexicon -> Position.T -> string -> span list
  val present_span: span -> output
  val report_span: span -> unit
  val unit_source: (span, 'a) Source.source ->
    (span * span list * bool, (span, 'a) Source.source) Source.source
end;

structure ThySyntax: THY_SYNTAX =
struct

structure K = OuterKeyword;
structure T = OuterLex;
structure P = OuterParse;


(** tokens **)

(* parse *)

fun token_source lexs pos src =
  Symbol.source {do_recover = true} src
  |> T.source {do_recover = SOME false} (K lexs) pos;

fun parse_tokens lexs pos str =
  Source.of_string str
  |> token_source lexs pos
  |> Source.exhaust;


(* present *)

local

val token_kind_markup =
 fn T.Command       => (Markup.commandN, [])
  | T.Keyword       => (Markup.keywordN, [])
  | T.Ident         => Markup.ident
  | T.LongIdent     => Markup.ident
  | T.SymIdent      => Markup.ident
  | T.Var           => Markup.var
  | T.TypeIdent     => Markup.tfree
  | T.TypeVar       => Markup.tvar
  | T.Nat           => Markup.ident
  | T.String        => Markup.string
  | T.AltString     => Markup.altstring
  | T.Verbatim      => Markup.verbatim
  | T.Space         => Markup.none
  | T.Comment       => Markup.comment
  | T.InternalValue => Markup.none
  | T.Malformed     => Markup.malformed
  | T.Error _       => Markup.malformed
  | T.Sync          => Markup.control
  | T.EOF           => Markup.control;

in

fun present_token tok =
  Markup.enclose (token_kind_markup (T.kind_of tok)) (Output.output (T.unparse tok));

fun report_token tok =
  Position.report (token_kind_markup (T.kind_of tok)) (T.position_of tok);

end;



(** spans **)

(* type span *)

datatype span_kind = Command of string | Ignored | Malformed;
datatype span = Span of span_kind * OuterLex.token list;

fun span_kind (Span (k, _)) = k;
fun span_content (Span (_, toks)) = toks;

fun span_range span =
  (case span_content span of
    [] => (Position.none, Position.none)
  | toks =>
      let
        val start_pos = T.position_of (hd toks);
        val end_pos = T.end_position_of (List.last toks);
      in (start_pos, end_pos) end);


(* parse *)

local

val is_whitespace = T.is_kind T.Space orf T.is_kind T.Comment;

val body = Scan.unless (Scan.many is_whitespace -- Scan.ahead (P.command || P.eof)) P.not_eof;

val span =
  Scan.ahead P.command -- P.not_eof -- Scan.repeat body
    >> (fn ((name, c), bs) => Span (Command name, c :: bs)) ||
  Scan.many1 is_whitespace >> (fn toks => Span (Ignored, toks)) ||
  Scan.repeat1 body >> (fn toks => Span (Malformed, toks));

in

fun span_source src = Source.source T.stopper (Scan.bulk span) NONE src;

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



(** units: commands with proof **)

(* scanning spans *)

val eof = Span (Command "", []);

fun is_eof (Span (Command "", _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper = Scan.stopper (K eof) is_eof;


(* unit_source *)

local

fun command_with pred = Scan.one (fn (Span (Command name, _)) => pred name | _ => false);

val proof = Scan.pass 1 (Scan.repeat (Scan.depend (fn d =>
  if d <= 0 then Scan.fail
  else
    command_with K.is_qed_global >> pair ~1 ||
    command_with K.is_proof_goal >> pair (d + 1) ||
    (if d = 0 then Scan.fail else command_with K.is_qed >> pair (d - 1)) ||
    Scan.unless (command_with K.is_theory) (Scan.one not_eof) >> pair d)) -- Scan.state);

val unit =
  command_with K.is_theory_goal -- proof >> (fn (a, (bs, d)) => (a, bs, d >= 0)) ||
  Scan.one not_eof >> (fn a => (a, [], true));

in

fun unit_source src = Source.source stopper (Scan.bulk unit) NONE src;

end;

end;
