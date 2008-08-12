(*  Title:      Pure/Thy/thy_edit.ML
    ID:         $Id$
    Author:     Makarius

Basic editor operations on theory sources.
*)

signature THY_EDIT =
sig
  val token_source: Scan.lexicon * Scan.lexicon -> Position.T -> (string, 'a) Source.source ->
    (OuterLex.token, (SymbolPos.T, Position.T * (Symbol.symbol, (string, 'a)
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
  val present_html: Path.T -> Path.T -> unit
end;

structure ThyEdit: THY_EDIT =
struct

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
 fn T.Command   => (Markup.commandN, [])
  | T.Keyword   => (Markup.keywordN, [])
  | T.Ident     => Markup.ident
  | T.LongIdent => Markup.ident
  | T.SymIdent  => Markup.ident
  | T.Var       => Markup.ident
  | T.TypeIdent => Markup.ident
  | T.TypeVar   => Markup.ident
  | T.Nat       => Markup.ident
  | T.String    => Markup.string
  | T.AltString => Markup.altstring
  | T.Verbatim  => Markup.verbatim
  | T.Comment   => Markup.comment
  | T.Sync      => Markup.control
  | T.Malformed => Markup.malformed
  | T.Error _   => Markup.malformed
  | T.EOF       => Markup.control
  | _           => Markup.none;

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


(* HTML presentation -- example *)

fun present_html inpath outpath =
  parse_spans (OuterKeyword.get_lexicons ()) (Path.position inpath) (File.read inpath)
  |> HTML.html_mode (implode o map present_span)
  |> enclose
    (HTML.begin_document (Path.implode (Path.base inpath)) ^ "<div class=\"source\"><pre>")
    ("</pre></div>" ^ HTML.end_document)
  |> File.write outpath;

end;
