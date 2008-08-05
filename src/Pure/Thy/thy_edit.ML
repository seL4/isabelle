(*  Title:      Pure/Thy/thy_edit.ML
    ID:         $Id$
    Author:     Makarius

Basic editing of theory sources.
*)

signature THY_EDIT =
sig
  val token_source: Position.T -> (string, 'a) Source.source ->
    (OuterLex.token, Position.T * (Symbol.symbol, (string, 'a) Source.source) Source.source)
      Source.source
  val parse_tokens: Position.T -> (string, 'a) Source.source -> OuterLex.token list
  val present_token: OuterLex.token -> output
  datatype span_kind = Command of string | Ignored | Unknown
  type span = span_kind * OuterLex.token list
  val span_range: span -> Position.range
  val span_source: Position.T -> (string, 'a) Source.source ->
    (span, (OuterLex.token, Position.T * (Symbol.symbol, (string, 'a) Source.source) Source.source)
      Source.source) Source.source
  val parse_spans: Position.T -> (string, 'a) Source.source -> span list
  val present_span: span -> output
  val present_html: Path.T -> Path.T -> unit
end;

structure ThyEdit: THY_EDIT =
struct

structure T = OuterLex;
structure P = OuterParse;


(** tokens **)

(* parse *)

fun token_source pos src =
  Symbol.source true src
  |> T.source (SOME false) OuterKeyword.get_lexicons pos;

fun parse_tokens pos src = Source.exhaust (token_source pos src);


(* present *)

local

val token_kind_markup =
 fn T.Command   => (Markup.commandN, [])
  | T.Keyword   => (Markup.keywordN, [])
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

end;



(** spans **)

datatype span_kind = Command of string | Ignored | Unknown;
type span = span_kind * OuterLex.token list;

fun span_range ((_, []): span) = raise Fail "span_range: empty span"
  | span_range (_, toks) =
      let
        val start_pos = T.position_of (hd toks);
        val end_pos = T.end_position_of (List.last toks);
      in (start_pos, end_pos) end;


(* parse *)

local

val is_whitespace = T.is_kind T.Space orf T.is_kind T.Comment;

val body = Scan.unless (Scan.many is_whitespace -- Scan.ahead (P.command || P.eof)) P.not_eof;

val span =
  Scan.ahead P.command -- P.not_eof -- Scan.repeat body
    >> (fn ((name, c), bs) => (Command name, c :: bs)) ||
  Scan.many1 is_whitespace >> pair Ignored ||
  Scan.repeat1 body >> pair Unknown;

in

fun span_source pos src =
  token_source pos src
  |> Source.source T.stopper (Scan.bulk span) NONE;

end;

fun parse_spans pos src = Source.exhaust (span_source pos src);


(* present *)

local

fun kind_markup (Command name) = Markup.command_span name
  | kind_markup Ignored = Markup.ignored_span
  | kind_markup Unknown = Markup.unknown_span;

in

fun present_span (kind, toks) =
  Markup.enclose (kind_markup kind) (implode (map present_token toks));

end;


(* HTML presentation -- example *)

fun present_html inpath outpath =
  parse_spans (Path.position inpath) (Source.of_string (File.read inpath))
  |> HTML.html_mode (implode o map present_span)
  |> enclose
    (HTML.begin_document (Path.implode (Path.base inpath)) ^ "<div class=\"source\"><pre>")
    ("</pre></div>" ^ HTML.end_document)
  |> File.write outpath;

end;
