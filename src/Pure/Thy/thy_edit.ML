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
  datatype item_kind = Whitespace | Junk | Commandspan of string
  type item = item_kind * OuterLex.token list
  val item_source: Position.T -> (string, 'a) Source.source ->
    (item, (OuterLex.token, Position.T * (Symbol.symbol, (string, 'a) Source.source) Source.source)
      Source.source) Source.source
  val parse_items: Position.T -> (string, 'a) Source.source -> item list
  val present_item: item -> output
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
  |> T.source (SOME false) OuterSyntax.get_lexicons pos;

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



(** items **)

datatype item_kind = Whitespace | Junk | Commandspan of string;
type item = item_kind * OuterLex.token list;


(* parse *)

local

val whitespace = Scan.many1 (T.is_kind T.Space orf T.is_kind T.Comment);
val before_command = Scan.optional whitespace [] -- Scan.ahead P.command;
val body = Scan.repeat1 (Scan.unless before_command P.not_eof);

val item =
  whitespace >> pair Whitespace ||
  body >> pair Junk ||
  before_command -- P.not_eof -- Scan.optional body []
    >> (fn (((ws, name), c), bs) => (Commandspan name, ws @ [c] @ bs));

in

fun item_source pos src =
  token_source pos src
  |> Source.source T.stopper (Scan.bulk item) NONE;

end;

fun parse_items pos src = Source.exhaust (item_source pos src);


(* present *)

local

fun item_kind_markup Whitespace = Markup.whitespace
  | item_kind_markup Junk = Markup.junk
  | item_kind_markup (Commandspan name) = Markup.commandspan name;

in

fun present_item (kind, toks) =
  Markup.enclose (item_kind_markup kind) (implode (map present_token toks));

end;


(* HTML presentation -- example *)

fun present_html inpath outpath =
  Source.exhaust (item_source (Position.path inpath) (Source.of_string (File.read inpath)))
  |> HTML.html_mode (implode o map present_item)
  |> enclose
    (HTML.begin_document (Path.implode (Path.base inpath)) ^ "<div class=\"source\"><pre>")
    ("</pre></div>" ^ HTML.end_document)
  |> File.write outpath;

end;
