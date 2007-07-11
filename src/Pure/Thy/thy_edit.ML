(*  Title:      Pure/Thy/thy_edit.ML
    ID:         $Id$
    Author:     Makarius

Basic editing of theory sources.
*)

signature THY_EDIT =
sig
  val read_tokens: Position.T -> (string, 'a) Source.source -> OuterLex.token list
  datatype item =
    Whitespace of OuterLex.token list |
    Junk of OuterLex.token list |
    Commandspan of string * OuterLex.token list
  val read_items: Position.T -> (string, 'a) Source.source -> item list
  val present_html: Path.T -> Path.T -> unit
end;

structure ThyEdit: THY_EDIT =
struct

structure T = OuterLex;
structure P = OuterParse;


(* tokens *)

fun token_source pos src =
  Symbol.source true src
  |> T.source (SOME false) OuterSyntax.get_lexicons pos;

fun read_tokens pos src = Source.exhaust (token_source pos src);


(* items *)

datatype item =
  Whitespace of T.token list |
  Junk of T.token list |
  Commandspan of string * T.token list;

local

val whitespace = Scan.many1 (T.is_kind T.Space orf T.is_kind T.Comment);
val before_command = Scan.optional whitespace [] -- Scan.ahead P.command;
val body = Scan.repeat1 (Scan.unless before_command P.not_eof);

val item =
  whitespace >> Whitespace ||
  body >> Junk ||
  before_command -- P.not_eof -- Scan.optional body []
    >> (fn (((ws, name), c), bs) => Commandspan (name, ws @ [c] @ bs));

in

fun item_source src = src
  |> Source.source T.stopper (Scan.bulk item) NONE;

end;

fun read_items pos src =
  Source.exhaust (item_source (token_source pos src));


(* presentation *)

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

fun present_token tok =
  Markup.enclose (token_kind_markup (T.kind_of tok)) (Output.output (T.unparse tok));

val present_tokens = implode o map present_token;

fun present_item (Whitespace toks) = Markup.enclose Markup.whitespace (present_tokens toks)
  | present_item (Junk toks) = Markup.enclose Markup.junk (present_tokens toks)
  | present_item (Commandspan (name, toks)) =
      Markup.enclose (Markup.commandspan name) (present_tokens toks);

val present_items = implode o map present_item;

in

fun present_html inpath outpath =
  read_items (Position.path inpath) (Source.of_string (File.read inpath))
  |> HTML.html_mode present_items
  |> enclose
    (HTML.begin_document (Path.implode (Path.base inpath)) ^ "<div class=\"source\"><pre>")
    ("</pre></div>" ^ HTML.end_document)
  |> File.write outpath;

end

end;
