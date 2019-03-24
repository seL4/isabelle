(*  Title:      Pure/General/comment.ML
    Author:     Makarius

Formal comments.
*)

signature COMMENT =
sig
  datatype kind = Comment | Cancel | Latex | Marker
  val kind_markups: kind -> Markup.T list
  val is_symbol: Symbol.symbol -> bool
  val scan_comment: (kind * Symbol_Pos.T list) scanner
  val scan_cancel: (kind * Symbol_Pos.T list) scanner
  val scan_latex: (kind * Symbol_Pos.T list) scanner
  val scan_marker: (kind * Symbol_Pos.T list) scanner
  val scan_inner: (kind * Symbol_Pos.T list) scanner
  val scan_outer: (kind * Symbol_Pos.T list) scanner
  val read_body: Symbol_Pos.T list -> (kind option * Symbol_Pos.T list) list
end;

structure Comment: COMMENT =
struct

(* kinds *)

datatype kind = Comment | Cancel | Latex | Marker;

val kinds =
  [(Comment,
     {symbol = Symbol.comment, blanks = true,
      markups = [Markup.language_document true, Markup.plain_text]}),
   (Cancel,
     {symbol = Symbol.cancel, blanks = false,
      markups = [Markup.language_text true, Markup.raw_text]}),
   (Latex,
     {symbol = Symbol.latex, blanks = false,
      markups = [Markup.language_latex true, Markup.no_words, Markup.raw_text]}),
   (Marker,
     {symbol = Symbol.marker, blanks = false,
      markups = [Markup.language_document_marker]})];

val get_kind = the o AList.lookup (op =) kinds;
val print_kind = quote o #symbol o get_kind;

fun kind_markups kind = Markup.cartouche :: #markups (get_kind kind);

fun is_symbol sym = exists (fn (_, {symbol, ...}) => symbol = sym) kinds;


(* scan *)

local

open Basic_Symbol_Pos;

val err_prefix = "Error in formal comment: ";

val scan_blanks = Scan.many (Symbol.is_blank o Symbol_Pos.symbol);

fun scan_symbol kind =
  let val {blanks, symbol, ...} = get_kind kind
  in if blanks then $$$ symbol @@@ scan_blanks else $$$ symbol end;

fun scan_strict kind =
  scan_symbol kind @@@
    Symbol_Pos.!!! (fn () => err_prefix ^ "cartouche expected after " ^ print_kind kind)
      (Symbol_Pos.scan_cartouche err_prefix) >> pair kind;

fun scan_permissive kind =
  scan_symbol kind -- Scan.option (Symbol_Pos.scan_cartouche err_prefix) >>
    (fn (ss, NONE) => (NONE, ss) | (_, SOME ss) => (SOME kind, ss));

in

val scan_comment = scan_strict Comment;
val scan_cancel = scan_strict Cancel;
val scan_latex = scan_strict Latex;
val scan_marker = scan_strict Marker;

val scan_inner = scan_comment || scan_cancel || scan_latex;
val scan_outer = scan_inner || scan_marker;

val scan_body =
  Scan.many1 (fn (s, _) => not (is_symbol s) andalso Symbol.not_eof s) >> pair NONE ||
  scan_permissive Comment || scan_permissive Cancel || scan_permissive Latex;

fun read_body syms =
  (if exists (is_symbol o Symbol_Pos.symbol) syms then
    Scan.read Symbol_Pos.stopper (Scan.repeat scan_body) syms
  else NONE) |> the_default [(NONE, syms)];

end;

end;
