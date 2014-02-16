(*  Title:      Pure/General/antiquote.ML
    Author:     Makarius

Antiquotations within plain text.
*)

signature ANTIQUOTE =
sig
  datatype 'a antiquote =
    Text of 'a |
    Antiq of Symbol_Pos.T list * Position.range
  val is_text: 'a antiquote -> bool
  val reports_of: ('a -> Position.report_text list) ->
    'a antiquote list -> Position.report_text list
  val scan_antiq: Symbol_Pos.T list -> (Symbol_Pos.T list * Position.range) * Symbol_Pos.T list
  val scan_antiquote: Symbol_Pos.T list -> Symbol_Pos.T list antiquote * Symbol_Pos.T list
  val read: Symbol_Pos.T list * Position.T -> Symbol_Pos.T list antiquote list
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

datatype 'a antiquote =
  Text of 'a |
  Antiq of Symbol_Pos.T list * Position.range;

fun is_text (Text _) = true
  | is_text _ = false;


(* reports *)

fun reports_of text =
  maps (fn Text x => text x | Antiq (_, (pos, _)) => [((pos, Markup.antiq), "")]);


(* scan *)

open Basic_Symbol_Pos;

local

val err_prefix = "Antiquotation lexical error: ";

val scan_txt =
  Scan.repeat1 ($$$ "@" --| Scan.ahead (~$$ "{") ||
    Scan.many1 (fn (s, _) => s <> "@" andalso Symbol.is_regular s)) >> flat;

val scan_antiq_body =
  Scan.trace (Symbol_Pos.scan_string_qq err_prefix || Symbol_Pos.scan_string_bq err_prefix) >> #2 ||
  Scan.trace (Symbol_Pos.scan_cartouche err_prefix) >> #2 ||
  Scan.one (fn (s, _) => s <> "}" andalso Symbol.is_regular s) >> single;

in

val scan_antiq =
  Symbol_Pos.scan_pos -- ($$ "@" |-- $$ "{" |--
    Symbol_Pos.!!! (fn () => err_prefix ^ "missing closing brace")
      (Scan.repeat scan_antiq_body -- ($$ "}" |-- Symbol_Pos.scan_pos)))
  >> (fn (pos1, (body, pos2)) => (flat body, Position.range pos1 pos2));

val scan_antiquote = scan_antiq >> Antiq || scan_txt >> Text;

end;


(* read *)

fun read (syms, pos) =
  (case Scan.read Symbol_Pos.stopper (Scan.repeat scan_antiquote) syms of
    SOME xs => (Position.reports_text (reports_of (K []) xs); xs)
  | NONE => error ("Malformed quotation/antiquotation source" ^ Position.here pos));

end;
