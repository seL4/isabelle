(*  Title:      Pure/Isar/antiquote.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Text with antiquotations of inner items (terms, types etc.).
*)

signature ANTIQUOTE =
sig
  exception ANTIQUOTE_FAIL of (string * Position.T) * exn
  datatype antiquote = Text of string | Antiq of string * Position.T
  val is_antiq: antiquote -> bool
  val antiquotes_of: string * Position.T -> antiquote list
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

exception ANTIQUOTE_FAIL of (string * Position.T) * exn;

datatype antiquote =
  Text of string |
  Antiq of string * Position.T;

fun is_antiq (Text _) = false
  | is_antiq (Antiq _) = true;


(* scan_antiquote *)

local

structure T = OuterLex;

val scan_txt =
  T.scan_blank ||
  T.keep_line ($$ "@" --| Scan.ahead (Scan.one (not_equal "{"))) ||
  T.keep_line (Scan.one (not_equal "@" andf Symbol.not_sync andf Symbol.not_eof));

fun escape "\\" = "\\\\"
  | escape "\"" = "\\\""
  | escape s = s;

val quote_escape = Library.quote o implode o map escape o Symbol.explode;

val scan_ant =
  T.scan_blank ||
  T.scan_string >> quote_escape ||
  T.keep_line (Scan.one (not_equal "}" andf Symbol.not_sync andf Symbol.not_eof));

val scan_antiq =
  T.keep_line ($$ "@" -- $$ "{") |--
    T.!!! "missing closing brace of antiquotation"
      (Scan.repeat scan_ant >> implode) --| T.keep_line ($$ "}");

in

fun scan_antiquote (pos, ss) = (pos, ss) |>
  (Scan.repeat1 scan_txt >> (Text o implode) ||
    scan_antiq >> (fn s => Antiq (s, pos)));

end;


(* antiquotes_of *)

fun antiquotes_of (s, pos) =
  (case Scan.error (Scan.finite' Symbol.stopper (Scan.repeat scan_antiquote))
      (pos, Symbol.explode s) of
    (xs, (_, [])) => xs
  | (_, (pos', ss)) => error ("Malformed quotation/antiquotation text at: " ^
      quote (Symbol.beginning ss) ^ Position.str_of pos'));


end;
