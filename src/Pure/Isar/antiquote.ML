(*  Title:      Pure/Isar/antiquote.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Text with antiquotations of inner items (terms, types etc.).
*)

signature ANTIQUOTE =
sig
  datatype antiquote = Text of string | Antiq of string * Position.T
  val is_antiq: antiquote -> bool
  val scan_antiquotes: string * Position.T -> antiquote list
  val scan_arguments: Scan.lexicon -> (OuterLex.token list -> 'a * OuterLex.token list) ->
    string * Position.T -> 'a
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

datatype antiquote =
  Text of string |
  Antiq of string * Position.T;

fun is_antiq (Text _) = false
  | is_antiq (Antiq _) = true;


(* scan_antiquote *)

structure T = OuterLex;

local

val scan_txt =
  T.count ($$ "@" --| Scan.ahead (~$$ "{")) ||
  T.count (Scan.one (fn s => s <> "@" andalso Symbol.is_regular s));

fun escape "\\" = "\\\\"
  | escape "\"" = "\\\""
  | escape s = s;

val quote_escape = Library.quote o implode o map escape o Symbol.explode;

val scan_ant =
  T.scan_string >> quote_escape ||
  T.count (Scan.one (fn s => s <> "}" andalso Symbol.is_regular s));

val scan_antiq =
  T.count ($$ "@") |-- T.count ($$ "{") |--
    T.!!! "missing closing brace of antiquotation"
      (Scan.repeat scan_ant >> implode) --| T.count ($$ "}");

in

fun scan_antiquote (pos, ss) = (pos, ss) |>
  (Scan.repeat1 scan_txt >> (Text o implode) ||
    scan_antiq >> (fn s => Antiq (s, pos)));

end;


(* scan_antiquotes *)

fun scan_antiquotes (s, pos) =
  (case Scan.error (Scan.finite' Symbol.stopper (Scan.repeat scan_antiquote))
      (pos, Symbol.explode s) of
    (xs, (_, [])) => xs
  | (_, (pos', ss)) => error ("Malformed quotation/antiquotation source at: " ^
      quote (Symbol.beginning 10 ss) ^ Position.str_of pos'));


(* scan_arguments *)

fun scan_arguments lex antiq (s, pos) =
  let
    fun err msg = cat_error msg
      ("Malformed antiquotation: " ^ quote ("@{" ^ s ^ "}") ^ Position.str_of pos);

    val res =
      Source.of_string s
      |> Symbol.source false
      |> T.source NONE (K (lex, Scan.empty_lexicon)) pos
      |> T.source_proper
      |> Source.source T.stopper (Scan.error (Scan.bulk antiq)) NONE
      |> Source.exhaust;
  in (case res of [x] => x | _ => err "") handle ERROR msg => err msg end;

end;
