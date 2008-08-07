(*  Title:      Pure/Isar/antiquote.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Text with antiquotations of inner items (terms, types etc.).
*)

signature ANTIQUOTE =
sig
  datatype antiquote =
    Text of string | Antiq of (string * Position.T) * Position.T |
    Open of Position.T | Close of Position.T
  val is_antiq: antiquote -> bool
  val read: string * Position.T -> antiquote list
  val read_arguments: Scan.lexicon -> (OuterLex.token list -> 'a * OuterLex.token list) ->
    string * Position.T -> 'a
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

datatype antiquote =
  Text of string |
  Antiq of (string * Position.T) * Position.T (*text, inner position, outer position*) |
  Open of Position.T |
  Close of Position.T;

fun is_antiq (Text _) = false
  | is_antiq _ = true;


(* check_nesting *)

fun err_unbalanced pos =
  error ("Unbalanced antiquotation block parentheses" ^ Position.str_of pos);

fun check_nesting antiqs =
  let
    fun check [] [] = ()
      | check [] (pos :: _) = err_unbalanced pos
      | check (Open pos :: ants) ps = check ants (pos :: ps)
      | check (Close pos :: _) [] = err_unbalanced pos
      | check (Close _ :: ants) (_ :: ps) = check ants ps
      | check (_ :: ants) ps = check ants ps;
  in check antiqs [] end;


(* scan_antiquote *)

open BasicSymbolPos;
structure T = OuterLex;

local

val scan_txt =
  $$$ "@" --| Scan.ahead (~$$$ "{") ||
  Scan.one (fn (s, _) => s <> "@" andalso s <> "\\<lbrace>" andalso s <> "\\<rbrace>"
    andalso Symbol.is_regular s) >> single;

val scan_ant =
  T.scan_quoted ||
  Scan.one (fn (s, _) => s <> "}" andalso Symbol.is_regular s) >> single;

val scan_antiq =
  SymbolPos.scan_position -- ($$$ "@" |-- $$$ "{" |--
    T.!!! "missing closing brace of antiquotation"
      (SymbolPos.scan_position -- Scan.repeat scan_ant -- SymbolPos.scan_position --
        ($$$ "}" |-- SymbolPos.scan_position)))
  >> (fn (pos1, (((pos2, body), pos3), pos4)) =>
    Antiq ((implode (map symbol (flat body)),
      Position.encode_range (pos2, pos3)), Position.encode_range (pos1, pos4)));

in

val scan_antiquote = T.!!! "malformed quotation/antiquotation"
 (Scan.repeat1 scan_txt >> (Text o implode o map symbol o flat) ||
  scan_antiq ||
  SymbolPos.scan_position --| $$$ "\\<lbrace>" >> Open ||
  SymbolPos.scan_position --| $$$ "\\<rbrace>" >> Close);

end;


(* read *)

fun read ("", _) = []
  | read (s, pos) =
      (case Scan.read SymbolPos.stopper (Scan.bulk scan_antiquote) (SymbolPos.explode (s, pos)) of
        SOME xs => (check_nesting xs; xs)
      | NONE => error ("Malformed quotation/antiquotation source" ^ Position.str_of pos));


(* scan_arguments *)

fun read_arguments lex scan (s, pos) =
  let
    fun err msg = cat_error msg
      ("Malformed antiquotation: " ^ quote ("@{" ^ s ^ "}") ^ Position.str_of pos);

    val res =
      Source.of_string s
      |> Symbol.source false
      |> T.source NONE (K (lex, Scan.empty_lexicon)) pos
      |> T.source_proper
      |> Source.source T.stopper (Scan.error (Scan.bulk scan)) NONE
      |> Source.exhaust;
  in (case res of [x] => x | _ => err "") handle ERROR msg => err msg end;

end;
