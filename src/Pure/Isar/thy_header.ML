(*  Title:      Pure/Isar/thy_header.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory headers (old and new-style).
*)

signature THY_HEADER =
sig
  val is_old: (string, 'a) Source.source * Position.T -> bool
  val args: OuterLex.token list ->
    (string * string list * (string * bool) list) * OuterLex.token list
  val scan: (string, 'a) Source.source * Position.T -> string * string list * (string * bool) list
end;

structure ThyHeader: THY_HEADER =
struct

structure T = OuterLex;
structure P = OuterParse;


(* scan header *)

fun scan_header get_lex scan (src, pos) =
  let val res =
    src
    |> Symbol.source false
    |> T.source false (fn () => (get_lex (), Scan.empty_lexicon)) pos
    |> T.source_proper
    |> Source.source T.stopper (Scan.single scan) None
    |> Source.get_single;
  in
    (case res of Some (x, _) => x
    | None => error ("Unexpected end of input" ^ Position.str_of pos))
  end;


(* keywords *)

val headerN = "header";
val theoryN = "theory";

val theory_keyword = P.$$$ theoryN;
val header_keyword = P.$$$ headerN;


(* detect new/old headers *)

val check_header_lexicon = T.make_lexicon [headerN, theoryN];
val check_header = Scan.option (header_keyword || theory_keyword);

fun is_old src_pos =
  Library.is_none (scan_header (K check_header_lexicon) check_header src_pos);


(* scan old/new headers *)

val header_lexicon =
  T.make_lexicon ["(", ")", "+", ":", ";", "=", "files", headerN, theoryN];

val file_name =
  (P.$$$ "(" |-- P.!!! (P.name --| P.$$$ ")")) >> rpair false || P.name >> rpair true;


val args =
  (P.name -- (P.$$$ "=" |-- P.enum1 "+" P.name) --
    Scan.optional (P.$$$ "files" |-- P.!!! (Scan.repeat1 file_name)) [] --|  P.$$$ ":")
  >> (fn ((A, Bs), files) => (A, Bs, files));


val new_header =
  header_keyword |-- (P.!!! (P.text -- Scan.repeat P.semicolon -- theory_keyword |-- args)) ||
  theory_keyword |-- P.!!! args;

val old_header =
  P.!!! (P.group "theory header"
    (P.name -- (P.$$$ "=" |-- P.name -- Scan.repeat (P.$$$ "+" |-- P.name))))
  >> (fn (A, (B, Bs)) => (A, B :: Bs, []: (string * bool) list));

fun scan src_pos =
  (*sadly, old-style headers depend on the current (dynamic!) lexicon*)
  if is_old src_pos then
    scan_header ThySyn.get_lexicon (Scan.error old_header) src_pos
  else scan_header (K header_lexicon) (Scan.error new_header) src_pos;


end;
