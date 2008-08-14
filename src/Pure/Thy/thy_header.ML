(*  Title:      Pure/Thy/thy_header.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory headers -- independent of outer syntax.
*)

signature THY_HEADER =
sig
  val args: OuterLex.token list ->
    (string * string list * (string * bool) list) * OuterLex.token list
  val read: Position.T -> (string, 'a) Source.source -> string * string list * (string * bool) list
end;

structure ThyHeader: THY_HEADER =
struct

structure T = OuterLex;
structure P = OuterParse;


(* keywords *)

val headerN = "header";
val theoryN = "theory";
val importsN = "imports";
val usesN = "uses";
val beginN = "begin";

val header_lexicon = Scan.make_lexicon
  (map Symbol.explode ["%", "(", ")", ";", beginN, headerN, importsN, theoryN, usesN]);


(* header args *)

val file = (P.$$$ "(" |-- P.!!! (P.name --| P.$$$ ")")) >> rpair false || P.name >> rpair true;
val uses = Scan.optional (P.$$$ usesN |-- P.!!! (Scan.repeat1 file)) [];

val args =
  P.name -- (P.$$$ importsN |-- P.!!! (Scan.repeat1 P.name -- uses --| P.$$$ beginN))
  >> P.triple2;


(* read header *)

val header =
  (P.$$$ headerN -- P.tags) |-- (P.!!! (P.doc_source -- Scan.repeat P.semicolon --
    (P.$$$ theoryN -- P.tags) |-- args)) ||
  (P.$$$ theoryN -- P.tags) |-- P.!!! args;

fun read pos src =
  let val res =
    src
    |> Symbol.source {do_recover = false}
    |> T.source {do_recover = NONE} (fn () => (header_lexicon, Scan.empty_lexicon)) pos
    |> T.source_proper
    |> Source.source T.stopper (Scan.single (Scan.error (P.!!! header))) NONE
    |> Source.get_single;
  in
    (case res of SOME (x, _) => x
    | NONE => error ("Unexpected end of input" ^ Position.str_of pos))
  end;

end;
