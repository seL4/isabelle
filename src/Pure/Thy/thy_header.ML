(*  Title:      Pure/Thy/thy_header.ML
    Author:     Markus Wenzel, TU Muenchen

Theory headers -- independent of outer syntax.
*)

signature THY_HEADER =
sig
  val args: OuterLex.token list ->
    (string * string list * (string * bool) list) * OuterLex.token list
  val read: Position.T -> (string, 'a) Source.source -> string * string list * (string * bool) list
end;

structure Thy_Header: THY_HEADER =
struct

structure T = OuterLex;


(* keywords *)

val headerN = "header";
val theoryN = "theory";
val importsN = "imports";
val usesN = "uses";
val beginN = "begin";

val header_lexicon = Scan.make_lexicon
  (map Symbol.explode ["%", "(", ")", ";", beginN, headerN, importsN, theoryN, usesN]);


(* header args *)

val file_name = Parse.group "file name" Parse.name;
val theory_name = Parse.group "theory name" Parse.name;

val file =
  Parse.$$$ "(" |-- Parse.!!! (file_name --| Parse.$$$ ")") >> rpair false ||
  file_name >> rpair true;

val uses = Scan.optional (Parse.$$$ usesN |-- Parse.!!! (Scan.repeat1 file)) [];

val args =
  theory_name -- (Parse.$$$ importsN |--
    Parse.!!! (Scan.repeat1 theory_name -- uses --| Parse.$$$ beginN))
  >> Parse.triple2;


(* read header *)

val header =
  (Parse.$$$ headerN -- Parse.tags) |--
    (Parse.!!! (Parse.doc_source -- Scan.repeat Parse.semicolon --
      (Parse.$$$ theoryN -- Parse.tags) |-- args)) ||
  (Parse.$$$ theoryN -- Parse.tags) |-- Parse.!!! args;

fun read pos src =
  let val res =
    src
    |> Symbol.source {do_recover = false}
    |> T.source {do_recover = NONE} (fn () => (header_lexicon, Scan.empty_lexicon)) pos
    |> T.source_proper
    |> Source.source T.stopper (Scan.single (Scan.error (Parse.!!! header))) NONE
    |> Source.get_single;
  in
    (case res of SOME (x, _) => x
    | NONE => error ("Unexpected end of input" ^ Position.str_of pos))
  end;

end;
