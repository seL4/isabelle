(*  Title:      Pure/Isar/antiquote.ML
    Author:     Markus Wenzel, TU Muenchen

Text with antiquotations of inner items (terms, types etc.).
*)

signature ANTIQUOTE =
sig
  datatype antiquote =
    Text of string | Antiq of SymbolPos.T list * Position.T |
    Open of Position.T | Close of Position.T
  val is_antiq: antiquote -> bool
  val read: SymbolPos.T list * Position.T -> antiquote list
  val read_antiq: Scan.lexicon -> (OuterLex.token list -> 'a * OuterLex.token list) ->
    SymbolPos.T list * Position.T -> 'a
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

datatype antiquote =
  Text of string |
  Antiq of SymbolPos.T list * Position.T |
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
  SymbolPos.scan_pos -- ($$$ "@" |-- $$$ "{" |--
    T.!!! "missing closing brace of antiquotation"
      (Scan.repeat scan_ant -- ($$$ "}" |-- SymbolPos.scan_pos)))
  >> (fn (pos1, (body, pos2)) => Antiq (flat body, Position.encode_range (pos1, pos2)));

in

val scan_antiquote =
 (Scan.repeat1 scan_txt >> (Text o SymbolPos.content o flat) ||
  scan_antiq ||
  SymbolPos.scan_pos --| $$$ "\\<lbrace>" >> Open ||
  SymbolPos.scan_pos --| $$$ "\\<rbrace>" >> Close);

end;


(* read *)

fun report_antiq (Antiq (_, pos)) = Position.report Markup.antiq pos
  | report_antiq _ = ();

fun read ([], _) = []
  | read (syms, pos) =
      (case Scan.read SymbolPos.stopper (Scan.repeat scan_antiquote) syms of
        SOME xs => (List.app report_antiq xs; check_nesting xs; xs)
      | NONE => error ("Malformed quotation/antiquotation source" ^ Position.str_of pos));


(* read_antiq *)

fun read_antiq lex scan (syms, pos) =
  let
    fun err msg = cat_error msg ("Malformed antiquotation" ^ Position.str_of pos ^ ":\n" ^
      "@{" ^ SymbolPos.content syms ^ "}");

    val res =
      Source.of_list syms
      |> T.source' {do_recover = NONE} (K (lex, Scan.empty_lexicon))
      |> T.source_proper
      |> Source.source T.stopper (Scan.error (Scan.bulk scan)) NONE
      |> Source.exhaust;
  in (case res of [x] => x | _ => err "") handle ERROR msg => err msg end;

end;
