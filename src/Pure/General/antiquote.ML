(*  Title:      Pure/General/antiquote.ML
    Author:     Markus Wenzel, TU Muenchen

Text with antiquotations of inner items (types, terms, theorems etc.).
*)

signature ANTIQUOTE =
sig
  datatype antiquote =
    Text of string | Antiq of Symbol_Pos.T list * Position.T |
    Open of Position.T | Close of Position.T
  val is_antiq: antiquote -> bool
  val read: Symbol_Pos.T list * Position.T -> antiquote list
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

datatype antiquote =
  Text of string |
  Antiq of Symbol_Pos.T list * Position.T |
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

open Basic_Symbol_Pos;

local

val scan_txt =
  $$$ "@" --| Scan.ahead (~$$$ "{") ||
  Scan.one (fn (s, _) => s <> "@" andalso s <> "\\<lbrace>" andalso s <> "\\<rbrace>"
    andalso Symbol.is_regular s) >> single;

val scan_ant =
  Symbol_Pos.scan_quoted ||
  Scan.one (fn (s, _) => s <> "}" andalso Symbol.is_regular s) >> single;

val scan_antiq =
  Symbol_Pos.scan_pos -- ($$$ "@" |-- $$$ "{" |--
    Symbol_Pos.!!! "missing closing brace of antiquotation"
      (Scan.repeat scan_ant -- ($$$ "}" |-- Symbol_Pos.scan_pos)))
  >> (fn (pos1, (body, pos2)) => Antiq (flat body, Position.encode_range (pos1, pos2)));

in

val scan_antiquote =
 (Scan.repeat1 scan_txt >> (Text o Symbol_Pos.content o flat) ||
  scan_antiq ||
  Symbol_Pos.scan_pos --| $$$ "\\<lbrace>" >> Open ||
  Symbol_Pos.scan_pos --| $$$ "\\<rbrace>" >> Close);

end;


(* read *)

fun report_antiq (Antiq (_, pos)) = Position.report Markup.antiq pos
  | report_antiq _ = ();

fun read ([], _) = []
  | read (syms, pos) =
      (case Scan.read Symbol_Pos.stopper (Scan.repeat scan_antiquote) syms of
        SOME xs => (List.app report_antiq xs; check_nesting xs; xs)
      | NONE => error ("Malformed quotation/antiquotation source" ^ Position.str_of pos));

end;
