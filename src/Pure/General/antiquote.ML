(*  Title:      Pure/General/antiquote.ML
    Author:     Markus Wenzel, TU Muenchen

Text with antiquotations of inner items (types, terms, theorems etc.).
*)

signature ANTIQUOTE =
sig
  datatype 'a antiquote =
    Text of 'a |
    Antiq of Symbol_Pos.T list * Position.range |
    Open of Position.T |
    Close of Position.T
  val is_text: 'a antiquote -> bool
  val reports_of: ('a -> Position.report list) -> 'a antiquote list -> Position.report list
  val check_nesting: 'a antiquote list -> unit
  val scan_antiq: Symbol_Pos.T list -> (Symbol_Pos.T list * Position.range) * Symbol_Pos.T list
  val scan: Symbol_Pos.T list -> 'a antiquote * Symbol_Pos.T list
  val scan_text: Symbol_Pos.T list -> Symbol_Pos.T list antiquote * Symbol_Pos.T list
  val read: Symbol_Pos.T list * Position.T -> Symbol_Pos.T list antiquote list
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

datatype 'a antiquote =
  Text of 'a |
  Antiq of Symbol_Pos.T list * Position.range |
  Open of Position.T |
  Close of Position.T;

fun is_text (Text _) = true
  | is_text _ = false;


(* reports *)

fun reports_of text =
  maps
    (fn Text x => text x
      | Antiq (_, (pos, _)) => [(pos, Isabelle_Markup.antiq)]
      | Open pos => [(pos, Isabelle_Markup.antiq)]
      | Close pos => [(pos, Isabelle_Markup.antiq)]);


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


(* scan *)

open Basic_Symbol_Pos;

local

val scan_txt =
  $$$ "@" --| Scan.ahead (~$$$ "{") ||
  Scan.one (fn (s, _) => s <> "@" andalso s <> "\\<lbrace>" andalso s <> "\\<rbrace>"
    andalso Symbol.is_regular s) >> single;

val scan_ant =
  Scan.trace (Symbol_Pos.scan_string_qq || Symbol_Pos.scan_string_bq) >> #2 ||
  Scan.one (fn (s, _) => s <> "}" andalso Symbol.is_regular s) >> single;

val scan_open = Symbol_Pos.scan_pos --| $$$ "\\<lbrace>";
val scan_close = Symbol_Pos.scan_pos --| $$$ "\\<rbrace>";

in

val scan_antiq =
  Symbol_Pos.scan_pos -- ($$$ "@" |-- $$$ "{" |--
    Symbol_Pos.!!! (fn () => "missing closing brace of antiquotation")
      (Scan.repeat scan_ant -- ($$$ "}" |-- Symbol_Pos.scan_pos)))
  >> (fn (pos1, (body, pos2)) => (flat body, Position.range pos1 pos2));

fun scan x = (scan_antiq >> Antiq || scan_open >> Open || scan_close >> Close) x;
val scan_text = scan || Scan.repeat1 scan_txt >> (Text o flat);

end;


(* read *)

fun read (syms, pos) =
  (case Scan.read Symbol_Pos.stopper (Scan.repeat scan_text) syms of
    SOME xs => (Position.reports (reports_of (K []) xs); check_nesting xs; xs)
  | NONE => error ("Malformed quotation/antiquotation source" ^ Position.str_of pos));

end;
