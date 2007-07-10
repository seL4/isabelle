(*  Title:      Pure/General/position.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Source positions.
*)

signature POSITION =
sig
  type T
  val line_of: T -> int option
  val file_of: T -> string option
  val inc: T -> T
  val none: T
  val line: int -> T
  val file: string -> T
  val path: Path.T -> T
  val of_properties: Markup.property list -> T
  val properties_of: T -> Markup.property list
  val str_of: T -> string
end;

structure Position: POSITION =
struct

(* datatype position *)

datatype T =
  Pos of int option * string option;

fun line_of (Pos (opt_n, _)) = opt_n;
fun file_of (Pos (_, opt_s)) = opt_s;

fun inc (pos as Pos (NONE, _)) = pos
  | inc (Pos (SOME n, opt_s)) = Pos (SOME (n + 1), opt_s);

val none = Pos (NONE, NONE);
fun line n = Pos (SOME n, NONE);
fun file s = Pos (SOME 1, SOME s);

val path = file o Path.implode o Path.expand;


(* markup properties *)

fun of_properties ps =
  let
    val lookup = AList.lookup (op =) ps;
    val opt_n =
      (case lookup Markup.lineN of
        SOME s => Int.fromString s
      | NONE => NONE);
    val opt_s = lookup Markup.fileN;
  in Pos (opt_n, opt_s) end;

fun properties_of (Pos (opt_n, opt_s)) =
  (case opt_n of SOME n => [(Markup.lineN, string_of_int n)] | NONE => []) @
  (case opt_s of SOME s => [(Markup.fileN, s)] | NONE => []);


(* str_of *)

fun print (Pos (SOME n, NONE)) = "(line " ^ string_of_int n ^ ")"
  | print (Pos (NONE, SOME s)) = "(" ^ s ^ ")"
  | print (Pos (SOME n, SOME s)) = "(line " ^ string_of_int n ^ " of " ^ quote s ^ ")";

fun str_of (Pos (NONE, NONE)) = ""
  | str_of pos =
      " " ^ Markup.enclose (Markup.properties (properties_of pos) Markup.position) (print pos);

end;
