(*  Title:      Pure/General/position.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Input positions.
*)

signature POSITION =
sig
  type T
  val none: T
  val line: int -> T
  val name: string -> T
  val line_name: int -> string -> T
  val line_of: T -> int option
  val name_of: T -> string option
  val inc: T -> T
  val str_of: T -> string
  val of_properties: Markup.property list -> T
  val properties_of: T -> Markup.property list
end;

structure Position: POSITION =
struct


(* datatype position *)

datatype T =
  Pos of int option * string option;

val none = Pos (NONE, NONE);
fun line n = Pos (SOME n, NONE);
fun name s = Pos (NONE, SOME s);
fun line_name n s = Pos (SOME n, SOME s);

fun line_of (Pos (opt_n, _)) = opt_n;
fun name_of (Pos (_, opt_s)) = opt_s;


(* increment *)

fun inc (pos as Pos (NONE, _)) = pos
  | inc (Pos (SOME n, opt_s)) = Pos (SOME (n + 1), opt_s);


(* str_of *)

fun str_of (Pos (NONE, NONE)) = ""
  | str_of (Pos (SOME n, NONE)) = " (line " ^ string_of_int n ^ ")"
  | str_of (Pos (NONE, SOME s)) = " (" ^ s ^ ")"
  | str_of (Pos (SOME n, SOME s)) = " (line " ^ string_of_int n ^ " of " ^ s ^ ")";


(* markup properties *)

fun of_properties ps =
  let
    val lookup = AList.lookup (op =) ps;
    val opt_n =
      (case lookup Markup.pos_lineN of
        SOME s => Int.fromString s
      | NONE => NONE);
    val opt_s = lookup Markup.pos_nameN;
  in Pos (opt_n, opt_s) end;

fun properties_of (Pos (opt_n, opt_s)) =
  (case opt_n of SOME n => [(Markup.pos_lineN, string_of_int n)] | NONE => []) @
  (case opt_s of SOME s => [(Markup.pos_nameN, s)] | NONE => []);

end;
