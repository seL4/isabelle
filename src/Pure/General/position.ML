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
  val inc: T -> T
  val str_of: T -> string
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


(* increment *)

fun inc (pos as Pos (NONE, _)) = pos
  | inc (Pos (SOME n, opt_s)) = Pos (SOME (n + 1), opt_s);


(* str_of *)

fun str_of (Pos (NONE, NONE)) = ""
  | str_of (Pos (SOME n, NONE)) = " (line " ^ string_of_int n ^ ")"
  | str_of (Pos (NONE, SOME s)) = " (" ^ s ^ ")"
  | str_of (Pos (SOME n, SOME s)) = " (line " ^ string_of_int n ^ " of " ^ s ^ ")";


end;
