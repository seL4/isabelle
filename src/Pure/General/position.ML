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

val none = Pos (None, None);
fun line n = Pos (Some n, None);
fun name s = Pos (None, Some s);
fun line_name n s = Pos (Some n, Some s);


(* increment *)

fun inc (pos as Pos (None, _)) = pos
  | inc (Pos (Some n, opt_s)) = Pos (Some (n + 1), opt_s);


(* str_of *)

fun str_of (Pos (None, None)) = ""
  | str_of (Pos (Some n, None)) = " (line " ^ string_of_int n ^ ")"
  | str_of (Pos (None, Some s)) = " (" ^ s ^ ")"
  | str_of (Pos (Some n, Some s)) = " (line " ^ string_of_int n ^ " of " ^ s ^ ")";


end;
