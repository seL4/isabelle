(*  Title:      Pure/Isar/comment.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Internal markup of formal comments -- mostly dummy.
*)

signature COMMENT =
sig
  type text
  val string_of: text -> string
  val plain: string list -> text
  val none: text
  val ignore: 'a * text -> 'a
  type interest
  val interest: int -> interest
  val no_interest: interest
  val default_interest: interest
  val ignore_interest: 'a * interest -> 'a
  val ignore_interest': interest * 'a -> 'a
  exception OUTPUT_FAIL of (string * Position.T) * exn
end;

structure Comment: COMMENT =
struct

(* text *)

datatype text = Text of string list;

fun string_of (Text ss) = cat_lines ss;
val plain = Text;
val none = plain [];

fun ignore (x, _) = x;


(* interest *)

datatype interest = Interest of int;
val interest = Interest;
val no_interest = interest ~1;
val default_interest = interest 0;

fun ignore_interest (x, _) = x;
fun ignore_interest' (_, x) = x;


(* output errors *)

(*note: actually belongs to isar_output.ML*)
exception OUTPUT_FAIL of (string * Position.T) * exn;

end;
