(*  Title:      Pure/Isar/comment.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Formal comments.
*)

signature COMMENT =
sig
  type text
  val string_of: text -> string
  val plain: string -> text
  val none: text
  val ignore: 'a * text -> 'a
  type interest
  val interest: int -> interest
  val no_interest: interest
  val default_interest: interest
  val ignore_interest: 'a * interest -> 'a
  val ignore_interest': interest * 'a -> 'a
end;

structure Comment: COMMENT =
struct

(** text **)

datatype text = Text of string;

fun string_of (Text s) = s;
val plain = Text;
val none = plain "";

fun ignore (x, _) = x;



(** interest **)

datatype interest = Interest of int;
val interest = Interest;
val no_interest = interest ~1;
val default_interest = interest 0;

fun ignore_interest (x, _) = x;
fun ignore_interest' (_, x) = x;


end;
