(*  Title:      Pure/Isar/comment.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Formal comments.
*)

signature COMMENT =
sig
  type text
  val plain: string -> text
  val none: text
  val ignore: 'a * text -> 'a
  type interest
  val no_interest: interest
  val default_interest: interest
  val ignore_interest: 'a * interest -> 'a
  val ignore_interest': interest * 'a -> 'a
end;

structure Comment: COMMENT =
struct

(** text **)

datatype text = Text of string;
val plain = Text;
val none = plain "";

fun ignore (x, _) = x;



(** interest **)

datatype interest = Interest of bool;
val no_interest = Interest false;
val default_interest = Interest true;

fun ignore_interest (x, _) = x;
fun ignore_interest' (_, x) = x;


end;
