(*  Title:      Pure/Isar/comment.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Formal comments.
*)

signature COMMENT =
sig
  type text
  val plain: string -> text
  val empty: text
  type interest
  val no_interest: interest
  val default_interest: interest
end;

structure Comment: COMMENT =
struct

(** text **)

datatype text = Text of string;
val plain = Text;
val empty = plain "";


(** interest **)

datatype interest = Interest of bool;
val no_interest = Interest false;
val default_interest = Interest true;

end;
