(*  Title:      Pure/Interface/isamode.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Configuration for David Aspinall's Isamode.
*)

signature ISAMODE =
sig
  val setup: (theory -> theory) list
  val init: bool -> unit
end;

structure Isamode: ISAMODE =
struct

(** compile-time theory setup **)

(* token translations *)

val isamodeN = "Isamode";

local

val end_tag = "\^A0";
val tclass_tag = "\^A1";
val tfree_tag = "\^A2";
val tvar_tag = "\^A3";
val free_tag = "\^A4";
val bound_tag = "\^A5";
val var_tag = "\^A6";

fun tagit p x = (p ^ x ^ end_tag, real (size x));

in

val isamode_trans =
 Syntax.tokentrans_mode isamodeN
  [("class", tagit tclass_tag),
   ("tfree", tagit tfree_tag),
   ("tvar", tagit tvar_tag),
   ("free", tagit free_tag),
   ("bound", tagit bound_tag),
   ("var", tagit var_tag)];

end;


(* setup *)

val setup = [Theory.add_tokentrfuns isamode_trans];



(** run-time initialization **)

fun init isamode =
  if isamode then print_mode := isamodeN :: ! print_mode else ();


end;
