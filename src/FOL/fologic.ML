(*  Title:      FOL/fologic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson

Abstract syntax operations for FOL.
*)

signature FOLOGIC =
sig
  val oT: typ
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val dest_imp	       : term -> term*term
  val conj: term
  val disj: term
  val imp: term
  val eq_const: typ -> term
  val all_const: typ -> term
  val exists_const: typ -> term
  val mk_eq: term * term -> term
  val mk_all: term * term -> term
  val mk_exists: term * term -> term
end;


structure FOLogic: FOLOGIC =
struct

val oT = Type("o",[]);

val Trueprop = Const("Trueprop", oT-->propT);

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);

(** Logical constants **)

val conj = Const("op &", [oT,oT]--->oT)
and disj = Const("op |", [oT,oT]--->oT)
and imp = Const("op -->", [oT,oT]--->oT);

fun dest_imp (Const("op -->",_) $ A $ B) = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

fun eq_const T = Const ("op =", [T, T] ---> oT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun all_const T = Const ("All", [T --> oT] ---> oT);
fun mk_all (Free(x,T),P) = all_const T $ (absfree (x,T,P));

fun exists_const T = Const ("Ex", [T --> oT] ---> oT);
fun mk_exists (Free(x,T),P) = exists_const T $ (absfree (x,T,P));

end;
