(*  Title:      FOL/fologic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson

Abstract syntax operations for FOL.
*)

signature FOLOGIC =
sig
  val oT		: typ
  val mk_Trueprop	: term -> term
  val atomic_Trueprop	: string -> term
  val dest_Trueprop	: term -> term
  val conj		: term
  val disj		: term
  val imp		: term
  val mk_conj		: term * term -> term
  val mk_disj		: term * term -> term
  val mk_imp		: term * term -> term
  val dest_imp	       	: term -> term*term
  val all_const		: typ -> term
  val mk_all		: term * term -> term
  val exists_const	: typ -> term
  val mk_exists		: term * term -> term
  val eq_const		: typ -> term
  val mk_eq		: term * term -> term
  val dest_eq 		: term -> term*term
end;


structure FOLogic: FOLOGIC =
struct

val oT = Type("o",[]);

val Trueprop = Const("Trueprop", oT-->propT);

fun mk_Trueprop P = Trueprop $ P;

fun atomic_Trueprop x = mk_Trueprop (Free (x, oT));

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);

(** Logical constants **)

val conj = Const("op &", [oT,oT]--->oT)
and disj = Const("op |", [oT,oT]--->oT)
and imp = Const("op -->", [oT,oT]--->oT);

fun mk_conj (t1, t2) = conj $ t1 $ t2
and mk_disj (t1, t2) = disj $ t1 $ t2
and mk_imp (t1, t2) = imp $ t1 $ t2;

fun dest_imp (Const("op -->",_) $ A $ B) = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

fun eq_const T = Const ("op =", [T, T] ---> oT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun dest_eq (Const ("op =", _) $ lhs $ rhs) = (lhs, rhs)
  | dest_eq t = raise TERM ("dest_eq", [t])

fun all_const T = Const ("All", [T --> oT] ---> oT);
fun mk_all (Free(x,T),P) = all_const T $ (absfree (x,T,P));

fun exists_const T = Const ("Ex", [T --> oT] ---> oT);
fun mk_exists (Free(x,T),P) = exists_const T $ (absfree (x,T,P));

end;
