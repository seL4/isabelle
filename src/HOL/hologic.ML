(*  Title:      HOL/hologic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

Abstract syntax operations for HOL.
*)

signature HOLOGIC =
sig
  val termC: class
  val termS: sort
  val termTVar: typ
  val boolT: typ
  val mk_setT: typ -> typ
  val dest_setT: typ -> typ
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val conj: term
  val disj: term
  val imp: term
  val eq_const: typ -> term
  val all_const: typ -> term
  val exists_const: typ -> term
  val Collect_const: typ -> term
  val mk_eq: term * term -> term
  val mk_all: string * typ * term -> term
  val mk_exists: string * typ * term -> term
  val mk_Collect: string * typ * term -> term
  val mk_mem: term * term -> term
end;

structure HOLogic: HOLOGIC =
struct

(* classes *)

val termC: class = "term";
val termS: sort = [termC];


(* types *)

val termTVar = TVar (("'a", 0), termS);

val boolT = Type ("bool", []);

fun mk_setT T = Type ("set", [T]);

fun dest_setT (Type ("set", [T])) = T
  | dest_setT T = raise_type "dest_setT: set type expected" [T] [];


(* terms *)

val Trueprop = Const ("Trueprop", boolT --> propT);

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
  | dest_Trueprop t = raise_term "dest_Trueprop" [t];


val conj = Const ("op &", [boolT, boolT] ---> boolT)
and disj = Const ("op |", [boolT, boolT] ---> boolT)
and imp = Const ("op -->", [boolT, boolT] ---> boolT);

fun eq_const T = Const ("op =", [T, T] ---> boolT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun all_const T = Const ("All", [T --> boolT] ---> boolT);
fun mk_all (x, T, P) = all_const T $ absfree (x, T, P);

fun exists_const T = Const ("Ex", [T --> boolT] ---> boolT);
fun mk_exists (x, T, P) = exists_const T $ absfree (x, T, P);

fun Collect_const T = Const ("Collect", [T --> boolT] ---> mk_setT T);
fun mk_Collect (a, T, t) = Collect_const T $ absfree (a, T, t);

fun mk_mem (x, A) =
  let val setT = fastype_of A in
    Const ("op :", [dest_setT setT, setT] ---> boolT) $ x $ A
  end;


end;

