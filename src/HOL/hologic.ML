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
  val dest_imp	       : term -> term*term
  val eq_const: typ -> term
  val all_const: typ -> term
  val exists_const: typ -> term
  val Collect_const: typ -> term
  val mk_eq: term * term -> term
  val mk_all: string * typ * term -> term
  val mk_exists: string * typ * term -> term
  val mk_Collect: string * typ * term -> term
  val mk_mem: term * term -> term
  val mk_binop: string -> term * term -> term
  val mk_binrel: string -> term * term -> term
  val dest_bin: string -> typ -> term -> term * term
  val natT: typ
  val zero: term
  val is_zero: term -> bool
  val mk_Suc: term -> term
  val dest_Suc: term -> term
  val mk_nat: int -> term
  val dest_nat: term -> int
end;


structure HOLogic: HOLOGIC =
struct

(* basics *)

val termC: class = "term";
val termS: sort = [termC];

val termTVar = TVar (("'a", 0), termS);


(* bool and set *)

val boolT = Type ("bool", []);

fun mk_setT T = Type ("set", [T]);

fun dest_setT (Type ("set", [T])) = T
  | dest_setT T = raise TYPE ("dest_setT: set type expected", [T], []);


val Trueprop = Const ("Trueprop", boolT --> propT);

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);


val conj = Const ("op &", [boolT, boolT] ---> boolT)
and disj = Const ("op |", [boolT, boolT] ---> boolT)
and imp = Const ("op -->", [boolT, boolT] ---> boolT);

fun dest_imp (Const("op -->",_) $ A $ B) = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

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


(* binary oprations and relations *)

fun mk_binop c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> T) $ t $ u
  end;

fun mk_binrel c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> boolT) $ t $ u
  end;

fun dest_bin c T (tm as Const (c', Type ("fun", [T', _])) $ t $ u) =
      if c = c' andalso T = T' then (t, u)
      else raise TERM ("dest_bin " ^ c, [tm])
  | dest_bin c _ tm = raise TERM ("dest_bin " ^ c, [tm]);


(* nat *)

val natT = Type ("nat", []);


val zero = Const ("0", natT);

fun is_zero (Const ("0", _)) = true
  | is_zero _ = false;


fun mk_Suc t = Const ("Suc", natT --> natT) $ t;

fun dest_Suc (Const ("Suc", _) $ t) = t
  | dest_Suc t = raise TERM ("dest_Suc", [t]);


fun mk_nat 0 = zero
  | mk_nat n = mk_Suc (mk_nat (n - 1));

fun dest_nat (Const ("0", _)) = 0
  | dest_nat (Const ("Suc", _) $ t) = dest_nat t + 1
  | dest_nat t = raise TERM ("dest_nat", [t]);


end;
