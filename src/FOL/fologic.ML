(*  Title:      FOL/fologic.ML
    Author:     Lawrence C Paulson

Abstract syntax operations for FOL.
*)

signature FOLOGIC =
sig
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val mk_conj: term * term -> term
  val mk_disj: term * term -> term
  val mk_imp: term * term -> term
  val dest_imp: term -> term * term
  val dest_conj: term -> term list
  val mk_iff: term * term -> term
  val dest_iff: term -> term * term
  val all_const: typ -> term
  val mk_all: term * term -> term
  val exists_const: typ -> term
  val mk_exists: term * term -> term
  val eq_const: typ -> term
  val mk_eq: term * term -> term
  val dest_eq: term -> term * term
end;


structure FOLogic: FOLOGIC =
struct

fun mk_Trueprop P = \<^Const>\<open>Trueprop for P\<close>;

val dest_Trueprop = \<^Const_fn>\<open>Trueprop for P => P\<close>;

fun mk_conj (t1, t2) = \<^Const>\<open>conj for t1 t2\<close>
and mk_disj (t1, t2) = \<^Const>\<open>disj for t1 t2\<close>
and mk_imp (t1, t2) = \<^Const>\<open>imp for t1 t2\<close>
and mk_iff (t1, t2) = \<^Const>\<open>iff for t1 t2\<close>;

val dest_imp = \<^Const_fn>\<open>imp for A B => \<open>(A, B)\<close>\<close>;

fun dest_conj \<^Const_>\<open>conj for t t'\<close> = t :: dest_conj t'
  | dest_conj t = [t];

val dest_iff = \<^Const_fn>\<open>iff for A B => \<open>(A, B)\<close>\<close>;

fun eq_const T = \<^Const>\<open>eq T\<close>;
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

val dest_eq = \<^Const_fn>\<open>eq _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>;

fun all_const T = \<^Const>\<open>All T\<close>;
fun mk_all (Free (x, T), P) = all_const T $ absfree (x, T) P;

fun exists_const T = \<^Const>\<open>Ex T\<close>;
fun mk_exists (Free (x, T), P) = exists_const T $ absfree (x, T) P;

end;
