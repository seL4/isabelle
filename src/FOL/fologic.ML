(*  Title:      FOL/fologic.ML
    Author:     Lawrence C Paulson

Abstract syntax operations for FOL.
*)

signature FOLOGIC =
sig
  val mk_conj: term * term -> term
  val mk_disj: term * term -> term
  val mk_imp: term * term -> term
  val dest_imp: term -> term * term
  val dest_conj: term -> term list
  val mk_iff: term * term -> term
  val dest_iff: term -> term * term
  val mk_all: string * typ -> term -> term
  val mk_exists: string * typ -> term -> term
  val mk_eq: term * term -> term
  val dest_eq: term -> term * term
end;

structure FOLogic: FOLOGIC =
struct

fun mk_conj (t1, t2) = \<^Const>\<open>conj for t1 t2\<close>
and mk_disj (t1, t2) = \<^Const>\<open>disj for t1 t2\<close>
and mk_imp (t1, t2) = \<^Const>\<open>imp for t1 t2\<close>
and mk_iff (t1, t2) = \<^Const>\<open>iff for t1 t2\<close>;

val dest_imp = \<^Const_fn>\<open>imp for A B => \<open>(A, B)\<close>\<close>;

fun dest_conj \<^Const_>\<open>conj for t t'\<close> = t :: dest_conj t'
  | dest_conj t = [t];

val dest_iff = \<^Const_fn>\<open>iff for A B => \<open>(A, B)\<close>\<close>;

fun mk_eq (t, u) =
  let val T = fastype_of t
  in \<^Const>\<open>eq T for t u\<close> end;

val dest_eq = \<^Const_fn>\<open>eq _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>;

fun mk_all (x, T) P = \<^Const>\<open>All T for \<open>absfree (x, T) P\<close>\<close>;
fun mk_exists (x, T) P = \<^Const>\<open>Ex T for \<open>absfree (x, T) P\<close>\<close>;

end;
