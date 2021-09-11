(*  Title:      FOL/fologic.ML
    Author:     Lawrence C Paulson

Abstract syntax operations for FOL.
*)

signature FOLOGIC =
sig
  val oT: typ
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val not: term
  val conj: term
  val disj: term
  val imp: term
  val iff: term
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
  val mk_binop: string -> term * term -> term
  val mk_binrel: string -> term * term -> term
  val dest_bin: string -> typ -> term -> term * term
end;


structure FOLogic: FOLOGIC =
struct

val oT = \<^Type>\<open>o\<close>;

val Trueprop = \<^Const>\<open>Trueprop\<close>;

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop \<^Const_>\<open>Trueprop for P\<close> = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);


(* Logical constants *)

val not = \<^Const>\<open>Not\<close>;
val conj = \<^Const>\<open>conj\<close>;
val disj = \<^Const>\<open>disj\<close>;
val imp = \<^Const>\<open>imp\<close>;
val iff = \<^Const>\<open>iff\<close>;

fun mk_conj (t1, t2) = conj $ t1 $ t2
and mk_disj (t1, t2) = disj $ t1 $ t2
and mk_imp (t1, t2) = imp $ t1 $ t2
and mk_iff (t1, t2) = iff $ t1 $ t2;

fun dest_imp \<^Const_>\<open>imp for A B\<close> = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

fun dest_conj \<^Const_>\<open>conj for t t'\<close> = t :: dest_conj t'
  | dest_conj t = [t];

fun dest_iff \<^Const_>\<open>iff for A B\<close> = (A, B)
  | dest_iff  t = raise TERM ("dest_iff", [t]);

fun eq_const T = \<^Const>\<open>eq T\<close>;
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun dest_eq \<^Const_>\<open>eq _ for lhs rhs\<close> = (lhs, rhs)
  | dest_eq t = raise TERM ("dest_eq", [t])

fun all_const T = \<^Const>\<open>All T\<close>;
fun mk_all (Free (x, T), P) = all_const T $ absfree (x, T) P;

fun exists_const T = \<^Const>\<open>Ex T\<close>;
fun mk_exists (Free (x, T), P) = exists_const T $ absfree (x, T) P;


(* binary operations and relations *)

fun mk_binop c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> T) $ t $ u
  end;

fun mk_binrel c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> oT) $ t $ u
  end;

fun dest_bin c T (tm as Const (c', Type ("fun", [T', _])) $ t $ u) =
      if c = c' andalso T = T' then (t, u)
      else raise TERM ("dest_bin " ^ c, [tm])
  | dest_bin c _ tm = raise TERM ("dest_bin " ^ c, [tm]);

end;
