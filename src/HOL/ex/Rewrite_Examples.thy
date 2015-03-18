theory Rewrite_Examples
imports Main "~~/src/HOL/Library/Rewrite"
begin

section \<open>The rewrite Proof Method by Example\<close>

(* This file is intended to give an overview over
   the features of the pattern-based rewrite proof method.

   See also https://www21.in.tum.de/~noschinl/Pattern-2014/
*)

lemma
  fixes a::int and b::int and c::int
  assumes "P (b + a)"
  shows "P (a + b)"
by (rewrite at "a + b" add.commute)
   (rule assms)

(* Selecting a specific subterm in a large, ambiguous term. *)
lemma
  fixes a b c :: int
  assumes "f (a - a + (a - a)) + f (   0    + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite in "f _ + f \<box> = _" diff_self) fact

lemma
  fixes a b c :: int
  assumes "f (a - a +    0   ) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite at "f (_ + \<box>) + f _ = _" diff_self) fact

lemma
  fixes a b c :: int
  assumes "f (  0   + (a - a)) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite in "f (\<box> + _) + _ = _" diff_self) fact

lemma
  fixes a b c :: int
  assumes "f (a - a +    0   ) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite in "f (_ + \<box>) + _ = _" diff_self) fact

lemma
  fixes x y :: nat
  shows"x + y > c \<Longrightarrow> y + x > c"
  by (rewrite at "\<box> > c" add.commute) assumption

(* We can also rewrite in the assumptions.  *)
lemma
  fixes x y :: nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
  by (rewrite in asm add.commute) fact

lemma
  fixes x y :: nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
  by (rewrite in "x + y > c" at asm add.commute) fact

lemma
  fixes x y :: nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
  by (rewrite at "\<box> > c" at asm  add.commute) fact

lemma
  assumes "P {x::int. y + 1 = 1 + x}"
  shows   "P {x::int. y + 1 = x + 1}"
  by (rewrite at "x+1" in "{x::int. \<box> }" add.commute) fact

lemma
  assumes "P {x::int. y + 1 = 1 + x}"
  shows   "P {x::int. y + 1 = x + 1}"
  by (rewrite at "any_identifier_will_work+1" in "{any_identifier_will_work::int. \<box> }" add.commute)
   fact

lemma
  assumes "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. s * t + y - 3)}"
  shows   "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. y + s * t - 3)}"
  by (rewrite at "b + d * e" in "\<lambda>(a, b, c). _ = Q (\<lambda>d e. \<box>)" add.commute) fact


(* Rewriting with conditional rewriting rules works just as well. *)
lemma test_theorem:
  fixes x :: nat
  shows "x \<le> y \<Longrightarrow> x \<ge> y \<Longrightarrow> x = y"
  by (rule Orderings.order_antisym)

lemma
fixes f :: "nat \<Rightarrow> nat"
  assumes "f x \<le> 0" "f x \<ge> 0"
  shows "f x = 0"
  apply (rewrite at "f x" to "0" test_theorem)
  apply fact
  apply fact
  apply (rule refl)
done

(*
   Instantiation.

   Since all rewriting is now done via conversions,
   instantiation becomes fairly easy to do.
*)

(* We first introduce a function f and an extended
   version of f that is annotated with an invariant. *)
fun f :: "nat \<Rightarrow> nat" where "f n = n"
definition "f_inv (I :: nat \<Rightarrow> bool) n \<equiv> f n"

lemma annotate_f: "f = f_inv I"
  by (simp add: f_inv_def fun_eq_iff)

(* We have a lemma with a bound variable n, and
   want to add an invariant to f. *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>_. True) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  by (rewrite to "f_inv (\<lambda>_. True)" annotate_f) fact

(* We can also add an invariant that contains the variable n bound in the outer context.
   For this, we need to bind this variable to an identifier. *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  by (rewrite in "\<lambda>n. \<box>" to "f_inv (\<lambda>x. n < x + 1)" annotate_f) fact

(* Any identifier will work *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  by (rewrite in "\<lambda>abc. \<box>" to "f_inv (\<lambda>x. abc < x + 1)" annotate_f) fact

(* The "for" keyword. *)
lemma
  assumes "P (2 + 1)"
  shows "\<And>x y. P (1 + 2 :: nat)"
by (rewrite in "P (1 + 2)" at for (x) add.commute) fact

lemma
  assumes "\<And>x y. P (y + x)"
  shows "\<And>x y. P (x + y :: nat)"
by (rewrite in "P (x + _)" at for (x y) add.commute) fact

lemma
  assumes "\<And>x y z. y + x + z = z + y + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (rewrite at "x + y" in "x + y + z" in concl at for (x y z) add.commute) fact

lemma
  assumes "\<And>x y z. z + (x + y) = z + y + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (rewrite at "(_ + y) + z" in concl at for (y z) add.commute) fact

lemma
  assumes "\<And>x y z. x + y + z = y + z + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (rewrite at "\<box> + _" at "_ = \<box>" in concl at for () add.commute) fact

(* The all-keyword can be used anywhere in the pattern where there is an \<And>-Quantifier. *)
lemma
  assumes "(\<And>(x::int). x < 1 + x)"
  and     "(x::int) + 1 > x"
  shows   "(\<And>(x::int). x + 1 > x) \<Longrightarrow> (x::int) + 1 > x"
by (rewrite at "x + 1" in for (x) at asm add.commute)
   (rule assms)

end

