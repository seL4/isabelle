(*  Title:      HOL/Real/HahnBanach/Linearform.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Linearforms *}

theory Linearform = VectorSpace:

text {*
  A \emph{linear form} is a function on a vector space into the reals
  that is additive and multiplicative.
*}

constdefs
  is_linearform :: "'a::{plus, minus, zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  "is_linearform V f \<equiv>
      (\<forall>x \<in> V. \<forall>y \<in> V. f (x + y) = f x + f y) \<and>
      (\<forall>x \<in> V. \<forall>a. f (a \<cdot> x) = a * (f x))"

lemma is_linearformI [intro]:
  "(\<And>x y. x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> f (x + y) = f x + f y) \<Longrightarrow>
    (\<And>x c. x \<in> V \<Longrightarrow> f (c \<cdot> x) = c * f x)
 \<Longrightarrow> is_linearform V f"
 by (unfold is_linearform_def) blast

lemma linearform_add [intro?]:
  "is_linearform V f \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> f (x + y) = f x + f y"
  by (unfold is_linearform_def) blast

lemma linearform_mult [intro?]:
  "is_linearform V f \<Longrightarrow> x \<in> V \<Longrightarrow>  f (a \<cdot> x) = a * (f x)"
  by (unfold is_linearform_def) blast

lemma linearform_neg [intro?]:
  "is_vectorspace V \<Longrightarrow> is_linearform V f \<Longrightarrow> x \<in> V
  \<Longrightarrow> f (- x) = - f x"
proof -
  assume "is_linearform V f"  "is_vectorspace V"  "x \<in> V"
  have "f (- x) = f ((- #1) \<cdot> x)" by (simp! add: negate_eq1)
  also have "... = (- #1) * (f x)" by (rule linearform_mult)
  also have "... = - (f x)" by (simp!)
  finally show ?thesis .
qed

lemma linearform_diff [intro?]:
  "is_vectorspace V \<Longrightarrow> is_linearform V f \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V
  \<Longrightarrow> f (x - y) = f x - f y"
proof -
  assume "is_vectorspace V"  "is_linearform V f"  "x \<in> V"  "y \<in> V"
  have "f (x - y) = f (x + - y)" by (simp! only: diff_eq1)
  also have "... = f x + f (- y)"
    by (rule linearform_add) (simp!)+
  also have "f (- y) = - f y" by (rule linearform_neg)
  finally show "f (x - y) = f x - f y" by (simp!)
qed

text {* Every linear form yields @{text 0} for the @{text 0} vector. *}

lemma linearform_zero [intro?, simp]:
  "is_vectorspace V \<Longrightarrow> is_linearform V f \<Longrightarrow> f 0 = #0"
proof -
  assume "is_vectorspace V"  "is_linearform V f"
  have "f 0 = f (0 - 0)" by (simp!)
  also have "... = f 0 - f 0"
    by (rule linearform_diff) (simp!)+
  also have "... = #0" by simp
  finally show "f 0 = #0" .
qed

end
