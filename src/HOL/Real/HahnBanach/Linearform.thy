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

locale linearform = var V + var f +
  assumes add [iff]: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> f (x + y) = f x + f y"
    and mult [iff]: "x \<in> V \<Longrightarrow> f (a \<cdot> x) = a * f x"

locale (open) vectorspace_linearform =
  vectorspace + linearform

lemma (in vectorspace_linearform) neg [iff]:
  "x \<in> V \<Longrightarrow> f (- x) = - f x"
proof -
  assume x: "x \<in> V"
  hence "f (- x) = f ((- 1) \<cdot> x)" by (simp add: negate_eq1)
  also from x have "... = (- 1) * (f x)" by (rule mult)
  also from x have "... = - (f x)" by simp
  finally show ?thesis .
qed

lemma (in vectorspace_linearform) diff [iff]:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> f (x - y) = f x - f y"
proof -
  assume x: "x \<in> V" and y: "y \<in> V"
  hence "x - y = x + - y" by (rule diff_eq1)
  also have "f ... = f x + f (- y)"
    by (rule add) (simp_all add: x y)
  also from y have "f (- y) = - f y" by (rule neg)
  finally show ?thesis by simp
qed

text {* Every linear form yields @{text 0} for the @{text 0} vector. *}

lemma (in vectorspace_linearform) linearform_zero [iff]:
  "f 0 = 0"
proof -
  have "f 0 = f (0 - 0)" by simp
  also have "\<dots> = f 0 - f 0" by (rule diff) simp_all
  also have "\<dots> = 0" by simp
  finally show ?thesis .
qed

end
