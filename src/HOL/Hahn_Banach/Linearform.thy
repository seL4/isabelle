(*  Title:      HOL/Hahn_Banach/Linearform.thy
    Author:     Gertrud Bauer, TU Munich
*)

header {* Linearforms *}

theory Linearform
imports Vector_Space
begin

text {*
  A \emph{linear form} is a function on a vector space into the reals
  that is additive and multiplicative.
*}

locale linearform =
  fixes V :: "'a\<Colon>{minus, plus, zero, uminus} set" and f
  assumes add [iff]: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> f (x + y) = f x + f y"
    and mult [iff]: "x \<in> V \<Longrightarrow> f (a \<cdot> x) = a * f x"

declare linearform.intro [intro?]

lemma (in linearform) neg [iff]:
  assumes "vectorspace V"
  shows "x \<in> V \<Longrightarrow> f (- x) = - f x"
proof -
  interpret vectorspace V by fact
  assume x: "x \<in> V"
  then have "f (- x) = f ((- 1) \<cdot> x)" by (simp add: negate_eq1)
  also from x have "\<dots> = (- 1) * (f x)" by (rule mult)
  also from x have "\<dots> = - (f x)" by simp
  finally show ?thesis .
qed

lemma (in linearform) diff [iff]:
  assumes "vectorspace V"
  shows "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> f (x - y) = f x - f y"
proof -
  interpret vectorspace V by fact
  assume x: "x \<in> V" and y: "y \<in> V"
  then have "x - y = x + - y" by (rule diff_eq1)
  also have "f \<dots> = f x + f (- y)" by (rule add) (simp_all add: x y)
  also have "f (- y) = - f y" using `vectorspace V` y by (rule neg)
  finally show ?thesis by simp
qed

text {* Every linear form yields @{text 0} for the @{text 0} vector. *}

lemma (in linearform) zero [iff]:
  assumes "vectorspace V"
  shows "f 0 = 0"
proof -
  interpret vectorspace V by fact
  have "f 0 = f (0 - 0)" by simp
  also have "\<dots> = f 0 - f 0" using `vectorspace V` by (rule diff) simp_all
  also have "\<dots> = 0" by simp
  finally show ?thesis .
qed

end
