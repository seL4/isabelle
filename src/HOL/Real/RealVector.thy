(*  Title       : RealVector.thy
    ID:         $Id$
    Author      : Brian Huffman
*)

header {* Vector Spaces and Algebras over the Reals *}

theory RealVector
imports RealDef
begin

subsection {* Locale for additive functions *}

locale additive =
  fixes f :: "'a::ab_group_add \<Rightarrow> 'b::ab_group_add"
  assumes add: "f (x + y) = f x + f y"

lemma (in additive) zero: "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "\<dots> = f 0 + f 0" by (rule add)
  finally show "f 0 = 0" by simp
qed

lemma (in additive) minus: "f (- x) = - f x"
proof -
  have "f (- x) + f x = f (- x + x)" by (rule add [symmetric])
  also have "\<dots> = - f x + f x" by (simp add: zero)
  finally show "f (- x) = - f x" by (rule add_right_imp_eq)
qed

lemma (in additive) diff: "f (x - y) = f x - f y"
by (simp add: diff_def add minus)


subsection {* Real vector spaces *}

axclass scaleR < type

consts
  scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a::scaleR" (infixr "*#" 75)

syntax (xsymbols)
  scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a::scaleR" (infixr "*\<^sub>R" 75)

axclass real_vector < scaleR, ab_group_add
  scaleR_right_distrib: "a *# (x + y) = a *# x + a *# y"
  scaleR_left_distrib: "(a + b) *# x = a *# x + b *# x"
  scaleR_assoc: "(a * b) *# x = a *# b *# x"
  scaleR_one [simp]: "1 *# x = x"

axclass real_algebra < real_vector, ring
  mult_scaleR_left: "a *# x * y = a *# (x * y)"
  mult_scaleR_right: "x * a *# y = a *# (x * y)"

lemmas scaleR_scaleR = scaleR_assoc [symmetric]

lemma scaleR_left_commute:
  fixes x :: "'a::real_vector"
  shows "a *# b *# x = b *# a *# x"
by (simp add: scaleR_scaleR mult_commute)

lemma additive_scaleR_right: "additive (\<lambda>x. a *# x :: 'a::real_vector)"
by (rule additive.intro, rule scaleR_right_distrib)

lemma additive_scaleR_left: "additive (\<lambda>a. a *# x :: 'a::real_vector)"
by (rule additive.intro, rule scaleR_left_distrib)

lemmas scaleR_zero_left [simp] =
  additive.zero [OF additive_scaleR_left, standard]

lemmas scaleR_zero_right [simp] =
  additive.zero [OF additive_scaleR_right, standard]

lemmas scaleR_minus_left [simp] =
  additive.minus [OF additive_scaleR_left, standard]

lemmas scaleR_minus_right [simp] =
  additive.minus [OF additive_scaleR_right, standard]

lemmas scaleR_left_diff_distrib =
  additive.diff [OF additive_scaleR_left, standard]

lemmas scaleR_right_diff_distrib =
  additive.diff [OF additive_scaleR_right, standard]


subsection {* Real normed vector spaces *}

axclass norm < type
consts norm :: "'a::norm \<Rightarrow> real"

axclass real_normed_vector < real_vector, norm
  norm_ge_zero [simp]: "0 \<le> norm x"
  norm_eq_zero [simp]: "(norm x = 0) = (x = 0)"
  norm_triangle_ineq: "norm (x + y) \<le> norm x + norm y"
  norm_scaleR: "norm (a *# x) = \<bar>a\<bar> * norm x"

axclass real_normed_algebra < real_normed_vector, real_algebra
  norm_mult_ineq: "norm (x * y) \<le> norm x * norm y"

axclass real_normed_div_algebra
          < real_normed_vector, real_algebra, division_ring
  norm_mult: "norm (x * y) = norm x * norm y"
  norm_one [simp]: "norm 1 = 1"

instance real_normed_div_algebra < real_normed_algebra
by (intro_classes, simp add: norm_mult)

lemma norm_zero [simp]: "norm (0::'a::real_normed_vector) = 0"
by simp

lemma zero_less_norm_iff [simp]:
  fixes x :: "'a::real_normed_vector" shows "(0 < norm x) = (x \<noteq> 0)"
by (simp add: order_less_le)

lemma norm_minus_cancel [simp]:
  fixes x :: "'a::real_normed_vector" shows "norm (- x) = norm x"
proof -
  have "norm (- x) = norm (- 1 *# x)"
    by (simp only: scaleR_minus_left scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * norm x"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

lemma norm_minus_commute:
  fixes a b :: "'a::real_normed_vector" shows "norm (a - b) = norm (b - a)"
proof -
  have "norm (a - b) = norm (- (a - b))"
    by (simp only: norm_minus_cancel)
  also have "\<dots> = norm (b - a)" by simp
  finally show ?thesis .
qed

lemma norm_triangle_ineq2:
  fixes a :: "'a::real_normed_vector"
  shows "norm a - norm b \<le> norm (a - b)"
proof -
  have "norm (a - b + b) \<le> norm (a - b) + norm b"
    by (rule norm_triangle_ineq)
  also have "(a - b + b) = a"
    by simp
  finally show ?thesis
    by (simp add: compare_rls)
qed

lemma norm_triangle_ineq4:
  fixes a :: "'a::real_normed_vector"
  shows "norm (a - b) \<le> norm a + norm b"
proof -
  have "norm (a - b) = norm (a + - b)"
    by (simp only: diff_minus)
  also have "\<dots> \<le> norm a + norm (- b)"
    by (rule norm_triangle_ineq)
  finally show ?thesis
    by simp
qed

lemma nonzero_norm_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
apply (rule inverse_unique [symmetric])
apply (simp add: norm_mult [symmetric])
done

lemma norm_inverse:
  fixes a :: "'a::{real_normed_div_algebra,division_by_zero}"
  shows "norm (inverse a) = inverse (norm a)"
apply (case_tac "a = 0", simp)
apply (erule nonzero_norm_inverse)
done


subsection {* Instances for type @{typ real} *}

instance real :: scaleR ..

defs (overloaded)
  real_scaleR_def: "a *# x \<equiv> a * x"

instance real :: real_algebra
apply (intro_classes, unfold real_scaleR_def)
apply (rule right_distrib)
apply (rule left_distrib)
apply (rule mult_assoc)
apply (rule mult_1_left)
apply (rule mult_assoc)
apply (rule mult_left_commute)
done

instance real :: norm ..

defs (overloaded)
  real_norm_def: "norm r \<equiv> \<bar>r\<bar>"

instance real :: real_normed_div_algebra
apply (intro_classes, unfold real_norm_def real_scaleR_def)
apply (rule abs_ge_zero)
apply (rule abs_eq_0)
apply (rule abs_triangle_ineq)
apply (rule abs_mult)
apply (rule abs_mult)
apply (rule abs_one)
done

end
