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
consts norm :: "'a::norm \<Rightarrow> real" ("\<parallel>_\<parallel>")

axclass real_normed_vector < real_vector, norm
  norm_ge_zero [simp]: "0 \<le> \<parallel>x\<parallel>"
  norm_eq_zero [simp]: "(\<parallel>x\<parallel> = 0) = (x = 0)"
  norm_triangle_ineq: "\<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
  norm_scaleR: "\<parallel>a *# x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>"

axclass real_normed_algebra < real_normed_vector, real_algebra
  norm_mult_ineq: "\<parallel>x * y\<parallel> \<le> \<parallel>x\<parallel> * \<parallel>y\<parallel>"

axclass real_normed_div_algebra
          < real_normed_vector, real_algebra, division_ring
  norm_mult: "\<parallel>x * y\<parallel> = \<parallel>x\<parallel> * \<parallel>y\<parallel>"
  norm_one [simp]: "\<parallel>1\<parallel> = 1"

instance real_normed_div_algebra < real_normed_algebra
by (intro_classes, simp add: norm_mult)

lemma norm_zero [simp]: "\<parallel>0::'a::real_normed_vector\<parallel> = 0"
by simp

lemma zero_less_norm_iff [simp]:
  fixes x :: "'a::real_normed_vector" shows "(0 < \<parallel>x\<parallel>) = (x \<noteq> 0)"
by (simp add: order_less_le)

lemma norm_minus_cancel [simp]:
  fixes x :: "'a::real_normed_vector" shows "\<parallel>- x\<parallel> = \<parallel>x\<parallel>"
proof -
  have "\<parallel>- x\<parallel> = \<parallel>- 1 *# x\<parallel>"
    by (simp only: scaleR_minus_left scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * \<parallel>x\<parallel>"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

lemma norm_minus_commute:
  fixes a b :: "'a::real_normed_vector" shows "\<parallel>a - b\<parallel> = \<parallel>b - a\<parallel>"
proof -
  have "\<parallel>a - b\<parallel> = \<parallel>-(a - b)\<parallel>" by (simp only: norm_minus_cancel)
  also have "\<dots> = \<parallel>b - a\<parallel>" by simp
  finally show ?thesis .
qed

lemma norm_triangle_ineq2:
  fixes a :: "'a::real_normed_vector" shows "\<parallel>a\<parallel> - \<parallel>b\<parallel> \<le> \<parallel>a - b\<parallel>"
proof -
  have "\<parallel>a - b + b\<parallel> \<le> \<parallel>a - b\<parallel> + \<parallel>b\<parallel>"
    by (rule norm_triangle_ineq)
  also have "(a - b + b) = a"
    by simp
  finally show ?thesis
    by (simp add: compare_rls)
qed

lemma norm_triangle_ineq4:
  fixes a :: "'a::real_normed_vector" shows "\<parallel>a - b\<parallel> \<le> \<parallel>a\<parallel> + \<parallel>b\<parallel>"
proof -
  have "\<parallel>a - b\<parallel> = \<parallel>a + - b\<parallel>"
    by (simp only: diff_minus)
  also have "\<dots> \<le> \<parallel>a\<parallel> + \<parallel>- b\<parallel>"
    by (rule norm_triangle_ineq)
  finally show ?thesis
    by simp
qed

lemma nonzero_norm_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "a \<noteq> 0 \<Longrightarrow> \<parallel>inverse a\<parallel> = inverse \<parallel>a\<parallel>"
apply (rule inverse_unique [symmetric])
apply (simp add: norm_mult [symmetric])
done

lemma norm_inverse:
  fixes a :: "'a::{real_normed_div_algebra,division_by_zero}"
  shows "\<parallel>inverse a\<parallel> = inverse \<parallel>a\<parallel>"
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
  real_norm_def: "\<parallel>r\<parallel> \<equiv> \<bar>r\<bar>"

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
