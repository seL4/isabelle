(*  Title:       HOL/Library/Quadratic_Discriminant.thy
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012

Originally from the AFP entry Tarskis_Geometry
*)

section "Roots of real quadratics"

theory Quadratic_Discriminant
imports Complex_Main
begin

definition discrim :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "discrim a b c \<equiv> b\<^sup>2 - 4 * a * c"

lemma complete_square:
  "a \<noteq> 0 \<Longrightarrow> a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> (2 * a * x + b)\<^sup>2 = discrim a b c"
by (simp add: discrim_def) algebra

lemma discriminant_negative:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
    and "discrim a b c < 0"
  shows "a * x\<^sup>2 + b * x + c \<noteq> 0"
  by (metis assms complete_square power2_less_0) 

lemma plus_or_minus_sqrt:
  fixes x y :: real
  assumes "y \<ge> 0"
  shows "x\<^sup>2 = y \<longleftrightarrow> x = sqrt y \<or> x = - sqrt y"
  using assms by fastforce

lemma divide_non_zero:
  fixes x y z :: real
  assumes "x \<noteq> 0"
  shows "x * y = z \<longleftrightarrow> y = z / x"
  by (simp add: assms mult.commute nonzero_eq_divide_eq)

lemma discriminant_nonneg:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
    and "discrim a b c \<ge> 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow>
    x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a)"  (is "?L = ?R")
proof
  assume ?L with assms show ?R
    by (smt (verit, ccfv_threshold) complete_square nonzero_mult_div_cancel_left real_sqrt_abs)
qed (use assms complete_square in auto)

lemma discriminant_zero:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
    and "discrim a b c = 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> x = -b / (2 * a)"
  by (simp add: discriminant_nonneg assms)

theorem discriminant_iff:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow>
    discrim a b c \<ge> 0 \<and>
    (x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
     x = (-b - sqrt (discrim a b c)) / (2 * a))"
  by (smt (verit, best) assms discriminant_negative discriminant_nonneg)

lemma discriminant_nonneg_ex:
  fixes a b c :: real
  assumes "a \<noteq> 0"
    and "discrim a b c \<ge> 0"
  shows "\<exists> x. a * x\<^sup>2 + b * x + c = 0"
  by (auto simp: discriminant_nonneg assms)

lemma discriminant_pos_ex:
  fixes a b c :: real
  assumes "a \<noteq> 0"
    and "discrim a b c > 0"
  shows "\<exists>x y. x \<noteq> y \<and> a * x\<^sup>2 + b * x + c = 0 \<and> a * y\<^sup>2 + b * y + c = 0"
proof -
  let ?x = "(-b + sqrt (discrim a b c)) / (2 * a)"
  let ?y = "(-b - sqrt (discrim a b c)) / (2 * a)"
  from \<open>discrim a b c > 0\<close> have "sqrt (discrim a b c) \<noteq> 0"
    by simp
  then have "sqrt (discrim a b c) \<noteq> - sqrt (discrim a b c)"
    by arith
  with \<open>a \<noteq> 0\<close> have "?x \<noteq> ?y"
    by simp
  moreover from assms have "a * ?x\<^sup>2 + b * ?x + c = 0" and "a * ?y\<^sup>2 + b * ?y + c = 0"
    using discriminant_nonneg [of a b c ?x]
      and discriminant_nonneg [of a b c ?y]
    by simp_all
  ultimately show ?thesis
    by blast
qed

lemma discriminant_pos_distinct:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
    and "discrim a b c > 0"
  shows "\<exists> y. x \<noteq> y \<and> a * y\<^sup>2 + b * y + c = 0"
  by (metis assms discriminant_pos_ex) 

lemma Rats_solution_QE:
  assumes "a \<in> \<rat>" "b \<in> \<rat>" "a \<noteq> 0"
  and "a*x^2 + b*x + c = 0"
  and "sqrt (discrim a b c) \<in> \<rat>"
  shows "x \<in> \<rat>" 
using assms(1,2,5) discriminant_iff[THEN iffD1, OF assms(3,4)] by auto

lemma Rats_solution_QE_converse:
  assumes "a \<in> \<rat>" "b \<in> \<rat>"
  and "a*x^2 + b*x + c = 0"
  and "x \<in> \<rat>"
  shows "sqrt (discrim a b c) \<in> \<rat>"
proof -
  from assms(3) have "discrim a b c = (2*a*x+b)^2" unfolding discrim_def by algebra
  hence "sqrt (discrim a b c) = \<bar>2*a*x+b\<bar>" by (simp)
  thus ?thesis using \<open>a \<in> \<rat>\<close> \<open>b \<in> \<rat>\<close> \<open>x \<in> \<rat>\<close> by (simp)
qed

end
