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
proof -
  have "(2 * a * x + b)\<^sup>2 \<ge> 0"
    by simp
  with \<open>discrim a b c < 0\<close> have "(2 * a * x + b)\<^sup>2 \<noteq> discrim a b c"
    by arith
  with complete_square and \<open>a \<noteq> 0\<close> show "a * x\<^sup>2 + b * x + c \<noteq> 0"
    by simp
qed

lemma plus_or_minus_sqrt:
  fixes x y :: real
  assumes "y \<ge> 0"
  shows "x\<^sup>2 = y \<longleftrightarrow> x = sqrt y \<or> x = - sqrt y"
proof
  assume "x\<^sup>2 = y"
  then have "sqrt (x\<^sup>2) = sqrt y"
    by simp
  then have "sqrt y = \<bar>x\<bar>"
    by simp
  then show "x = sqrt y \<or> x = - sqrt y"
    by auto
next
  assume "x = sqrt y \<or> x = - sqrt y"
  then have "x\<^sup>2 = (sqrt y)\<^sup>2 \<or> x\<^sup>2 = (- sqrt y)\<^sup>2"
    by auto
  with \<open>y \<ge> 0\<close> show "x\<^sup>2 = y"
    by simp
qed

lemma divide_non_zero:
  fixes x y z :: real
  assumes "x \<noteq> 0"
  shows "x * y = z \<longleftrightarrow> y = z / x"
proof
  show "y = z / x" if "x * y = z"
    using \<open>x \<noteq> 0\<close> that by (simp add: field_simps)
  show "x * y = z" if "y = z / x"
    using \<open>x \<noteq> 0\<close> that by simp
qed

lemma discriminant_nonneg:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
    and "discrim a b c \<ge> 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow>
    x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a)"
proof -
  from complete_square and plus_or_minus_sqrt and assms
  have "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow>
    (2 * a) * x + b = sqrt (discrim a b c) \<or>
    (2 * a) * x + b = - sqrt (discrim a b c)"
    by simp
  also have "\<dots> \<longleftrightarrow> (2 * a) * x = (-b + sqrt (discrim a b c)) \<or>
    (2 * a) * x = (-b - sqrt (discrim a b c))"
    by auto
  also from \<open>a \<noteq> 0\<close> and divide_non_zero [of "2 * a" x]
  have "\<dots> \<longleftrightarrow> x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a)"
    by simp
  finally show "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow>
    x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a)" .
qed

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
proof
  assume "a * x\<^sup>2 + b * x + c = 0"
  with discriminant_negative and \<open>a \<noteq> 0\<close> have "\<not>(discrim a b c < 0)"
    by auto
  then have "discrim a b c \<ge> 0"
    by simp
  with discriminant_nonneg and \<open>a * x\<^sup>2 + b * x + c = 0\<close> and \<open>a \<noteq> 0\<close>
  have "x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
      x = (-b - sqrt (discrim a b c)) / (2 * a)"
    by simp
  with \<open>discrim a b c \<ge> 0\<close>
  show "discrim a b c \<ge> 0 \<and>
    (x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
     x = (-b - sqrt (discrim a b c)) / (2 * a))" ..
next
  assume "discrim a b c \<ge> 0 \<and>
    (x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
     x = (-b - sqrt (discrim a b c)) / (2 * a))"
  then have "discrim a b c \<ge> 0" and
    "x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
     x = (-b - sqrt (discrim a b c)) / (2 * a)"
    by simp_all
  with discriminant_nonneg and \<open>a \<noteq> 0\<close> show "a * x\<^sup>2 + b * x + c = 0"
    by simp
qed

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
proof -
  from discriminant_pos_ex and \<open>a \<noteq> 0\<close> and \<open>discrim a b c > 0\<close>
  obtain w and z where "w \<noteq> z"
    and "a * w\<^sup>2 + b * w + c = 0" and "a * z\<^sup>2 + b * z + c = 0"
    by blast
  show "\<exists>y. x \<noteq> y \<and> a * y\<^sup>2 + b * y + c = 0"
  proof (cases "x = w")
    case True
    with \<open>w \<noteq> z\<close> have "x \<noteq> z"
      by simp
    with \<open>a * z\<^sup>2 + b * z + c = 0\<close> show ?thesis
      by auto
  next
    case False
    with \<open>a * w\<^sup>2 + b * w + c = 0\<close> show ?thesis
      by auto
  qed
qed

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
