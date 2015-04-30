(*  Title:       Roots of real quadratics
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012

Originally from the AFP entry Tarskis_Geometry
*)

section "Roots of real quadratics"

theory Quadratic_Discriminant
imports Complex_Main
begin

definition discrim :: "[real,real,real] \<Rightarrow> real" where
  "discrim a b c \<equiv> b\<^sup>2 - 4 * a * c"

lemma complete_square:
  fixes a b c x :: "real"
  assumes "a \<noteq> 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> (2 * a * x + b)\<^sup>2 = discrim a b c"
proof -
  have "4 * a\<^sup>2 * x\<^sup>2 + 4 * a * b * x + 4 * a * c = 4 * a * (a * x\<^sup>2 + b * x + c)"
    by (simp add: algebra_simps power2_eq_square)
  with `a \<noteq> 0`
  have "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> 4 * a\<^sup>2 * x\<^sup>2 + 4 * a * b * x + 4 * a * c = 0"
    by simp
  thus "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> (2 * a * x + b)\<^sup>2 = discrim a b c"
    unfolding discrim_def
    by (simp add: power2_eq_square algebra_simps)
qed

lemma discriminant_negative:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
  and "discrim a b c < 0"
  shows "a * x\<^sup>2 + b * x + c \<noteq> 0"
proof -
  have "(2 * a * x + b)\<^sup>2 \<ge> 0" by simp
  with `discrim a b c < 0` have "(2 * a * x + b)\<^sup>2 \<noteq> discrim a b c" by arith
  with complete_square and `a \<noteq> 0` show "a * x\<^sup>2 + b * x + c \<noteq> 0" by simp
qed

lemma plus_or_minus_sqrt:
  fixes x y :: real
  assumes "y \<ge> 0"
  shows "x\<^sup>2 = y \<longleftrightarrow> x = sqrt y \<or> x = - sqrt y"
proof
  assume "x\<^sup>2 = y"
  hence "sqrt (x\<^sup>2) = sqrt y" by simp
  hence "sqrt y = \<bar>x\<bar>" by simp
  thus "x = sqrt y \<or> x = - sqrt y" by auto
next
  assume "x = sqrt y \<or> x = - sqrt y"
  hence "x\<^sup>2 = (sqrt y)\<^sup>2 \<or> x\<^sup>2 = (- sqrt y)\<^sup>2" by auto
  with `y \<ge> 0` show "x\<^sup>2 = y" by simp
qed

lemma divide_non_zero:
  fixes x y z :: real
  assumes "x \<noteq> 0"
  shows "x * y = z \<longleftrightarrow> y = z / x"
proof
  assume "x * y = z"
  with `x \<noteq> 0` show "y = z / x" by (simp add: field_simps)
next
  assume "y = z / x"
  with `x \<noteq> 0` show "x * y = z" by simp
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
  also from `a \<noteq> 0` and divide_non_zero [of "2 * a" x]
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
  using discriminant_nonneg and assms
  by simp

theorem discriminant_iff:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow>
  discrim a b c \<ge> 0 \<and>
  (x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
  x = (-b - sqrt (discrim a b c)) / (2 * a))"
proof
  assume "a * x\<^sup>2 + b * x + c = 0"
  with discriminant_negative and `a \<noteq> 0` have "\<not>(discrim a b c < 0)" by auto
  hence "discrim a b c \<ge> 0" by simp
  with discriminant_nonneg and `a * x\<^sup>2 + b * x + c = 0` and `a \<noteq> 0`
  have "x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a)"
    by simp
  with `discrim a b c \<ge> 0`
  show "discrim a b c \<ge> 0 \<and>
    (x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a))" ..
next
  assume "discrim a b c \<ge> 0 \<and>
    (x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a))"
  hence "discrim a b c \<ge> 0" and
    "x = (-b + sqrt (discrim a b c)) / (2 * a) \<or>
    x = (-b - sqrt (discrim a b c)) / (2 * a)"
    by simp_all
  with discriminant_nonneg and `a \<noteq> 0` show "a * x\<^sup>2 + b * x + c = 0" by simp
qed

lemma discriminant_nonneg_ex:
  fixes a b c :: real
  assumes "a \<noteq> 0"
  and "discrim a b c \<ge> 0"
  shows "\<exists> x. a * x\<^sup>2 + b * x + c = 0"
  using discriminant_nonneg and assms
  by auto

lemma discriminant_pos_ex:
  fixes a b c :: real
  assumes "a \<noteq> 0"
  and "discrim a b c > 0"
  shows "\<exists> x y. x \<noteq> y \<and> a * x\<^sup>2 + b * x + c = 0 \<and> a * y\<^sup>2 + b * y + c = 0"
proof -
  let ?x = "(-b + sqrt (discrim a b c)) / (2 * a)"
  let ?y = "(-b - sqrt (discrim a b c)) / (2 * a)"
  from `discrim a b c > 0` have "sqrt (discrim a b c) \<noteq> 0" by simp
  hence "sqrt (discrim a b c) \<noteq> - sqrt (discrim a b c)" by arith
  with `a \<noteq> 0` have "?x \<noteq> ?y" by simp
  moreover
  from discriminant_nonneg [of a b c ?x]
    and discriminant_nonneg [of a b c ?y]
    and assms
  have "a * ?x\<^sup>2 + b * ?x + c = 0" and "a * ?y\<^sup>2 + b * ?y + c = 0" by simp_all
  ultimately
  show "\<exists> x y. x \<noteq> y \<and> a * x\<^sup>2 + b * x + c = 0 \<and> a * y\<^sup>2 + b * y + c = 0" by blast
qed

lemma discriminant_pos_distinct:
  fixes a b c x :: real
  assumes "a \<noteq> 0" and "discrim a b c > 0"
  shows "\<exists> y. x \<noteq> y \<and> a * y\<^sup>2 + b * y + c = 0"
proof -
  from discriminant_pos_ex and `a \<noteq> 0` and `discrim a b c > 0`
  obtain w and z where "w \<noteq> z"
    and "a * w\<^sup>2 + b * w + c = 0" and "a * z\<^sup>2 + b * z + c = 0"
    by blast
  show "\<exists> y. x \<noteq> y \<and> a * y\<^sup>2 + b * y + c = 0"
  proof cases
    assume "x = w"
    with `w \<noteq> z` have "x \<noteq> z" by simp
    with `a * z\<^sup>2 + b * z + c = 0`
    show "\<exists> y. x \<noteq> y \<and> a * y\<^sup>2 + b * y + c = 0" by auto
  next
    assume "x \<noteq> w"
    with `a * w\<^sup>2 + b * w + c = 0`
    show "\<exists> y. x \<noteq> y \<and> a * y\<^sup>2 + b * y + c = 0" by auto
  qed
qed

end
