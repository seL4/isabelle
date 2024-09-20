(*  Title:    HOL/Library/Nonpos_Ints.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>Non-negative, non-positive integers and reals\<close>

theory Nonpos_Ints
imports Complex_Main
begin

subsection\<open>Non-positive integers\<close>
text \<open>
  The set of non-positive integers on a ring. (in analogy to the set of non-negative
  integers \<^term>\<open>\<nat>\<close>) This is useful e.g. for the Gamma function.
\<close>

definition nonpos_Ints (\<open>\<int>\<^sub>\<le>\<^sub>0\<close>) where "\<int>\<^sub>\<le>\<^sub>0 = {of_int n |n. n \<le> 0}"

lemma zero_in_nonpos_Ints [simp,intro]: "0 \<in> \<int>\<^sub>\<le>\<^sub>0"
  unfolding nonpos_Ints_def by (auto intro!: exI[of _ "0::int"])

lemma neg_one_in_nonpos_Ints [simp,intro]: "-1 \<in> \<int>\<^sub>\<le>\<^sub>0"
  unfolding nonpos_Ints_def by (auto intro!: exI[of _ "-1::int"])

lemma neg_numeral_in_nonpos_Ints [simp,intro]: "-numeral n \<in> \<int>\<^sub>\<le>\<^sub>0"
  unfolding nonpos_Ints_def by (auto intro!: exI[of _ "-numeral n::int"])

lemma one_notin_nonpos_Ints [simp]: "(1 :: 'a :: ring_char_0) \<notin> \<int>\<^sub>\<le>\<^sub>0"
  by (auto simp: nonpos_Ints_def)

lemma numeral_notin_nonpos_Ints [simp]: "(numeral n :: 'a :: ring_char_0) \<notin> \<int>\<^sub>\<le>\<^sub>0"
  by (auto simp: nonpos_Ints_def)

lemma minus_of_nat_in_nonpos_Ints [simp, intro]: "- of_nat n \<in> \<int>\<^sub>\<le>\<^sub>0"
proof -
  have "- of_nat n = of_int (-int n)" by simp
  also have "-int n \<le> 0" by simp
  hence "of_int (-int n) \<in> \<int>\<^sub>\<le>\<^sub>0" unfolding nonpos_Ints_def by blast
  finally show ?thesis .
qed

lemma of_nat_in_nonpos_Ints_iff: "(of_nat n :: 'a :: {ring_1,ring_char_0}) \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> n = 0"
proof
  assume "(of_nat n :: 'a) \<in> \<int>\<^sub>\<le>\<^sub>0"
  then obtain m where "of_nat n = (of_int m :: 'a)" "m \<le> 0" by (auto simp: nonpos_Ints_def)
  hence "(of_int m :: 'a) = of_nat n" by simp
  also have "... = of_int (int n)" by simp
  finally have "m = int n" by (subst (asm) of_int_eq_iff)
  with \<open>m \<le> 0\<close> show "n = 0" by auto
qed simp

lemma nonpos_Ints_of_int: "n \<le> 0 \<Longrightarrow> of_int n \<in> \<int>\<^sub>\<le>\<^sub>0"
  unfolding nonpos_Ints_def by blast

lemma nonpos_IntsI: 
  "x \<in> \<int> \<Longrightarrow> x \<le> 0 \<Longrightarrow> (x :: 'a :: linordered_idom) \<in> \<int>\<^sub>\<le>\<^sub>0"
  unfolding nonpos_Ints_def Ints_def by auto

lemma nonpos_Ints_subset_Ints: "\<int>\<^sub>\<le>\<^sub>0 \<subseteq> \<int>"
  unfolding nonpos_Ints_def Ints_def by blast

lemma nonpos_Ints_nonpos [dest]: "x \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> x \<le> (0 :: 'a :: linordered_idom)"
  unfolding nonpos_Ints_def by auto

lemma nonpos_Ints_Int [dest]: "x \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> x \<in> \<int>"
  unfolding nonpos_Ints_def Ints_def by blast

lemma nonpos_Ints_cases:
  assumes "x \<in> \<int>\<^sub>\<le>\<^sub>0"
  obtains n where "x = of_int n" "n \<le> 0"
  using assms unfolding nonpos_Ints_def by (auto elim!: Ints_cases)

lemma nonpos_Ints_cases':
  assumes "x \<in> \<int>\<^sub>\<le>\<^sub>0"
  obtains n where "x = -of_nat n"
proof -
  from assms obtain m where "x = of_int m" and m: "m \<le> 0" by (auto elim!: nonpos_Ints_cases)
  hence "x = - of_int (-m)" by auto
  also from m have "(of_int (-m) :: 'a) = of_nat (nat (-m))" by simp_all
  finally show ?thesis by (rule that)
qed

lemma of_real_in_nonpos_Ints_iff: "(of_real x :: 'a :: real_algebra_1) \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> x \<in> \<int>\<^sub>\<le>\<^sub>0"
proof
  assume "of_real x \<in> (\<int>\<^sub>\<le>\<^sub>0 :: 'a set)"
  then obtain n where "(of_real x :: 'a) = of_int n" "n \<le> 0" by (erule nonpos_Ints_cases)
  note \<open>of_real x = of_int n\<close>
  also have "of_int n = of_real (of_int n)" by (rule of_real_of_int_eq [symmetric])
  finally have "x = of_int n" by (subst (asm) of_real_eq_iff)
  with \<open>n \<le> 0\<close> show "x \<in> \<int>\<^sub>\<le>\<^sub>0" by (simp add: nonpos_Ints_of_int)
qed (auto elim!: nonpos_Ints_cases intro!: nonpos_Ints_of_int)

lemma nonpos_Ints_altdef: "\<int>\<^sub>\<le>\<^sub>0 = {n \<in> \<int>. (n :: 'a :: linordered_idom) \<le> 0}"
  by (auto intro!: nonpos_IntsI elim!: nonpos_Ints_cases)

lemma uminus_in_Nats_iff: "-x \<in> \<nat> \<longleftrightarrow> x \<in> \<int>\<^sub>\<le>\<^sub>0"
proof
  assume "-x \<in> \<nat>"
  then obtain n where "n \<ge> 0" "-x = of_int n" by (auto simp: Nats_altdef1)
  hence "-n \<le> 0" "x = of_int (-n)" by (simp_all add: eq_commute minus_equation_iff[of x])
  thus "x \<in> \<int>\<^sub>\<le>\<^sub>0" unfolding nonpos_Ints_def by blast
next
  assume "x \<in> \<int>\<^sub>\<le>\<^sub>0"
  then obtain n where "n \<le> 0" "x = of_int n" by (auto simp: nonpos_Ints_def)
  hence "-n \<ge> 0" "-x = of_int (-n)" by (simp_all add: eq_commute minus_equation_iff[of x])
  thus "-x \<in> \<nat>" unfolding Nats_altdef1 by blast
qed

lemma uminus_in_nonpos_Ints_iff: "-x \<in> \<int>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> x \<in> \<nat>"
  using uminus_in_Nats_iff[of "-x"] by simp

lemma nonpos_Ints_mult: "x \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> y \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> x * y \<in> \<nat>"
  using Nats_mult[of "-x" "-y"] by (simp add: uminus_in_Nats_iff)

lemma Nats_mult_nonpos_Ints: "x \<in> \<nat> \<Longrightarrow> y \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> x * y \<in> \<int>\<^sub>\<le>\<^sub>0"
  using Nats_mult[of x "-y"] by (simp add: uminus_in_Nats_iff)

lemma nonpos_Ints_mult_Nats:
  "x \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> y \<in> \<nat> \<Longrightarrow> x * y \<in> \<int>\<^sub>\<le>\<^sub>0"
  using Nats_mult[of "-x" y] by (simp add: uminus_in_Nats_iff)

lemma nonpos_Ints_add:
  "x \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> y \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> x + y \<in> \<int>\<^sub>\<le>\<^sub>0"
  using Nats_add[of "-x" "-y"] uminus_in_Nats_iff[of "y+x", simplified minus_add] 
  by (simp add: uminus_in_Nats_iff add.commute)

lemma nonpos_Ints_diff_Nats:
  "x \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> y \<in> \<nat> \<Longrightarrow> x - y \<in> \<int>\<^sub>\<le>\<^sub>0"
  using Nats_add[of "-x" "y"] uminus_in_Nats_iff[of "x-y", simplified minus_add] 
  by (simp add: uminus_in_Nats_iff add.commute)

lemma Nats_diff_nonpos_Ints:
  "x \<in> \<nat> \<Longrightarrow> y \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> x - y \<in> \<nat>"
  using Nats_add[of "x" "-y"] by (simp add: uminus_in_Nats_iff add.commute)

lemma plus_of_nat_eq_0_imp: "z + of_nat n = 0 \<Longrightarrow> z \<in> \<int>\<^sub>\<le>\<^sub>0"
proof -
  assume "z + of_nat n = 0"
  hence A: "z = - of_nat n" by (simp add: eq_neg_iff_add_eq_0)
  show "z \<in> \<int>\<^sub>\<le>\<^sub>0" by (subst A) simp
qed


subsection\<open>Non-negative reals\<close>

definition nonneg_Reals :: "'a::real_algebra_1 set"  (\<open>\<real>\<^sub>\<ge>\<^sub>0\<close>)
  where "\<real>\<^sub>\<ge>\<^sub>0 = {of_real r | r. r \<ge> 0}"

lemma nonneg_Reals_of_real_iff [simp]: "of_real r \<in> \<real>\<^sub>\<ge>\<^sub>0 \<longleftrightarrow> r \<ge> 0"
  by (force simp add: nonneg_Reals_def)

lemma nonneg_Reals_subset_Reals: "\<real>\<^sub>\<ge>\<^sub>0 \<subseteq> \<real>"
  unfolding nonneg_Reals_def Reals_def by blast

lemma nonneg_Reals_Real [dest]: "x \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> x \<in> \<real>"
  unfolding nonneg_Reals_def Reals_def by blast

lemma nonneg_Reals_of_nat_I [simp]: "of_nat n \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (metis nonneg_Reals_of_real_iff of_nat_0_le_iff of_real_of_nat_eq)

lemma nonneg_Reals_cases:
  assumes "x \<in> \<real>\<^sub>\<ge>\<^sub>0"
  obtains r where "x = of_real r" "r \<ge> 0"
  using assms unfolding nonneg_Reals_def by (auto elim!: Reals_cases)

lemma nonneg_Reals_zero_I [simp]: "0 \<in> \<real>\<^sub>\<ge>\<^sub>0"
  unfolding nonneg_Reals_def by auto

lemma nonneg_Reals_one_I [simp]: "1 \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (metis (mono_tags, lifting) nonneg_Reals_of_nat_I of_nat_1)

lemma nonneg_Reals_minus_one_I [simp]: "-1 \<notin> \<real>\<^sub>\<ge>\<^sub>0"
  by (metis nonneg_Reals_of_real_iff le_minus_one_simps(3) of_real_1 of_real_def real_vector.scale_minus_left)

lemma nonneg_Reals_numeral_I [simp]: "numeral w \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (metis (no_types) nonneg_Reals_of_nat_I of_nat_numeral)

lemma nonneg_Reals_minus_numeral_I [simp]: "- numeral w \<notin> \<real>\<^sub>\<ge>\<^sub>0"
  using nonneg_Reals_of_real_iff not_zero_le_neg_numeral by fastforce

lemma nonneg_Reals_add_I [simp]: "\<lbrakk>a \<in> \<real>\<^sub>\<ge>\<^sub>0; b \<in> \<real>\<^sub>\<ge>\<^sub>0\<rbrakk> \<Longrightarrow> a + b \<in> \<real>\<^sub>\<ge>\<^sub>0"
apply (simp add: nonneg_Reals_def)
apply clarify
apply (rename_tac r s)
apply (rule_tac x="r+s" in exI, auto)
done

lemma nonneg_Reals_mult_I [simp]: "\<lbrakk>a \<in> \<real>\<^sub>\<ge>\<^sub>0; b \<in> \<real>\<^sub>\<ge>\<^sub>0\<rbrakk> \<Longrightarrow> a * b \<in> \<real>\<^sub>\<ge>\<^sub>0"
  unfolding nonneg_Reals_def  by (auto simp: of_real_def)

lemma nonneg_Reals_inverse_I [simp]:
  fixes a :: "'a::real_div_algebra"
  shows "a \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> inverse a \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (simp add: nonneg_Reals_def image_iff) (metis inverse_nonnegative_iff_nonnegative of_real_inverse)

lemma nonneg_Reals_divide_I [simp]:
  fixes a :: "'a::real_div_algebra"
  shows "\<lbrakk>a \<in> \<real>\<^sub>\<ge>\<^sub>0; b \<in> \<real>\<^sub>\<ge>\<^sub>0\<rbrakk> \<Longrightarrow> a / b \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (simp add: divide_inverse)

lemma nonneg_Reals_pow_I [simp]: "a \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> a^n \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (induction n) auto

lemma complex_nonneg_Reals_iff: "z \<in> \<real>\<^sub>\<ge>\<^sub>0 \<longleftrightarrow> Re z \<ge> 0 \<and> Im z = 0"
  by (auto simp: nonneg_Reals_def) (metis complex_of_real_def complex_surj)

lemma ii_not_nonneg_Reals [iff]: "\<i> \<notin> \<real>\<^sub>\<ge>\<^sub>0"
  by (simp add: complex_nonneg_Reals_iff)


subsection\<open>Non-positive reals\<close>

definition nonpos_Reals :: "'a::real_algebra_1 set"  (\<open>\<real>\<^sub>\<le>\<^sub>0\<close>)
  where "\<real>\<^sub>\<le>\<^sub>0 = {of_real r | r. r \<le> 0}"

lemma nonpos_Reals_of_real_iff [simp]: "of_real r \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> r \<le> 0"
  by (force simp add: nonpos_Reals_def)

lemma nonpos_Reals_subset_Reals: "\<real>\<^sub>\<le>\<^sub>0 \<subseteq> \<real>"
  unfolding nonpos_Reals_def Reals_def by blast

lemma nonpos_Ints_subset_nonpos_Reals: "\<int>\<^sub>\<le>\<^sub>0 \<subseteq> \<real>\<^sub>\<le>\<^sub>0"
  by (metis nonpos_Ints_cases nonpos_Ints_nonpos nonpos_Ints_of_int 
    nonpos_Reals_of_real_iff of_real_of_int_eq subsetI)

lemma nonpos_Reals_of_nat_iff [simp]: "of_nat n \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> n=0"
  by (metis nonpos_Reals_of_real_iff of_nat_le_0_iff of_real_of_nat_eq)

lemma nonpos_Reals_Real [dest]: "x \<in> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> x \<in> \<real>"
  unfolding nonpos_Reals_def Reals_def by blast

lemma nonpos_Reals_cases:
  assumes "x \<in> \<real>\<^sub>\<le>\<^sub>0"
  obtains r where "x = of_real r" "r \<le> 0"
  using assms unfolding nonpos_Reals_def by (auto elim!: Reals_cases)

lemma uminus_nonneg_Reals_iff [simp]: "-x \<in> \<real>\<^sub>\<ge>\<^sub>0 \<longleftrightarrow> x \<in> \<real>\<^sub>\<le>\<^sub>0"
  apply (auto simp: nonpos_Reals_def nonneg_Reals_def)
  apply (metis nonpos_Reals_of_real_iff minus_minus neg_le_0_iff_le of_real_minus)
  done

lemma uminus_nonpos_Reals_iff [simp]: "-x \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> x \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (metis (no_types) minus_minus uminus_nonneg_Reals_iff)

lemma nonpos_Reals_zero_I [simp]: "0 \<in> \<real>\<^sub>\<le>\<^sub>0"
  unfolding nonpos_Reals_def by force

lemma nonpos_Reals_one_I [simp]: "1 \<notin> \<real>\<^sub>\<le>\<^sub>0"
  using nonneg_Reals_minus_one_I uminus_nonneg_Reals_iff by blast

lemma nonpos_Reals_numeral_I [simp]: "numeral w \<notin> \<real>\<^sub>\<le>\<^sub>0"
  using nonneg_Reals_minus_numeral_I uminus_nonneg_Reals_iff by blast

lemma nonpos_Reals_add_I [simp]: "\<lbrakk>a \<in> \<real>\<^sub>\<le>\<^sub>0; b \<in> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> a + b \<in> \<real>\<^sub>\<le>\<^sub>0"
  by (metis nonneg_Reals_add_I add_uminus_conv_diff minus_diff_eq minus_minus uminus_nonpos_Reals_iff)

lemma nonpos_Reals_mult_I1: "\<lbrakk>a \<in> \<real>\<^sub>\<ge>\<^sub>0; b \<in> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> a * b \<in> \<real>\<^sub>\<le>\<^sub>0"
  by (metis nonneg_Reals_mult_I mult_minus_right uminus_nonneg_Reals_iff)

lemma nonpos_Reals_mult_I2: "\<lbrakk>a \<in> \<real>\<^sub>\<le>\<^sub>0; b \<in> \<real>\<^sub>\<ge>\<^sub>0\<rbrakk> \<Longrightarrow> a * b \<in> \<real>\<^sub>\<le>\<^sub>0"
  by (metis nonneg_Reals_mult_I mult_minus_left uminus_nonneg_Reals_iff)

lemma nonpos_Reals_mult_of_nat_iff:
  fixes a:: "'a :: real_div_algebra" shows "a * of_nat n \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> a \<in> \<real>\<^sub>\<le>\<^sub>0 \<or> n=0"
  apply (auto intro: nonpos_Reals_mult_I2)
  apply (auto simp: nonpos_Reals_def)
  apply (rule_tac x="r/n" in exI)
  apply (auto simp: field_split_simps)
  done

lemma nonpos_Reals_inverse_I:
    fixes a :: "'a::real_div_algebra"
    shows "a \<in> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> inverse a \<in> \<real>\<^sub>\<le>\<^sub>0"
  using nonneg_Reals_inverse_I uminus_nonneg_Reals_iff by fastforce

lemma nonpos_Reals_divide_I1:
    fixes a :: "'a::real_div_algebra"
    shows "\<lbrakk>a \<in> \<real>\<^sub>\<ge>\<^sub>0; b \<in> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> a / b \<in> \<real>\<^sub>\<le>\<^sub>0"
  by (simp add: nonpos_Reals_inverse_I nonpos_Reals_mult_I1 divide_inverse)

lemma nonpos_Reals_divide_I2:
    fixes a :: "'a::real_div_algebra"
    shows "\<lbrakk>a \<in> \<real>\<^sub>\<le>\<^sub>0; b \<in> \<real>\<^sub>\<ge>\<^sub>0\<rbrakk> \<Longrightarrow> a / b \<in> \<real>\<^sub>\<le>\<^sub>0"
  by (metis nonneg_Reals_divide_I minus_divide_left uminus_nonneg_Reals_iff)

lemma nonpos_Reals_divide_of_nat_iff:
  fixes a:: "'a :: real_div_algebra" shows "a / of_nat n \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> a \<in> \<real>\<^sub>\<le>\<^sub>0 \<or> n=0"
  apply (auto intro: nonpos_Reals_divide_I2)
  apply (auto simp: nonpos_Reals_def)
  apply (rule_tac x="r*n" in exI)
  apply (auto simp: field_split_simps mult_le_0_iff)
  done

lemma nonpos_Reals_inverse_iff [simp]:
  fixes a :: "'a::real_div_algebra"
  shows "inverse a \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> a \<in> \<real>\<^sub>\<le>\<^sub>0"
  using nonpos_Reals_inverse_I by fastforce

lemma nonpos_Reals_pow_I: "\<lbrakk>a \<in> \<real>\<^sub>\<le>\<^sub>0; odd n\<rbrakk> \<Longrightarrow> a^n \<in> \<real>\<^sub>\<le>\<^sub>0"
  by (metis nonneg_Reals_pow_I power_minus_odd uminus_nonneg_Reals_iff)

lemma complex_nonpos_Reals_iff: "z \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> Re z \<le> 0 \<and> Im z = 0"
   using complex_is_Real_iff by (force simp add: nonpos_Reals_def)

lemma ii_not_nonpos_Reals [iff]: "\<i> \<notin> \<real>\<^sub>\<le>\<^sub>0"
  by (simp add: complex_nonpos_Reals_iff)

end
