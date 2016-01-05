(*  Title:    HOL/Library/Nonpos_Ints.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>Non-positive integers\<close>

theory Nonpos_Ints
imports Complex_Main
begin

text \<open>
  The set of non-positive integers on a ring. (in analogy to the set of non-negative
  integers @{term "\<nat>"}) This is useful e.g. for the Gamma function.
\<close>

definition nonpos_Ints ("\<int>\<^sub>\<le>\<^sub>0") where "\<int>\<^sub>\<le>\<^sub>0 = {of_int n |n. n \<le> 0}"

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
  with `m \<le> 0` show "n = 0" by auto
qed simp

lemma nonpos_Ints_of_int: "n \<le> 0 \<Longrightarrow> of_int n \<in> \<int>\<^sub>\<le>\<^sub>0"
  unfolding nonpos_Ints_def by blast

lemma nonpos_IntsI: 
  "x \<in> \<int> \<Longrightarrow> x \<le> 0 \<Longrightarrow> (x :: 'a :: linordered_idom) \<in> \<int>\<^sub>\<le>\<^sub>0"
  using assms unfolding nonpos_Ints_def Ints_def by auto

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
  note `of_real x = of_int n`
  also have "of_int n = of_real (of_int n)" by (rule of_real_of_int_eq [symmetric])
  finally have "x = of_int n" by (subst (asm) of_real_eq_iff)
  with `n \<le> 0` show "x \<in> \<int>\<^sub>\<le>\<^sub>0" by (simp add: nonpos_Ints_of_int)
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

end