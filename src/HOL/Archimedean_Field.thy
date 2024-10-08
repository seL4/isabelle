(*  Title:      HOL/Archimedean_Field.thy
    Author:     Brian Huffman
*)

section \<open>Archimedean Fields, Floor and Ceiling Functions\<close>

theory Archimedean_Field
imports Main
begin

lemma cInf_abs_ge:
  fixes S :: "'a::{linordered_idom,conditionally_complete_linorder} set"
  assumes "S \<noteq> {}"
    and bdd: "\<And>x. x\<in>S \<Longrightarrow> \<bar>x\<bar> \<le> a"
  shows "\<bar>Inf S\<bar> \<le> a"
proof -
  have "Sup (uminus ` S) = - (Inf S)"
  proof (rule antisym)
    have "\<And>x. x \<in> S \<Longrightarrow> bdd_above (uminus ` S)"
      using bdd by (force simp: abs_le_iff bdd_above_def)
  then show "- (Inf S) \<le> Sup (uminus ` S)"
    by (meson cInf_greatest [OF \<open>S \<noteq> {}\<close>] cSUP_upper minus_le_iff)
  next
    have *: "\<And>x. x \<in> S \<Longrightarrow> Inf S \<le> x"
      by (meson abs_le_iff bdd bdd_below_def cInf_lower minus_le_iff)
    show "Sup (uminus ` S) \<le> - Inf S"
      using \<open>S \<noteq> {}\<close> by (force intro: * cSup_least)
  qed
  with cSup_abs_le [of "uminus ` S"] assms show ?thesis
    by fastforce
qed

lemma cSup_asclose:
  fixes S :: "'a::{linordered_idom,conditionally_complete_linorder} set"
  assumes S: "S \<noteq> {}"
    and b: "\<forall>x\<in>S. \<bar>x - l\<bar> \<le> e"
  shows "\<bar>Sup S - l\<bar> \<le> e"
proof -
  have *: "\<bar>x - l\<bar> \<le> e \<longleftrightarrow> l - e \<le> x \<and> x \<le> l + e" for x l e :: 'a
    by arith
  have "bdd_above S"
    using b by (auto intro!: bdd_aboveI[of _ "l + e"])
  with S b show ?thesis
    unfolding * by (auto intro!: cSup_upper2 cSup_least)
qed

lemma cInf_asclose:
  fixes S :: "'a::{linordered_idom,conditionally_complete_linorder} set"
  assumes S: "S \<noteq> {}"
    and b: "\<forall>x\<in>S. \<bar>x - l\<bar> \<le> e"
  shows "\<bar>Inf S - l\<bar> \<le> e"
proof -
  have *: "\<bar>x - l\<bar> \<le> e \<longleftrightarrow> l - e \<le> x \<and> x \<le> l + e" for x l e :: 'a
    by arith
  have "bdd_below S"
    using b by (auto intro!: bdd_belowI[of _ "l - e"])
  with S b show ?thesis
    unfolding * by (auto intro!: cInf_lower2 cInf_greatest)
qed


subsection \<open>Class of Archimedean fields\<close>

text \<open>Archimedean fields have no infinite elements.\<close>

class archimedean_field = linordered_field +
  assumes ex_le_of_int: "\<exists>z. x \<le> of_int z"

lemma ex_less_of_int: "\<exists>z. x < of_int z"
  for x :: "'a::archimedean_field"
proof -
  from ex_le_of_int obtain z where "x \<le> of_int z" ..
  then have "x < of_int (z + 1)" by simp
  then show ?thesis ..
qed

lemma ex_of_int_less: "\<exists>z. of_int z < x"
  for x :: "'a::archimedean_field"
proof -
  from ex_less_of_int obtain z where "- x < of_int z" ..
  then have "of_int (- z) < x" by simp
  then show ?thesis ..
qed

lemma reals_Archimedean2: "\<exists>n. x < of_nat n"
  for x :: "'a::archimedean_field"
proof -
  obtain z where "x < of_int z"
    using ex_less_of_int ..
  also have "\<dots> \<le> of_int (int (nat z))"
    by simp
  also have "\<dots> = of_nat (nat z)"
    by (simp only: of_int_of_nat_eq)
  finally show ?thesis ..
qed

lemma real_arch_simple: "\<exists>n. x \<le> of_nat n"
  for x :: "'a::archimedean_field"
proof -
  obtain n where "x < of_nat n"
    using reals_Archimedean2 ..
  then have "x \<le> of_nat n"
    by simp
  then show ?thesis ..
qed

text \<open>Archimedean fields have no infinitesimal elements.\<close>

lemma reals_Archimedean:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x"
  shows "\<exists>n. inverse (of_nat (Suc n)) < x"
proof -
  from \<open>0 < x\<close> have "0 < inverse x"
    by (rule positive_imp_inverse_positive)
  obtain n where "inverse x < of_nat n"
    using reals_Archimedean2 ..
  then obtain m where "inverse x < of_nat (Suc m)"
    using \<open>0 < inverse x\<close> by (cases n) (simp_all del: of_nat_Suc)
  then have "inverse (of_nat (Suc m)) < inverse (inverse x)"
    using \<open>0 < inverse x\<close> by (rule less_imp_inverse_less)
  then have "inverse (of_nat (Suc m)) < x"
    using \<open>0 < x\<close> by (simp add: nonzero_inverse_inverse_eq)
  then show ?thesis ..
qed

lemma ex_inverse_of_nat_less:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x"
  shows "\<exists>n>0. inverse (of_nat n) < x"
  using reals_Archimedean [OF \<open>0 < x\<close>] by auto

lemma ex_less_of_nat_mult:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x"
  shows "\<exists>n. y < of_nat n * x"
proof -
  obtain n where "y / x < of_nat n"
    using reals_Archimedean2 ..
  with \<open>0 < x\<close> have "y < of_nat n * x"
    by (simp add: pos_divide_less_eq)
  then show ?thesis ..
qed


subsection \<open>Existence and uniqueness of floor function\<close>

lemma exists_least_lemma:
  assumes "\<not> P 0" and "\<exists>n. P n"
  shows "\<exists>n. \<not> P n \<and> P (Suc n)"
proof -
  from \<open>\<exists>n. P n\<close> have "P (Least P)"
    by (rule LeastI_ex)
  with \<open>\<not> P 0\<close> obtain n where "Least P = Suc n"
    by (cases "Least P") auto
  then have "n < Least P"
    by simp
  then have "\<not> P n"
    by (rule not_less_Least)
  then have "\<not> P n \<and> P (Suc n)"
    using \<open>P (Least P)\<close> \<open>Least P = Suc n\<close> by simp
  then show ?thesis ..
qed

lemma floor_exists:
  fixes x :: "'a::archimedean_field"
  shows "\<exists>z. of_int z \<le> x \<and> x < of_int (z + 1)"
proof (cases "0 \<le> x")
  case True
  then have "\<not> x < of_nat 0"
    by simp
  then have "\<exists>n. \<not> x < of_nat n \<and> x < of_nat (Suc n)"
    using reals_Archimedean2 by (rule exists_least_lemma)
  then obtain n where "\<not> x < of_nat n \<and> x < of_nat (Suc n)" ..
  then have "of_int (int n) \<le> x \<and> x < of_int (int n + 1)"
    by simp
  then show ?thesis ..
next
  case False
  then have "\<not> - x \<le> of_nat 0"
    by simp
  then have "\<exists>n. \<not> - x \<le> of_nat n \<and> - x \<le> of_nat (Suc n)"
    using real_arch_simple by (rule exists_least_lemma)
  then obtain n where "\<not> - x \<le> of_nat n \<and> - x \<le> of_nat (Suc n)" ..
  then have "of_int (- int n - 1) \<le> x \<and> x < of_int (- int n - 1 + 1)"
    by simp
  then show ?thesis ..
qed

lemma floor_exists1: "\<exists>!z. of_int z \<le> x \<and> x < of_int (z + 1)"
  for x :: "'a::archimedean_field"
proof (rule ex_ex1I)
  show "\<exists>z. of_int z \<le> x \<and> x < of_int (z + 1)"
    by (rule floor_exists)
next
  fix y z
  assume "of_int y \<le> x \<and> x < of_int (y + 1)"
    and "of_int z \<le> x \<and> x < of_int (z + 1)"
  with le_less_trans [of "of_int y" "x" "of_int (z + 1)"]
       le_less_trans [of "of_int z" "x" "of_int (y + 1)"] show "y = z"
    by (simp del: of_int_add)
qed


subsection \<open>Floor function\<close>

class floor_ceiling = archimedean_field +
  fixes floor :: "'a \<Rightarrow> int"  (\<open>(\<open>open_block notation=\<open>mixfix floor\<close>\<close>\<lfloor>_\<rfloor>)\<close>)
  assumes floor_correct: "of_int \<lfloor>x\<rfloor> \<le> x \<and> x < of_int (\<lfloor>x\<rfloor> + 1)"

lemma floor_unique: "of_int z \<le> x \<Longrightarrow> x < of_int z + 1 \<Longrightarrow> \<lfloor>x\<rfloor> = z"
  using floor_correct [of x] floor_exists1 [of x] by auto

lemma floor_eq_iff: "\<lfloor>x\<rfloor> = a \<longleftrightarrow> of_int a \<le> x \<and> x < of_int a + 1"
using floor_correct floor_unique by auto

lemma of_int_floor_le [simp]: "of_int \<lfloor>x\<rfloor> \<le> x"
  using floor_correct ..

lemma le_floor_iff: "z \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> of_int z \<le> x"
proof
  assume "z \<le> \<lfloor>x\<rfloor>"
  then have "(of_int z :: 'a) \<le> of_int \<lfloor>x\<rfloor>" by simp
  also have "of_int \<lfloor>x\<rfloor> \<le> x" by (rule of_int_floor_le)
  finally show "of_int z \<le> x" .
next
  assume "of_int z \<le> x"
  also have "x < of_int (\<lfloor>x\<rfloor> + 1)" using floor_correct ..
  finally show "z \<le> \<lfloor>x\<rfloor>" by (simp del: of_int_add)
qed

lemma floor_less_iff: "\<lfloor>x\<rfloor> < z \<longleftrightarrow> x < of_int z"
  by (simp add: not_le [symmetric] le_floor_iff)

lemma less_floor_iff: "z < \<lfloor>x\<rfloor> \<longleftrightarrow> of_int z + 1 \<le> x"
  using le_floor_iff [of "z + 1" x] by auto

lemma floor_le_iff: "\<lfloor>x\<rfloor> \<le> z \<longleftrightarrow> x < of_int z + 1"
  by (simp add: not_less [symmetric] less_floor_iff)

lemma floor_split[linarith_split]: "P \<lfloor>t\<rfloor> \<longleftrightarrow> (\<forall>i. of_int i \<le> t \<and> t < of_int i + 1 \<longrightarrow> P i)"
  by (metis floor_correct floor_unique less_floor_iff not_le order_refl)

lemma floor_mono:
  assumes "x \<le> y"
  shows "\<lfloor>x\<rfloor> \<le> \<lfloor>y\<rfloor>"
proof -
  have "of_int \<lfloor>x\<rfloor> \<le> x" by (rule of_int_floor_le)
  also note \<open>x \<le> y\<close>
  finally show ?thesis by (simp add: le_floor_iff)
qed

lemma floor_less_cancel: "\<lfloor>x\<rfloor> < \<lfloor>y\<rfloor> \<Longrightarrow> x < y"
  by (auto simp add: not_le [symmetric] floor_mono)

lemma floor_of_int [simp]: "\<lfloor>of_int z\<rfloor> = z"
  by (rule floor_unique) simp_all

lemma floor_of_nat [simp]: "\<lfloor>of_nat n\<rfloor> = int n"
  using floor_of_int [of "of_nat n"] by simp

lemma le_floor_add: "\<lfloor>x\<rfloor> + \<lfloor>y\<rfloor> \<le> \<lfloor>x + y\<rfloor>"
  by (simp only: le_floor_iff of_int_add add_mono of_int_floor_le)


text \<open>Floor with numerals.\<close>

lemma floor_zero [simp]: "\<lfloor>0\<rfloor> = 0"
  using floor_of_int [of 0] by simp

lemma floor_one [simp]: "\<lfloor>1\<rfloor> = 1"
  using floor_of_int [of 1] by simp

lemma floor_numeral [simp]: "\<lfloor>numeral v\<rfloor> = numeral v"
  using floor_of_int [of "numeral v"] by simp

lemma floor_neg_numeral [simp]: "\<lfloor>- numeral v\<rfloor> = - numeral v"
  using floor_of_int [of "- numeral v"] by simp

lemma zero_le_floor [simp]: "0 \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> 0 \<le> x"
  by (simp add: le_floor_iff)

lemma one_le_floor [simp]: "1 \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> 1 \<le> x"
  by (simp add: le_floor_iff)

lemma numeral_le_floor [simp]: "numeral v \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> numeral v \<le> x"
  by (simp add: le_floor_iff)

lemma neg_numeral_le_floor [simp]: "- numeral v \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> - numeral v \<le> x"
  by (simp add: le_floor_iff)

lemma zero_less_floor [simp]: "0 < \<lfloor>x\<rfloor> \<longleftrightarrow> 1 \<le> x"
  by (simp add: less_floor_iff)

lemma one_less_floor [simp]: "1 < \<lfloor>x\<rfloor> \<longleftrightarrow> 2 \<le> x"
  by (simp add: less_floor_iff)

lemma numeral_less_floor [simp]: "numeral v < \<lfloor>x\<rfloor> \<longleftrightarrow> numeral v + 1 \<le> x"
  by (simp add: less_floor_iff)

lemma neg_numeral_less_floor [simp]: "- numeral v < \<lfloor>x\<rfloor> \<longleftrightarrow> - numeral v + 1 \<le> x"
  by (simp add: less_floor_iff)

lemma floor_le_zero [simp]: "\<lfloor>x\<rfloor> \<le> 0 \<longleftrightarrow> x < 1"
  by (simp add: floor_le_iff)

lemma floor_le_one [simp]: "\<lfloor>x\<rfloor> \<le> 1 \<longleftrightarrow> x < 2"
  by (simp add: floor_le_iff)

lemma floor_le_numeral [simp]: "\<lfloor>x\<rfloor> \<le> numeral v \<longleftrightarrow> x < numeral v + 1"
  by (simp add: floor_le_iff)

lemma floor_le_neg_numeral [simp]: "\<lfloor>x\<rfloor> \<le> - numeral v \<longleftrightarrow> x < - numeral v + 1"
  by (simp add: floor_le_iff)

lemma floor_less_zero [simp]: "\<lfloor>x\<rfloor> < 0 \<longleftrightarrow> x < 0"
  by (simp add: floor_less_iff)

lemma floor_less_one [simp]: "\<lfloor>x\<rfloor> < 1 \<longleftrightarrow> x < 1"
  by (simp add: floor_less_iff)

lemma floor_less_numeral [simp]: "\<lfloor>x\<rfloor> < numeral v \<longleftrightarrow> x < numeral v"
  by (simp add: floor_less_iff)

lemma floor_less_neg_numeral [simp]: "\<lfloor>x\<rfloor> < - numeral v \<longleftrightarrow> x < - numeral v"
  by (simp add: floor_less_iff)

lemma le_mult_floor_Ints:
  assumes "0 \<le> a" "a \<in> Ints"
  shows "of_int (\<lfloor>a\<rfloor> * \<lfloor>b\<rfloor>) \<le> (of_int\<lfloor>a * b\<rfloor> :: 'a :: linordered_idom)"
  by (metis Ints_cases assms floor_less_iff floor_of_int linorder_not_less mult_left_mono of_int_floor_le of_int_less_iff of_int_mult)


text \<open>Addition and subtraction of integers.\<close>

lemma floor_add_int: "\<lfloor>x\<rfloor> + z = \<lfloor>x + of_int z\<rfloor>"
  using floor_correct [of x] by (simp add: floor_unique[symmetric])

lemma int_add_floor: "z + \<lfloor>x\<rfloor> = \<lfloor>of_int z + x\<rfloor>"
  using floor_correct [of x] by (simp add: floor_unique[symmetric])

lemma one_add_floor: "\<lfloor>x\<rfloor> + 1 = \<lfloor>x + 1\<rfloor>"
  using floor_add_int [of x 1] by simp

lemma floor_diff_of_int [simp]: "\<lfloor>x - of_int z\<rfloor> = \<lfloor>x\<rfloor> - z"
  using floor_add_int [of x "- z"] by (simp add: algebra_simps)

lemma floor_uminus_of_int [simp]: "\<lfloor>- (of_int z)\<rfloor> = - z"
  by (metis floor_diff_of_int [of 0] diff_0 floor_zero)

lemma floor_diff_numeral [simp]: "\<lfloor>x - numeral v\<rfloor> = \<lfloor>x\<rfloor> - numeral v"
  using floor_diff_of_int [of x "numeral v"] by simp

lemma floor_diff_one [simp]: "\<lfloor>x - 1\<rfloor> = \<lfloor>x\<rfloor> - 1"
  using floor_diff_of_int [of x 1] by simp

lemma le_mult_floor:
  assumes "0 \<le> a" and "0 \<le> b"
  shows "\<lfloor>a\<rfloor> * \<lfloor>b\<rfloor> \<le> \<lfloor>a * b\<rfloor>"
proof -
  have "of_int \<lfloor>a\<rfloor> \<le> a" and "of_int \<lfloor>b\<rfloor> \<le> b"
    by (auto intro: of_int_floor_le)
  then have "of_int (\<lfloor>a\<rfloor> * \<lfloor>b\<rfloor>) \<le> a * b"
    using assms by (auto intro!: mult_mono)
  also have "a * b < of_int (\<lfloor>a * b\<rfloor> + 1)"
    using floor_correct[of "a * b"] by auto
  finally show ?thesis
    unfolding of_int_less_iff by simp
qed

lemma floor_divide_of_int_eq: "\<lfloor>of_int k / of_int l\<rfloor> = k div l"
  for k l :: int
proof (cases "l = 0")
  case True
  then show ?thesis by simp
next
  case False
  have *: "\<lfloor>of_int (k mod l) / of_int l :: 'a\<rfloor> = 0"
  proof (cases "l > 0")
    case True
    then show ?thesis
      by (auto intro: floor_unique)
  next
    case False
    obtain r where "r = - l"
      by blast
    then have l: "l = - r"
      by simp
    with \<open>l \<noteq> 0\<close> False have "r > 0"
      by simp
    with l show ?thesis
      using pos_mod_bound [of r]
      by (auto simp add: zmod_zminus2_eq_if less_le field_simps intro: floor_unique)
  qed
  have "(of_int k :: 'a) = of_int (k div l * l + k mod l)"
    by simp
  also have "\<dots> = (of_int (k div l) + of_int (k mod l) / of_int l) * of_int l"
    using False by (simp only: of_int_add) (simp add: field_simps)
  finally have "(of_int k / of_int l :: 'a) = \<dots> / of_int l"
    by simp
  then have "(of_int k / of_int l :: 'a) = of_int (k div l) + of_int (k mod l) / of_int l"
    using False by (simp only:) (simp add: field_simps)
  then have "\<lfloor>of_int k / of_int l :: 'a\<rfloor> = \<lfloor>of_int (k div l) + of_int (k mod l) / of_int l :: 'a\<rfloor>"
    by simp
  then have "\<lfloor>of_int k / of_int l :: 'a\<rfloor> = \<lfloor>of_int (k mod l) / of_int l + of_int (k div l) :: 'a\<rfloor>"
    by (simp add: ac_simps)
  then have "\<lfloor>of_int k / of_int l :: 'a\<rfloor> = \<lfloor>of_int (k mod l) / of_int l :: 'a\<rfloor> + k div l"
    by (simp add: floor_add_int)
  with * show ?thesis
    by simp
qed

lemma floor_divide_of_nat_eq: "\<lfloor>of_nat m / of_nat n\<rfloor> = of_nat (m div n)"
  for m n :: nat
    by (metis floor_divide_of_int_eq of_int_of_nat_eq linordered_euclidean_semiring_class.of_nat_div)

lemma floor_divide_lower:
  fixes q :: "'a::floor_ceiling"
  shows "q > 0 \<Longrightarrow> of_int \<lfloor>p / q\<rfloor> * q \<le> p"
  using of_int_floor_le pos_le_divide_eq by blast

lemma floor_divide_upper:
  fixes q :: "'a::floor_ceiling"
  shows "q > 0 \<Longrightarrow> p < (of_int \<lfloor>p / q\<rfloor> + 1) * q"
  by (meson floor_eq_iff pos_divide_less_eq)


subsection \<open>Ceiling function\<close>

definition ceiling :: "'a::floor_ceiling \<Rightarrow> int"  (\<open>(\<open>open_block notation=\<open>mixfix ceiling\<close>\<close>\<lceil>_\<rceil>)\<close>)
  where "\<lceil>x\<rceil> = - \<lfloor>- x\<rfloor>"

lemma ceiling_correct: "of_int \<lceil>x\<rceil> - 1 < x \<and> x \<le> of_int \<lceil>x\<rceil>"
  unfolding ceiling_def using floor_correct [of "- x"]
  by (simp add: le_minus_iff)

lemma ceiling_unique: "of_int z - 1 < x \<Longrightarrow> x \<le> of_int z \<Longrightarrow> \<lceil>x\<rceil> = z"
  unfolding ceiling_def using floor_unique [of "- z" "- x"] by simp

lemma ceiling_eq_iff: "\<lceil>x\<rceil> = a \<longleftrightarrow> of_int a - 1 < x \<and> x \<le> of_int a"
using ceiling_correct ceiling_unique by auto

lemma le_of_int_ceiling [simp]: "x \<le> of_int \<lceil>x\<rceil>"
  using ceiling_correct ..

lemma ceiling_le_iff: "\<lceil>x\<rceil> \<le> z \<longleftrightarrow> x \<le> of_int z"
  unfolding ceiling_def using le_floor_iff [of "- z" "- x"] by auto

lemma less_ceiling_iff: "z < \<lceil>x\<rceil> \<longleftrightarrow> of_int z < x"
  by (simp add: not_le [symmetric] ceiling_le_iff)

lemma ceiling_less_iff: "\<lceil>x\<rceil> < z \<longleftrightarrow> x \<le> of_int z - 1"
  using ceiling_le_iff [of x "z - 1"] by simp

lemma le_ceiling_iff: "z \<le> \<lceil>x\<rceil> \<longleftrightarrow> of_int z - 1 < x"
  by (simp add: not_less [symmetric] ceiling_less_iff)

lemma ceiling_mono: "x \<ge> y \<Longrightarrow> \<lceil>x\<rceil> \<ge> \<lceil>y\<rceil>"
  unfolding ceiling_def by (simp add: floor_mono)

lemma ceiling_less_cancel: "\<lceil>x\<rceil> < \<lceil>y\<rceil> \<Longrightarrow> x < y"
  by (auto simp add: not_le [symmetric] ceiling_mono)

lemma ceiling_of_int [simp]: "\<lceil>of_int z\<rceil> = z"
  by (rule ceiling_unique) simp_all

lemma ceiling_of_nat [simp]: "\<lceil>of_nat n\<rceil> = int n"
  using ceiling_of_int [of "of_nat n"] by simp

lemma ceiling_add_le: "\<lceil>x + y\<rceil> \<le> \<lceil>x\<rceil> + \<lceil>y\<rceil>"
  by (simp only: ceiling_le_iff of_int_add add_mono le_of_int_ceiling)

lemma mult_ceiling_le:
  assumes "0 \<le> a" and "0 \<le> b"
  shows "\<lceil>a * b\<rceil> \<le> \<lceil>a\<rceil> * \<lceil>b\<rceil>"
  by (metis assms ceiling_le_iff ceiling_mono le_of_int_ceiling mult_mono of_int_mult)

lemma mult_ceiling_le_Ints:
  assumes "0 \<le> a" "a \<in> Ints"
  shows "(of_int \<lceil>a * b\<rceil> :: 'a :: linordered_idom) \<le> of_int(\<lceil>a\<rceil> * \<lceil>b\<rceil>)"
  by (metis Ints_cases assms ceiling_le_iff ceiling_of_int le_of_int_ceiling mult_left_mono of_int_le_iff of_int_mult)

lemma finite_int_segment:
  fixes a :: "'a::floor_ceiling"
  shows "finite {x \<in> \<int>. a \<le> x \<and> x \<le> b}"
proof -
  have "finite {ceiling a..floor b}"
    by simp
  moreover have "{x \<in> \<int>. a \<le> x \<and> x \<le> b} = of_int ` {ceiling a..floor b}"
    by (auto simp: le_floor_iff ceiling_le_iff elim!: Ints_cases)
  ultimately show ?thesis
    by simp
qed

corollary finite_abs_int_segment:
  fixes a :: "'a::floor_ceiling"
  shows "finite {k \<in> \<int>. \<bar>k\<bar> \<le> a}" 
  using finite_int_segment [of "-a" a] by (auto simp add: abs_le_iff conj_commute minus_le_iff)


subsubsection \<open>Ceiling with numerals.\<close>

lemma ceiling_zero [simp]: "\<lceil>0\<rceil> = 0"
  using ceiling_of_int [of 0] by simp

lemma ceiling_one [simp]: "\<lceil>1\<rceil> = 1"
  using ceiling_of_int [of 1] by simp

lemma ceiling_numeral [simp]: "\<lceil>numeral v\<rceil> = numeral v"
  using ceiling_of_int [of "numeral v"] by simp

lemma ceiling_neg_numeral [simp]: "\<lceil>- numeral v\<rceil> = - numeral v"
  using ceiling_of_int [of "- numeral v"] by simp

lemma ceiling_le_zero [simp]: "\<lceil>x\<rceil> \<le> 0 \<longleftrightarrow> x \<le> 0"
  by (simp add: ceiling_le_iff)

lemma ceiling_le_one [simp]: "\<lceil>x\<rceil> \<le> 1 \<longleftrightarrow> x \<le> 1"
  by (simp add: ceiling_le_iff)

lemma ceiling_le_numeral [simp]: "\<lceil>x\<rceil> \<le> numeral v \<longleftrightarrow> x \<le> numeral v"
  by (simp add: ceiling_le_iff)

lemma ceiling_le_neg_numeral [simp]: "\<lceil>x\<rceil> \<le> - numeral v \<longleftrightarrow> x \<le> - numeral v"
  by (simp add: ceiling_le_iff)

lemma ceiling_less_zero [simp]: "\<lceil>x\<rceil> < 0 \<longleftrightarrow> x \<le> -1"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_one [simp]: "\<lceil>x\<rceil> < 1 \<longleftrightarrow> x \<le> 0"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_numeral [simp]: "\<lceil>x\<rceil> < numeral v \<longleftrightarrow> x \<le> numeral v - 1"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_neg_numeral [simp]: "\<lceil>x\<rceil> < - numeral v \<longleftrightarrow> x \<le> - numeral v - 1"
  by (simp add: ceiling_less_iff)

lemma zero_le_ceiling [simp]: "0 \<le> \<lceil>x\<rceil> \<longleftrightarrow> -1 < x"
  by (simp add: le_ceiling_iff)

lemma one_le_ceiling [simp]: "1 \<le> \<lceil>x\<rceil> \<longleftrightarrow> 0 < x"
  by (simp add: le_ceiling_iff)

lemma numeral_le_ceiling [simp]: "numeral v \<le> \<lceil>x\<rceil> \<longleftrightarrow> numeral v - 1 < x"
  by (simp add: le_ceiling_iff)

lemma neg_numeral_le_ceiling [simp]: "- numeral v \<le> \<lceil>x\<rceil> \<longleftrightarrow> - numeral v - 1 < x"
  by (simp add: le_ceiling_iff)

lemma zero_less_ceiling [simp]: "0 < \<lceil>x\<rceil> \<longleftrightarrow> 0 < x"
  by (simp add: less_ceiling_iff)

lemma one_less_ceiling [simp]: "1 < \<lceil>x\<rceil> \<longleftrightarrow> 1 < x"
  by (simp add: less_ceiling_iff)

lemma numeral_less_ceiling [simp]: "numeral v < \<lceil>x\<rceil> \<longleftrightarrow> numeral v < x"
  by (simp add: less_ceiling_iff)

lemma neg_numeral_less_ceiling [simp]: "- numeral v < \<lceil>x\<rceil> \<longleftrightarrow> - numeral v < x"
  by (simp add: less_ceiling_iff)

lemma ceiling_altdef: "\<lceil>x\<rceil> = (if x = of_int \<lfloor>x\<rfloor> then \<lfloor>x\<rfloor> else \<lfloor>x\<rfloor> + 1)"
  by (intro ceiling_unique; simp, linarith?)

lemma floor_le_ceiling [simp]: "\<lfloor>x\<rfloor> \<le> \<lceil>x\<rceil>"
  by (simp add: ceiling_altdef)


subsubsection \<open>Addition and subtraction of integers.\<close>

lemma ceiling_add_of_int [simp]: "\<lceil>x + of_int z\<rceil> = \<lceil>x\<rceil> + z"
  using ceiling_correct [of x] by (simp add: ceiling_def)

lemma ceiling_add_numeral [simp]: "\<lceil>x + numeral v\<rceil> = \<lceil>x\<rceil> + numeral v"
  using ceiling_add_of_int [of x "numeral v"] by simp

lemma ceiling_add_one [simp]: "\<lceil>x + 1\<rceil> = \<lceil>x\<rceil> + 1"
  using ceiling_add_of_int [of x 1] by simp

lemma ceiling_diff_of_int [simp]: "\<lceil>x - of_int z\<rceil> = \<lceil>x\<rceil> - z"
  using ceiling_add_of_int [of x "- z"] by (simp add: algebra_simps)

lemma ceiling_diff_numeral [simp]: "\<lceil>x - numeral v\<rceil> = \<lceil>x\<rceil> - numeral v"
  using ceiling_diff_of_int [of x "numeral v"] by simp

lemma ceiling_diff_one [simp]: "\<lceil>x - 1\<rceil> = \<lceil>x\<rceil> - 1"
  using ceiling_diff_of_int [of x 1] by simp

lemma ceiling_split[linarith_split]: "P \<lceil>t\<rceil> \<longleftrightarrow> (\<forall>i. of_int i - 1 < t \<and> t \<le> of_int i \<longrightarrow> P i)"
  by (auto simp add: ceiling_unique ceiling_correct)

lemma ceiling_diff_floor_le_1: "\<lceil>x\<rceil> - \<lfloor>x\<rfloor> \<le> 1"
proof -
  have "of_int \<lceil>x\<rceil> - 1 < x"
    using ceiling_correct[of x] by simp
  also have "x < of_int \<lfloor>x\<rfloor> + 1"
    using floor_correct[of x] by simp_all
  finally have "of_int (\<lceil>x\<rceil> - \<lfloor>x\<rfloor>) < (of_int 2::'a)"
    by simp
  then show ?thesis
    unfolding of_int_less_iff by simp
qed

lemma nat_approx_posE:
  fixes e:: "'a::{archimedean_field,floor_ceiling}"
  assumes "0 < e"
  obtains n :: nat where "1 / of_nat(Suc n) < e"
proof 
  have "(1::'a) / of_nat (Suc (nat \<lceil>1/e\<rceil>)) < 1 / of_int (\<lceil>1/e\<rceil>)"
  proof (rule divide_strict_left_mono)
    show "(of_int \<lceil>1 / e\<rceil>::'a) < of_nat (Suc (nat \<lceil>1 / e\<rceil>))"
      using assms by (simp add: field_simps)
    show "(0::'a) < of_nat (Suc (nat \<lceil>1 / e\<rceil>)) * of_int \<lceil>1 / e\<rceil>"
      using assms by (auto simp: zero_less_mult_iff pos_add_strict)
  qed auto
  also have "1 / of_int (\<lceil>1/e\<rceil>) \<le> 1 / (1/e)"
    by (rule divide_left_mono) (auto simp: \<open>0 < e\<close> ceiling_correct)
  also have "\<dots> = e" by simp
  finally show  "1 / of_nat (Suc (nat \<lceil>1 / e\<rceil>)) < e"
    by metis 
qed

lemma ceiling_divide_upper:
  fixes q :: "'a::floor_ceiling"
  shows "q > 0 \<Longrightarrow> p \<le> of_int (ceiling (p / q)) * q"
  by (meson divide_le_eq le_of_int_ceiling)

lemma ceiling_divide_lower:
  fixes q :: "'a::floor_ceiling"
  shows "q > 0 \<Longrightarrow> (of_int \<lceil>p / q\<rceil> - 1) * q < p"
  by (meson ceiling_eq_iff pos_less_divide_eq)

subsection \<open>Negation\<close>

lemma floor_minus: "\<lfloor>- x\<rfloor> = - \<lceil>x\<rceil>"
  unfolding ceiling_def by simp

lemma ceiling_minus: "\<lceil>- x\<rceil> = - \<lfloor>x\<rfloor>"
  unfolding ceiling_def by simp

subsection \<open>Natural numbers\<close>

lemma of_nat_floor: "r\<ge>0 \<Longrightarrow> of_nat (nat \<lfloor>r\<rfloor>) \<le> r"
  by simp

lemma of_nat_ceiling: "of_nat (nat \<lceil>r\<rceil>) \<ge> r"
  by (cases "r\<ge>0") auto

lemma of_nat_int_floor [simp]: "x\<ge>0 \<Longrightarrow> of_nat (nat\<lfloor>x\<rfloor>) = of_int \<lfloor>x\<rfloor>"
  by auto

lemma of_nat_int_ceiling [simp]: "x\<ge>0 \<Longrightarrow> of_nat (nat \<lceil>x\<rceil>) = of_int \<lceil>x\<rceil>"
  by auto

subsection \<open>Frac Function\<close>

definition frac :: "'a \<Rightarrow> 'a::floor_ceiling"
  where "frac x \<equiv> x - of_int \<lfloor>x\<rfloor>"

lemma frac_lt_1: "frac x < 1"
  by (simp add: frac_def) linarith

lemma frac_eq_0_iff [simp]: "frac x = 0 \<longleftrightarrow> x \<in> \<int>"
  by (simp add: frac_def) (metis Ints_cases Ints_of_int floor_of_int )

lemma frac_ge_0 [simp]: "frac x \<ge> 0"
  unfolding frac_def by linarith

lemma frac_gt_0_iff [simp]: "frac x > 0 \<longleftrightarrow> x \<notin> \<int>"
  by (metis frac_eq_0_iff frac_ge_0 le_less less_irrefl)

lemma frac_of_int [simp]: "frac (of_int z) = 0"
  by (simp add: frac_def)

lemma frac_frac [simp]: "frac (frac x) = frac x"
  by (simp add: frac_def)

lemma floor_add: "\<lfloor>x + y\<rfloor> = (if frac x + frac y < 1 then \<lfloor>x\<rfloor> + \<lfloor>y\<rfloor> else (\<lfloor>x\<rfloor> + \<lfloor>y\<rfloor>) + 1)"
proof -
  have "x + y < 1 + (of_int \<lfloor>x\<rfloor> + of_int \<lfloor>y\<rfloor>) \<Longrightarrow> \<lfloor>x + y\<rfloor> = \<lfloor>x\<rfloor> + \<lfloor>y\<rfloor>"
    by (metis add.commute floor_unique le_floor_add le_floor_iff of_int_add)
  moreover
  have "\<not> x + y < 1 + (of_int \<lfloor>x\<rfloor> + of_int \<lfloor>y\<rfloor>) \<Longrightarrow> \<lfloor>x + y\<rfloor> = 1 + (\<lfloor>x\<rfloor> + \<lfloor>y\<rfloor>)"
    apply (simp add: floor_eq_iff)
    apply (auto simp add: algebra_simps)
    apply linarith
    done
  ultimately show ?thesis by (auto simp add: frac_def algebra_simps)
qed

lemma floor_add2[simp]: "x \<in> \<int> \<or> y \<in> \<int> \<Longrightarrow> \<lfloor>x + y\<rfloor> = \<lfloor>x\<rfloor> + \<lfloor>y\<rfloor>"
by (metis add.commute add.left_neutral frac_lt_1 floor_add frac_eq_0_iff)

lemma frac_add:
  "frac (x + y) = (if frac x + frac y < 1 then frac x + frac y else (frac x + frac y) - 1)"
  by (simp add: frac_def floor_add)

lemma frac_unique_iff: "frac x = a \<longleftrightarrow> x - a \<in> \<int> \<and> 0 \<le> a \<and> a < 1"
  for x :: "'a::floor_ceiling"
  apply (auto simp: Ints_def frac_def algebra_simps floor_unique)
   apply linarith+
  done

lemma frac_eq: "frac x = x \<longleftrightarrow> 0 \<le> x \<and> x < 1"
  by (simp add: frac_unique_iff)

lemma frac_neg: "frac (- x) = (if x \<in> \<int> then 0 else 1 - frac x)"
  for x :: "'a::floor_ceiling"
  apply (auto simp add: frac_unique_iff)
   apply (simp add: frac_def)
  apply (meson frac_lt_1 less_iff_diff_less_0 not_le not_less_iff_gr_or_eq)
  done

lemma frac_in_Ints_iff [simp]: "frac x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
proof safe
  assume "frac x \<in> \<int>"
  hence "of_int \<lfloor>x\<rfloor> + frac x \<in> \<int>" by auto
  also have "of_int \<lfloor>x\<rfloor> + frac x = x" by (simp add: frac_def)
  finally show "x \<in> \<int>" .
qed (auto simp: frac_def)

lemma frac_1_eq: "frac (x+1) = frac x"
  by (simp add: frac_def)


subsection \<open>Fractional part arithmetic\<close>
text \<open>Many thanks to Stepan Holub\<close>

lemma frac_non_zero: "frac x \<noteq> 0 \<Longrightarrow> frac (-x) =  1 - frac x"
  using frac_eq_0_iff frac_neg by metis

lemma frac_add_simps [simp]: 
   "frac (frac a + b) = frac (a + b)"
   "frac (a + frac b) = frac (a + b)"      
  by (simp_all add: frac_add)

lemma frac_neg_frac:  "frac (- frac x) = frac (-x)"
  unfolding frac_neg frac_frac by force

lemma frac_diff_simp: "frac (y - frac x) = frac (y - x)"
    unfolding diff_conv_add_uminus frac_add frac_neg_frac..

lemma frac_diff: "frac (a - b) = frac (frac a + (- frac b))" 
  unfolding frac_add_simps(1) 
  unfolding ab_group_add_class.ab_diff_conv_add_uminus[symmetric] frac_diff_simp..

lemma frac_diff_pos: "frac x \<le> frac y \<Longrightarrow> frac (y - x) = frac y - frac x"
  unfolding diff_conv_add_uminus frac_add frac_neg
  using frac_lt_1 by force 
   
lemma frac_diff_neg: assumes "frac y < frac x" 
  shows "frac (y - x) = frac y + 1 - frac x"
proof-
  have "x \<notin> \<int>"
    unfolding frac_gt_0_iff[symmetric]
    using assms frac_ge_0[of y] by order
  have "frac y + (1 + - frac x) < 1"
    using frac_lt_1[of x] assms by fastforce
  show ?thesis
    unfolding diff_conv_add_uminus frac_add frac_neg 
    if_not_P[OF \<open>x \<notin> \<int>\<close>] if_P[OF \<open>frac y + (1 + - frac x) < 1\<close>]
    by simp
qed

lemma frac_diff_eq: assumes "frac y = frac x" 
  shows "frac (y - x) = 0"
  by (simp add: assms frac_diff_pos)

lemma frac_diff_zero: assumes "frac (x - y) = 0"
  shows "frac x = frac y"
  using frac_add_simps(1)[of "x - y" y, symmetric]
  unfolding assms add.group_left_neutral diff_add_cancel.

lemma frac_neg_eq_iff: "frac (-x) = frac (-y) \<longleftrightarrow> frac x = frac y"
  using add.inverse_inverse frac_neg_frac by metis

subsection \<open>Rounding to the nearest integer\<close>

definition round :: "'a::floor_ceiling \<Rightarrow> int"
  where "round x = \<lfloor>x + 1/2\<rfloor>"

lemma of_int_round_ge: "of_int (round x) \<ge> x - 1/2"
  and of_int_round_le: "of_int (round x) \<le> x + 1/2"
  and of_int_round_abs_le: "\<bar>of_int (round x) - x\<bar> \<le> 1/2"
  and of_int_round_gt: "of_int (round x) > x - 1/2"
proof -
  from floor_correct[of "x + 1/2"] have "x + 1/2 < of_int (round x) + 1"
    by (simp add: round_def)
  from add_strict_right_mono[OF this, of "-1"] show A: "of_int (round x) > x - 1/2"
    by simp
  then show "of_int (round x) \<ge> x - 1/2"
    by simp
  from floor_correct[of "x + 1/2"] show "of_int (round x) \<le> x + 1/2"
    by (simp add: round_def)
  with A show "\<bar>of_int (round x) - x\<bar> \<le> 1/2"
    by linarith
qed

lemma round_of_int [simp]: "round (of_int n) = n"
  unfolding round_def by (subst floor_eq_iff) force

lemma round_0 [simp]: "round 0 = 0"
  using round_of_int[of 0] by simp

lemma round_1 [simp]: "round 1 = 1"
  using round_of_int[of 1] by simp

lemma round_numeral [simp]: "round (numeral n) = numeral n"
  using round_of_int[of "numeral n"] by simp

lemma round_neg_numeral [simp]: "round (-numeral n) = -numeral n"
  using round_of_int[of "-numeral n"] by simp

lemma round_of_nat [simp]: "round (of_nat n) = of_nat n"
  using round_of_int[of "int n"] by simp

lemma round_mono: "x \<le> y \<Longrightarrow> round x \<le> round y"
  unfolding round_def by (intro floor_mono) simp

lemma round_unique: "of_int y > x - 1/2 \<Longrightarrow> of_int y \<le> x + 1/2 \<Longrightarrow> round x = y"
  unfolding round_def
proof (rule floor_unique)
  assume "x - 1 / 2 < of_int y"
  from add_strict_left_mono[OF this, of 1] show "x + 1 / 2 < of_int y + 1"
    by simp
qed

lemma round_unique': "\<bar>x - of_int n\<bar> < 1/2 \<Longrightarrow> round x = n"
  by (subst (asm) abs_less_iff, rule round_unique) (simp_all add: field_simps)

lemma round_altdef: "round x = (if frac x \<ge> 1/2 then \<lceil>x\<rceil> else \<lfloor>x\<rfloor>)"
  by (cases "frac x \<ge> 1/2")
    (rule round_unique, ((simp add: frac_def field_simps ceiling_altdef; linarith)+)[2])+

lemma floor_le_round: "\<lfloor>x\<rfloor> \<le> round x"
  unfolding round_def by (intro floor_mono) simp

lemma ceiling_ge_round: "\<lceil>x\<rceil> \<ge> round x"
  unfolding round_altdef by simp

lemma round_diff_minimal: "\<bar>z - of_int (round z)\<bar> \<le> \<bar>z - of_int m\<bar>"
  for z :: "'a::floor_ceiling"
proof (cases "of_int m \<ge> z")
  case True
  then have "\<bar>z - of_int (round z)\<bar> \<le> \<bar>of_int \<lceil>z\<rceil> - z\<bar>"
    unfolding round_altdef by (simp add: field_simps ceiling_altdef frac_def) linarith
  also have "of_int \<lceil>z\<rceil> - z \<ge> 0"
    by linarith
  with True have "\<bar>of_int \<lceil>z\<rceil> - z\<bar> \<le> \<bar>z - of_int m\<bar>"
    by (simp add: ceiling_le_iff)
  finally show ?thesis .
next
  case False
  then have "\<bar>z - of_int (round z)\<bar> \<le> \<bar>of_int \<lfloor>z\<rfloor> - z\<bar>"
    unfolding round_altdef by (simp add: field_simps ceiling_altdef frac_def) linarith
  also have "z - of_int \<lfloor>z\<rfloor> \<ge> 0"
    by linarith
  with False have "\<bar>of_int \<lfloor>z\<rfloor> - z\<bar> \<le> \<bar>z - of_int m\<bar>"
    by (simp add: le_floor_iff)
  finally show ?thesis .
qed

bundle floor_ceiling_syntax
begin
notation floor  (\<open>(\<open>open_block notation=\<open>mixfix floor\<close>\<close>\<lfloor>_\<rfloor>)\<close>)
  and ceiling  (\<open>(\<open>open_block notation=\<open>mixfix ceiling\<close>\<close>\<lceil>_\<rceil>)\<close>)
end

end
