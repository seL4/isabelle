(*  Title:      HOL/Archimedean_Field.thy
    Author:     Brian Huffman
*)

section \<open>Archimedean Fields, Floor and Ceiling Functions\<close>

theory Archimedean_Field
imports Main
begin

subsection \<open>Class of Archimedean fields\<close>

text \<open>Archimedean fields have no infinite elements.\<close>

class archimedean_field = linordered_field +
  assumes ex_le_of_int: "\<exists>z. x \<le> of_int z"

lemma ex_less_of_int:
  fixes x :: "'a::archimedean_field" shows "\<exists>z. x < of_int z"
proof -
  from ex_le_of_int obtain z where "x \<le> of_int z" ..
  then have "x < of_int (z + 1)" by simp
  then show ?thesis ..
qed

lemma ex_of_int_less:
  fixes x :: "'a::archimedean_field" shows "\<exists>z. of_int z < x"
proof -
  from ex_less_of_int obtain z where "- x < of_int z" ..
  then have "of_int (- z) < x" by simp
  then show ?thesis ..
qed

lemma ex_less_of_nat:
  fixes x :: "'a::archimedean_field" shows "\<exists>n. x < of_nat n"
proof -
  obtain z where "x < of_int z" using ex_less_of_int ..
  also have "\<dots> \<le> of_int (int (nat z))" by simp
  also have "\<dots> = of_nat (nat z)" by (simp only: of_int_of_nat_eq)
  finally show ?thesis ..
qed

lemma ex_le_of_nat:
  fixes x :: "'a::archimedean_field" shows "\<exists>n. x \<le> of_nat n"
proof -
  obtain n where "x < of_nat n" using ex_less_of_nat ..
  then have "x \<le> of_nat n" by simp
  then show ?thesis ..
qed

text \<open>Archimedean fields have no infinitesimal elements.\<close>

lemma ex_inverse_of_nat_Suc_less:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x" shows "\<exists>n. inverse (of_nat (Suc n)) < x"
proof -
  from \<open>0 < x\<close> have "0 < inverse x"
    by (rule positive_imp_inverse_positive)
  obtain n where "inverse x < of_nat n"
    using ex_less_of_nat ..
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
  assumes "0 < x" shows "\<exists>n>0. inverse (of_nat n) < x"
  using ex_inverse_of_nat_Suc_less [OF \<open>0 < x\<close>] by auto

lemma ex_less_of_nat_mult:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x" shows "\<exists>n. y < of_nat n * x"
proof -
  obtain n where "y / x < of_nat n" using ex_less_of_nat ..
  with \<open>0 < x\<close> have "y < of_nat n * x" by (simp add: pos_divide_less_eq)
  then show ?thesis ..
qed


subsection \<open>Existence and uniqueness of floor function\<close>

lemma exists_least_lemma:
  assumes "\<not> P 0" and "\<exists>n. P n"
  shows "\<exists>n. \<not> P n \<and> P (Suc n)"
proof -
  from \<open>\<exists>n. P n\<close> have "P (Least P)" by (rule LeastI_ex)
  with \<open>\<not> P 0\<close> obtain n where "Least P = Suc n"
    by (cases "Least P") auto
  then have "n < Least P" by simp
  then have "\<not> P n" by (rule not_less_Least)
  then have "\<not> P n \<and> P (Suc n)"
    using \<open>P (Least P)\<close> \<open>Least P = Suc n\<close> by simp
  then show ?thesis ..
qed

lemma floor_exists:
  fixes x :: "'a::archimedean_field"
  shows "\<exists>z. of_int z \<le> x \<and> x < of_int (z + 1)"
proof (cases)
  assume "0 \<le> x"
  then have "\<not> x < of_nat 0" by simp
  then have "\<exists>n. \<not> x < of_nat n \<and> x < of_nat (Suc n)"
    using ex_less_of_nat by (rule exists_least_lemma)
  then obtain n where "\<not> x < of_nat n \<and> x < of_nat (Suc n)" ..
  then have "of_int (int n) \<le> x \<and> x < of_int (int n + 1)" by simp
  then show ?thesis ..
next
  assume "\<not> 0 \<le> x"
  then have "\<not> - x \<le> of_nat 0" by simp
  then have "\<exists>n. \<not> - x \<le> of_nat n \<and> - x \<le> of_nat (Suc n)"
    using ex_le_of_nat by (rule exists_least_lemma)
  then obtain n where "\<not> - x \<le> of_nat n \<and> - x \<le> of_nat (Suc n)" ..
  then have "of_int (- int n - 1) \<le> x \<and> x < of_int (- int n - 1 + 1)" by simp
  then show ?thesis ..
qed

lemma floor_exists1:
  fixes x :: "'a::archimedean_field"
  shows "\<exists>!z. of_int z \<le> x \<and> x < of_int (z + 1)"
proof (rule ex_ex1I)
  show "\<exists>z. of_int z \<le> x \<and> x < of_int (z + 1)"
    by (rule floor_exists)
next
  fix y z assume
    "of_int y \<le> x \<and> x < of_int (y + 1)"
    "of_int z \<le> x \<and> x < of_int (z + 1)"
  with le_less_trans [of "of_int y" "x" "of_int (z + 1)"]
       le_less_trans [of "of_int z" "x" "of_int (y + 1)"]
  show "y = z" by (simp del: of_int_add)
qed


subsection \<open>Floor function\<close>

class floor_ceiling = archimedean_field +
  fixes floor :: "'a \<Rightarrow> int"  ("\<lfloor>_\<rfloor>")
  assumes floor_correct: "of_int \<lfloor>x\<rfloor> \<le> x \<and> x < of_int (\<lfloor>x\<rfloor> + 1)"

lemma floor_unique: "\<lbrakk>of_int z \<le> x; x < of_int z + 1\<rbrakk> \<Longrightarrow> \<lfloor>x\<rfloor> = z"
  using floor_correct [of x] floor_exists1 [of x] by auto

lemma floor_unique_iff:
  fixes x :: "'a::floor_ceiling"
  shows  "\<lfloor>x\<rfloor> = a \<longleftrightarrow> of_int a \<le> x \<and> x < of_int a + 1"
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

lemma floor_split[arith_split]: "P \<lfloor>t\<rfloor> \<longleftrightarrow> (\<forall>i. of_int i \<le> t \<and> t < of_int i + 1 \<longrightarrow> P i)"
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

text \<open>Floor with numerals\<close>

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

lemma numeral_le_floor [simp]:
  "numeral v \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> numeral v \<le> x"
  by (simp add: le_floor_iff)

lemma neg_numeral_le_floor [simp]:
  "- numeral v \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> - numeral v \<le> x"
  by (simp add: le_floor_iff)

lemma zero_less_floor [simp]: "0 < \<lfloor>x\<rfloor> \<longleftrightarrow> 1 \<le> x"
  by (simp add: less_floor_iff)

lemma one_less_floor [simp]: "1 < \<lfloor>x\<rfloor> \<longleftrightarrow> 2 \<le> x"
  by (simp add: less_floor_iff)

lemma numeral_less_floor [simp]:
  "numeral v < \<lfloor>x\<rfloor> \<longleftrightarrow> numeral v + 1 \<le> x"
  by (simp add: less_floor_iff)

lemma neg_numeral_less_floor [simp]:
  "- numeral v < \<lfloor>x\<rfloor> \<longleftrightarrow> - numeral v + 1 \<le> x"
  by (simp add: less_floor_iff)

lemma floor_le_zero [simp]: "\<lfloor>x\<rfloor> \<le> 0 \<longleftrightarrow> x < 1"
  by (simp add: floor_le_iff)

lemma floor_le_one [simp]: "\<lfloor>x\<rfloor> \<le> 1 \<longleftrightarrow> x < 2"
  by (simp add: floor_le_iff)

lemma floor_le_numeral [simp]:
  "\<lfloor>x\<rfloor> \<le> numeral v \<longleftrightarrow> x < numeral v + 1"
  by (simp add: floor_le_iff)

lemma floor_le_neg_numeral [simp]:
  "\<lfloor>x\<rfloor> \<le> - numeral v \<longleftrightarrow> x < - numeral v + 1"
  by (simp add: floor_le_iff)

lemma floor_less_zero [simp]: "\<lfloor>x\<rfloor> < 0 \<longleftrightarrow> x < 0"
  by (simp add: floor_less_iff)

lemma floor_less_one [simp]: "\<lfloor>x\<rfloor> < 1 \<longleftrightarrow> x < 1"
  by (simp add: floor_less_iff)

lemma floor_less_numeral [simp]:
  "\<lfloor>x\<rfloor> < numeral v \<longleftrightarrow> x < numeral v"
  by (simp add: floor_less_iff)

lemma floor_less_neg_numeral [simp]:
  "\<lfloor>x\<rfloor> < - numeral v \<longleftrightarrow> x < - numeral v"
  by (simp add: floor_less_iff)

text \<open>Addition and subtraction of integers\<close>

lemma floor_add_of_int [simp]: "\<lfloor>x + of_int z\<rfloor> = \<lfloor>x\<rfloor> + z"
  using floor_correct [of x] by (simp add: floor_unique)

lemma floor_add_numeral [simp]:
    "\<lfloor>x + numeral v\<rfloor> = \<lfloor>x\<rfloor> + numeral v"
  using floor_add_of_int [of x "numeral v"] by simp

lemma floor_add_one [simp]: "\<lfloor>x + 1\<rfloor> = \<lfloor>x\<rfloor> + 1"
  using floor_add_of_int [of x 1] by simp

lemma floor_diff_of_int [simp]: "\<lfloor>x - of_int z\<rfloor> = \<lfloor>x\<rfloor> - z"
  using floor_add_of_int [of x "- z"] by (simp add: algebra_simps)

lemma floor_uminus_of_int [simp]: "\<lfloor>- (of_int z)\<rfloor> = - z"
  by (metis floor_diff_of_int [of 0] diff_0 floor_zero)

lemma floor_diff_numeral [simp]:
  "\<lfloor>x - numeral v\<rfloor> = \<lfloor>x\<rfloor> - numeral v"
  using floor_diff_of_int [of x "numeral v"] by simp

lemma floor_diff_one [simp]: "\<lfloor>x - 1\<rfloor> = \<lfloor>x\<rfloor> - 1"
  using floor_diff_of_int [of x 1] by simp

lemma le_mult_floor:
  assumes "0 \<le> a" and "0 \<le> b"
  shows "\<lfloor>a\<rfloor> * \<lfloor>b\<rfloor> \<le> \<lfloor>a * b\<rfloor>"
proof -
  have "of_int \<lfloor>a\<rfloor> \<le> a"
    and "of_int \<lfloor>b\<rfloor> \<le> b" by (auto intro: of_int_floor_le)
  hence "of_int (\<lfloor>a\<rfloor> * \<lfloor>b\<rfloor>) \<le> a * b"
    using assms by (auto intro!: mult_mono)
  also have "a * b < of_int (\<lfloor>a * b\<rfloor> + 1)"
    using floor_correct[of "a * b"] by auto
  finally show ?thesis unfolding of_int_less_iff by simp
qed

lemma floor_divide_of_int_eq:
  fixes k l :: int
  shows "\<lfloor>of_int k / of_int l\<rfloor> = k div l"
proof (cases "l = 0")
  case True then show ?thesis by simp
next
  case False
  have *: "\<lfloor>of_int (k mod l) / of_int l :: 'a\<rfloor> = 0"
  proof (cases "l > 0")
    case True then show ?thesis
      by (auto intro: floor_unique)
  next
    case False
    obtain r where "r = - l" by blast
    then have l: "l = - r" by simp
    moreover with \<open>l \<noteq> 0\<close> False have "r > 0" by simp
    ultimately show ?thesis using pos_mod_bound [of r]
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
    by simp
  with * show ?thesis by simp
qed

lemma floor_divide_of_nat_eq:
  fixes m n :: nat
  shows "\<lfloor>of_nat m / of_nat n\<rfloor> = of_nat (m div n)"
proof (cases "n = 0")
  case True then show ?thesis by simp
next
  case False
  then have *: "\<lfloor>of_nat (m mod n) / of_nat n :: 'a\<rfloor> = 0"
    by (auto intro: floor_unique)
  have "(of_nat m :: 'a) = of_nat (m div n * n + m mod n)"
    by simp
  also have "\<dots> = (of_nat (m div n) + of_nat (m mod n) / of_nat n) * of_nat n"
    using False by (simp only: of_nat_add) (simp add: field_simps of_nat_mult)
  finally have "(of_nat m / of_nat n :: 'a) = \<dots> / of_nat n"
    by simp 
  then have "(of_nat m / of_nat n :: 'a) = of_nat (m div n) + of_nat (m mod n) / of_nat n"
    using False by (simp only:) simp
  then have "\<lfloor>of_nat m / of_nat n :: 'a\<rfloor> = \<lfloor>of_nat (m div n) + of_nat (m mod n) / of_nat n :: 'a\<rfloor>" 
    by simp
  then have "\<lfloor>of_nat m / of_nat n :: 'a\<rfloor> = \<lfloor>of_nat (m mod n) / of_nat n + of_nat (m div n) :: 'a\<rfloor>"
    by (simp add: ac_simps)
  moreover have "(of_nat (m div n) :: 'a) = of_int (of_nat (m div n))"
    by simp
  ultimately have "\<lfloor>of_nat m / of_nat n :: 'a\<rfloor> = \<lfloor>of_nat (m mod n) / of_nat n :: 'a\<rfloor> + of_nat (m div n)"
    by (simp only: floor_add_of_int)
  with * show ?thesis by simp
qed


subsection \<open>Ceiling function\<close>

definition ceiling :: "'a::floor_ceiling \<Rightarrow> int"  ("\<lceil>_\<rceil>")
  where "\<lceil>x\<rceil> = - \<lfloor>- x\<rfloor>"

lemma ceiling_correct: "of_int \<lceil>x\<rceil> - 1 < x \<and> x \<le> of_int \<lceil>x\<rceil>"
  unfolding ceiling_def using floor_correct [of "- x"] by (simp add: le_minus_iff) 

lemma ceiling_unique: "\<lbrakk>of_int z - 1 < x; x \<le> of_int z\<rbrakk> \<Longrightarrow> \<lceil>x\<rceil> = z"
  unfolding ceiling_def using floor_unique [of "- z" "- x"] by simp

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

text \<open>Ceiling with numerals\<close>

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

lemma ceiling_le_numeral [simp]:
  "\<lceil>x\<rceil> \<le> numeral v \<longleftrightarrow> x \<le> numeral v"
  by (simp add: ceiling_le_iff)

lemma ceiling_le_neg_numeral [simp]:
  "\<lceil>x\<rceil> \<le> - numeral v \<longleftrightarrow> x \<le> - numeral v"
  by (simp add: ceiling_le_iff)

lemma ceiling_less_zero [simp]: "\<lceil>x\<rceil> < 0 \<longleftrightarrow> x \<le> -1"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_one [simp]: "\<lceil>x\<rceil> < 1 \<longleftrightarrow> x \<le> 0"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_numeral [simp]:
  "\<lceil>x\<rceil> < numeral v \<longleftrightarrow> x \<le> numeral v - 1"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_neg_numeral [simp]:
  "\<lceil>x\<rceil> < - numeral v \<longleftrightarrow> x \<le> - numeral v - 1"
  by (simp add: ceiling_less_iff)

lemma zero_le_ceiling [simp]: "0 \<le> \<lceil>x\<rceil> \<longleftrightarrow> -1 < x"
  by (simp add: le_ceiling_iff)

lemma one_le_ceiling [simp]: "1 \<le> \<lceil>x\<rceil> \<longleftrightarrow> 0 < x"
  by (simp add: le_ceiling_iff)

lemma numeral_le_ceiling [simp]:
  "numeral v \<le> \<lceil>x\<rceil> \<longleftrightarrow> numeral v - 1 < x"
  by (simp add: le_ceiling_iff)

lemma neg_numeral_le_ceiling [simp]:
  "- numeral v \<le> \<lceil>x\<rceil> \<longleftrightarrow> - numeral v - 1 < x"
  by (simp add: le_ceiling_iff)

lemma zero_less_ceiling [simp]: "0 < \<lceil>x\<rceil> \<longleftrightarrow> 0 < x"
  by (simp add: less_ceiling_iff)

lemma one_less_ceiling [simp]: "1 < \<lceil>x\<rceil> \<longleftrightarrow> 1 < x"
  by (simp add: less_ceiling_iff)

lemma numeral_less_ceiling [simp]:
  "numeral v < \<lceil>x\<rceil> \<longleftrightarrow> numeral v < x"
  by (simp add: less_ceiling_iff)

lemma neg_numeral_less_ceiling [simp]:
  "- numeral v < \<lceil>x\<rceil> \<longleftrightarrow> - numeral v < x"
  by (simp add: less_ceiling_iff)

lemma ceiling_altdef: "\<lceil>x\<rceil> = (if x = of_int \<lfloor>x\<rfloor> then \<lfloor>x\<rfloor> else \<lfloor>x\<rfloor> + 1)"
  by (intro ceiling_unique, (simp, linarith?)+)

lemma floor_le_ceiling [simp]: "\<lfloor>x\<rfloor> \<le> \<lceil>x\<rceil>"
  by (simp add: ceiling_altdef)

text \<open>Addition and subtraction of integers\<close>

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

lemma ceiling_split[arith_split]: "P \<lceil>t\<rceil> \<longleftrightarrow> (\<forall>i. of_int i - 1 < t \<and> t \<le> of_int i \<longrightarrow> P i)"
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

subsection \<open>Negation\<close>

lemma floor_minus: "\<lfloor>- x\<rfloor> = - \<lceil>x\<rceil>"
  unfolding ceiling_def by simp

lemma ceiling_minus: "\<lceil>- x\<rceil> = - \<lfloor>x\<rfloor>"
  unfolding ceiling_def by simp


subsection \<open>Frac Function\<close>

definition frac :: "'a \<Rightarrow> 'a::floor_ceiling" where
  "frac x \<equiv> x - of_int \<lfloor>x\<rfloor>"

lemma frac_lt_1: "frac x < 1"
  by  (simp add: frac_def) linarith

lemma frac_eq_0_iff [simp]: "frac x = 0 \<longleftrightarrow> x \<in> \<int>"
  by (simp add: frac_def) (metis Ints_cases Ints_of_int floor_of_int )

lemma frac_ge_0 [simp]: "frac x \<ge> 0"
  unfolding frac_def
  by linarith

lemma frac_gt_0_iff [simp]: "frac x > 0 \<longleftrightarrow> x \<notin> \<int>"
  by (metis frac_eq_0_iff frac_ge_0 le_less less_irrefl)

lemma frac_of_int [simp]: "frac (of_int z) = 0"
  by (simp add: frac_def)

lemma floor_add: "\<lfloor>x + y\<rfloor> = (if frac x + frac y < 1 then \<lfloor>x\<rfloor> + \<lfloor>y\<rfloor> else (\<lfloor>x\<rfloor> + \<lfloor>y\<rfloor>) + 1)"  
proof -
  {assume "x + y < 1 + (of_int \<lfloor>x\<rfloor> + of_int \<lfloor>y\<rfloor>)"
   then have "\<lfloor>x + y\<rfloor> = \<lfloor>x\<rfloor> + \<lfloor>y\<rfloor>"
     by (metis add.commute floor_unique le_floor_add le_floor_iff of_int_add)
   }
  moreover
  { assume "\<not> x + y < 1 + (of_int \<lfloor>x\<rfloor> + of_int \<lfloor>y\<rfloor>)"
    then have "\<lfloor>x + y\<rfloor> = 1 + (\<lfloor>x\<rfloor> + \<lfloor>y\<rfloor>)"
      apply (simp add: floor_unique_iff)
      apply (auto simp add: algebra_simps)
      by linarith    
  }
  ultimately show ?thesis
    by (auto simp add: frac_def algebra_simps)
qed

lemma frac_add: "frac (x + y) = (if frac x + frac y < 1 then frac x + frac y
                                 else (frac x + frac y) - 1)"  
  by (simp add: frac_def floor_add)

lemma frac_unique_iff:
  fixes x :: "'a::floor_ceiling"
  shows  "(frac x) = a \<longleftrightarrow> x - a \<in> \<int> \<and> 0 \<le> a \<and> a < 1"
  apply (auto simp: Ints_def frac_def)
  apply linarith
  apply linarith
  by (metis (no_types) add.commute add.left_neutral eq_diff_eq floor_add_of_int floor_unique of_int_0)

lemma frac_eq: "(frac x) = x \<longleftrightarrow> 0 \<le> x \<and> x < 1"
  by (simp add: frac_unique_iff)
  
lemma frac_neg:
  fixes x :: "'a::floor_ceiling"
  shows  "frac (-x) = (if x \<in> \<int> then 0 else 1 - frac x)"
  apply (auto simp add: frac_unique_iff)
  apply (simp add: frac_def)
  by (meson frac_lt_1 less_iff_diff_less_0 not_le not_less_iff_gr_or_eq)


subsection \<open>Rounding to the nearest integer\<close>

definition round where "round x = \<lfloor>x + 1/2\<rfloor>"

lemma of_int_round_ge:     "of_int (round x) \<ge> x - 1/2"
  and of_int_round_le:     "of_int (round x) \<le> x + 1/2"
  and of_int_round_abs_le: "\<bar>of_int (round x) - x\<bar> \<le> 1/2"
  and of_int_round_gt:     "of_int (round x) > x - 1/2"
proof -
  from floor_correct[of "x + 1/2"] have "x + 1/2 < of_int (round x) + 1" by (simp add: round_def)
  from add_strict_right_mono[OF this, of "-1"] show A: "of_int (round x) > x - 1/2" by simp
  thus "of_int (round x) \<ge> x - 1/2" by simp
  from floor_correct[of "x + 1/2"] show "of_int (round x) \<le> x + 1/2" by (simp add: round_def)
  with A show "\<bar>of_int (round x) - x\<bar> \<le> 1/2" by linarith
qed

lemma round_of_int [simp]: "round (of_int n) = n"
  unfolding round_def by (subst floor_unique_iff) force

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
  from add_strict_left_mono[OF this, of 1] show "x + 1 / 2 < of_int y + 1" by simp
qed

lemma round_altdef: "round x = (if frac x \<ge> 1/2 then \<lceil>x\<rceil> else \<lfloor>x\<rfloor>)"
  by (cases "frac x \<ge> 1/2")
     (rule round_unique, ((simp add: frac_def field_simps ceiling_altdef, linarith?)+)[2])+

lemma floor_le_round: "\<lfloor>x\<rfloor> \<le> round x"
  unfolding round_def by (intro floor_mono) simp

lemma ceiling_ge_round: "\<lceil>x\<rceil> \<ge> round x" unfolding round_altdef by simp
     
lemma round_diff_minimal: 
  fixes z :: "'a :: floor_ceiling"
  shows "\<bar>z - of_int (round z)\<bar> \<le> \<bar>z - of_int m\<bar>"
proof (cases "of_int m \<ge> z")
  case True
  hence "\<bar>z - of_int (round z)\<bar> \<le> \<bar>of_int \<lceil>z\<rceil> - z\<bar>"
    unfolding round_altdef by (simp add: field_simps ceiling_altdef frac_def) linarith?
  also have "of_int \<lceil>z\<rceil> - z \<ge> 0" by linarith
  with True have "\<bar>of_int \<lceil>z\<rceil> - z\<bar> \<le> \<bar>z - of_int m\<bar>"
    by (simp add: ceiling_le_iff)
  finally show ?thesis .
next
  case False
  hence "\<bar>z - of_int (round z)\<bar> \<le> \<bar>of_int \<lfloor>z\<rfloor> - z\<bar>"
    unfolding round_altdef by (simp add: field_simps ceiling_altdef frac_def) linarith?
  also have "z - of_int \<lfloor>z\<rfloor> \<ge> 0" by linarith
  with False have "\<bar>of_int \<lfloor>z\<rfloor> - z\<bar> \<le> \<bar>z - of_int m\<bar>"
    by (simp add: le_floor_iff)
  finally show ?thesis .
qed

end
