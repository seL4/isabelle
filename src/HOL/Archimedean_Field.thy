(*  Title:      HOL/Archimedean_Field.thy
    Author:     Brian Huffman
*)

header {* Archimedean Fields, Floor and Ceiling Functions *}

theory Archimedean_Field
imports Main
begin

subsection {* Class of Archimedean fields *}

text {* Archimedean fields have no infinite elements. *}

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

text {* Archimedean fields have no infinitesimal elements. *}

lemma ex_inverse_of_nat_Suc_less:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x" shows "\<exists>n. inverse (of_nat (Suc n)) < x"
proof -
  from `0 < x` have "0 < inverse x"
    by (rule positive_imp_inverse_positive)
  obtain n where "inverse x < of_nat n"
    using ex_less_of_nat ..
  then obtain m where "inverse x < of_nat (Suc m)"
    using `0 < inverse x` by (cases n) (simp_all del: of_nat_Suc)
  then have "inverse (of_nat (Suc m)) < inverse (inverse x)"
    using `0 < inverse x` by (rule less_imp_inverse_less)
  then have "inverse (of_nat (Suc m)) < x"
    using `0 < x` by (simp add: nonzero_inverse_inverse_eq)
  then show ?thesis ..
qed

lemma ex_inverse_of_nat_less:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x" shows "\<exists>n>0. inverse (of_nat n) < x"
  using ex_inverse_of_nat_Suc_less [OF `0 < x`] by auto

lemma ex_less_of_nat_mult:
  fixes x :: "'a::archimedean_field"
  assumes "0 < x" shows "\<exists>n. y < of_nat n * x"
proof -
  obtain n where "y / x < of_nat n" using ex_less_of_nat ..
  with `0 < x` have "y < of_nat n * x" by (simp add: pos_divide_less_eq)
  then show ?thesis ..
qed


subsection {* Existence and uniqueness of floor function *}

lemma exists_least_lemma:
  assumes "\<not> P 0" and "\<exists>n. P n"
  shows "\<exists>n. \<not> P n \<and> P (Suc n)"
proof -
  from `\<exists>n. P n` have "P (Least P)" by (rule LeastI_ex)
  with `\<not> P 0` obtain n where "Least P = Suc n"
    by (cases "Least P") auto
  then have "n < Least P" by simp
  then have "\<not> P n" by (rule not_less_Least)
  then have "\<not> P n \<and> P (Suc n)"
    using `P (Least P)` `Least P = Suc n` by simp
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
  then have
    "of_int y \<le> x" "x < of_int (y + 1)"
    "of_int z \<le> x" "x < of_int (z + 1)"
    by simp_all
  from le_less_trans [OF `of_int y \<le> x` `x < of_int (z + 1)`]
       le_less_trans [OF `of_int z \<le> x` `x < of_int (y + 1)`]
  show "y = z" by (simp del: of_int_add)
qed


subsection {* Floor function *}

class floor_ceiling = archimedean_field +
  fixes floor :: "'a \<Rightarrow> int"
  assumes floor_correct: "of_int (floor x) \<le> x \<and> x < of_int (floor x + 1)"

notation (xsymbols)
  floor  ("\<lfloor>_\<rfloor>")

notation (HTML output)
  floor  ("\<lfloor>_\<rfloor>")

lemma floor_unique: "\<lbrakk>of_int z \<le> x; x < of_int z + 1\<rbrakk> \<Longrightarrow> floor x = z"
  using floor_correct [of x] floor_exists1 [of x] by auto

lemma of_int_floor_le: "of_int (floor x) \<le> x"
  using floor_correct ..

lemma le_floor_iff: "z \<le> floor x \<longleftrightarrow> of_int z \<le> x"
proof
  assume "z \<le> floor x"
  then have "(of_int z :: 'a) \<le> of_int (floor x)" by simp
  also have "of_int (floor x) \<le> x" by (rule of_int_floor_le)
  finally show "of_int z \<le> x" .
next
  assume "of_int z \<le> x"
  also have "x < of_int (floor x + 1)" using floor_correct ..
  finally show "z \<le> floor x" by (simp del: of_int_add)
qed

lemma floor_less_iff: "floor x < z \<longleftrightarrow> x < of_int z"
  by (simp add: not_le [symmetric] le_floor_iff)

lemma less_floor_iff: "z < floor x \<longleftrightarrow> of_int z + 1 \<le> x"
  using le_floor_iff [of "z + 1" x] by auto

lemma floor_le_iff: "floor x \<le> z \<longleftrightarrow> x < of_int z + 1"
  by (simp add: not_less [symmetric] less_floor_iff)

lemma floor_mono: assumes "x \<le> y" shows "floor x \<le> floor y"
proof -
  have "of_int (floor x) \<le> x" by (rule of_int_floor_le)
  also note `x \<le> y`
  finally show ?thesis by (simp add: le_floor_iff)
qed

lemma floor_less_cancel: "floor x < floor y \<Longrightarrow> x < y"
  by (auto simp add: not_le [symmetric] floor_mono)

lemma floor_of_int [simp]: "floor (of_int z) = z"
  by (rule floor_unique) simp_all

lemma floor_of_nat [simp]: "floor (of_nat n) = int n"
  using floor_of_int [of "of_nat n"] by simp

lemma le_floor_add: "floor x + floor y \<le> floor (x + y)"
  by (simp only: le_floor_iff of_int_add add_mono of_int_floor_le)

text {* Floor with numerals *}

lemma floor_zero [simp]: "floor 0 = 0"
  using floor_of_int [of 0] by simp

lemma floor_one [simp]: "floor 1 = 1"
  using floor_of_int [of 1] by simp

lemma floor_numeral [simp]: "floor (numeral v) = numeral v"
  using floor_of_int [of "numeral v"] by simp

lemma floor_neg_numeral [simp]: "floor (neg_numeral v) = neg_numeral v"
  using floor_of_int [of "neg_numeral v"] by simp

lemma zero_le_floor [simp]: "0 \<le> floor x \<longleftrightarrow> 0 \<le> x"
  by (simp add: le_floor_iff)

lemma one_le_floor [simp]: "1 \<le> floor x \<longleftrightarrow> 1 \<le> x"
  by (simp add: le_floor_iff)

lemma numeral_le_floor [simp]:
  "numeral v \<le> floor x \<longleftrightarrow> numeral v \<le> x"
  by (simp add: le_floor_iff)

lemma neg_numeral_le_floor [simp]:
  "neg_numeral v \<le> floor x \<longleftrightarrow> neg_numeral v \<le> x"
  by (simp add: le_floor_iff)

lemma zero_less_floor [simp]: "0 < floor x \<longleftrightarrow> 1 \<le> x"
  by (simp add: less_floor_iff)

lemma one_less_floor [simp]: "1 < floor x \<longleftrightarrow> 2 \<le> x"
  by (simp add: less_floor_iff)

lemma numeral_less_floor [simp]:
  "numeral v < floor x \<longleftrightarrow> numeral v + 1 \<le> x"
  by (simp add: less_floor_iff)

lemma neg_numeral_less_floor [simp]:
  "neg_numeral v < floor x \<longleftrightarrow> neg_numeral v + 1 \<le> x"
  by (simp add: less_floor_iff)

lemma floor_le_zero [simp]: "floor x \<le> 0 \<longleftrightarrow> x < 1"
  by (simp add: floor_le_iff)

lemma floor_le_one [simp]: "floor x \<le> 1 \<longleftrightarrow> x < 2"
  by (simp add: floor_le_iff)

lemma floor_le_numeral [simp]:
  "floor x \<le> numeral v \<longleftrightarrow> x < numeral v + 1"
  by (simp add: floor_le_iff)

lemma floor_le_neg_numeral [simp]:
  "floor x \<le> neg_numeral v \<longleftrightarrow> x < neg_numeral v + 1"
  by (simp add: floor_le_iff)

lemma floor_less_zero [simp]: "floor x < 0 \<longleftrightarrow> x < 0"
  by (simp add: floor_less_iff)

lemma floor_less_one [simp]: "floor x < 1 \<longleftrightarrow> x < 1"
  by (simp add: floor_less_iff)

lemma floor_less_numeral [simp]:
  "floor x < numeral v \<longleftrightarrow> x < numeral v"
  by (simp add: floor_less_iff)

lemma floor_less_neg_numeral [simp]:
  "floor x < neg_numeral v \<longleftrightarrow> x < neg_numeral v"
  by (simp add: floor_less_iff)

text {* Addition and subtraction of integers *}

lemma floor_add_of_int [simp]: "floor (x + of_int z) = floor x + z"
  using floor_correct [of x] by (simp add: floor_unique)

lemma floor_add_numeral [simp]:
    "floor (x + numeral v) = floor x + numeral v"
  using floor_add_of_int [of x "numeral v"] by simp

lemma floor_add_neg_numeral [simp]:
    "floor (x + neg_numeral v) = floor x + neg_numeral v"
  using floor_add_of_int [of x "neg_numeral v"] by simp

lemma floor_add_one [simp]: "floor (x + 1) = floor x + 1"
  using floor_add_of_int [of x 1] by simp

lemma floor_diff_of_int [simp]: "floor (x - of_int z) = floor x - z"
  using floor_add_of_int [of x "- z"] by (simp add: algebra_simps)

lemma floor_diff_numeral [simp]:
  "floor (x - numeral v) = floor x - numeral v"
  using floor_diff_of_int [of x "numeral v"] by simp

lemma floor_diff_neg_numeral [simp]:
  "floor (x - neg_numeral v) = floor x - neg_numeral v"
  using floor_diff_of_int [of x "neg_numeral v"] by simp

lemma floor_diff_one [simp]: "floor (x - 1) = floor x - 1"
  using floor_diff_of_int [of x 1] by simp


subsection {* Ceiling function *}

definition
  ceiling :: "'a::floor_ceiling \<Rightarrow> int" where
  "ceiling x = - floor (- x)"

notation (xsymbols)
  ceiling  ("\<lceil>_\<rceil>")

notation (HTML output)
  ceiling  ("\<lceil>_\<rceil>")

lemma ceiling_correct: "of_int (ceiling x) - 1 < x \<and> x \<le> of_int (ceiling x)"
  unfolding ceiling_def using floor_correct [of "- x"] by simp

lemma ceiling_unique: "\<lbrakk>of_int z - 1 < x; x \<le> of_int z\<rbrakk> \<Longrightarrow> ceiling x = z"
  unfolding ceiling_def using floor_unique [of "- z" "- x"] by simp

lemma le_of_int_ceiling: "x \<le> of_int (ceiling x)"
  using ceiling_correct ..

lemma ceiling_le_iff: "ceiling x \<le> z \<longleftrightarrow> x \<le> of_int z"
  unfolding ceiling_def using le_floor_iff [of "- z" "- x"] by auto

lemma less_ceiling_iff: "z < ceiling x \<longleftrightarrow> of_int z < x"
  by (simp add: not_le [symmetric] ceiling_le_iff)

lemma ceiling_less_iff: "ceiling x < z \<longleftrightarrow> x \<le> of_int z - 1"
  using ceiling_le_iff [of x "z - 1"] by simp

lemma le_ceiling_iff: "z \<le> ceiling x \<longleftrightarrow> of_int z - 1 < x"
  by (simp add: not_less [symmetric] ceiling_less_iff)

lemma ceiling_mono: "x \<ge> y \<Longrightarrow> ceiling x \<ge> ceiling y"
  unfolding ceiling_def by (simp add: floor_mono)

lemma ceiling_less_cancel: "ceiling x < ceiling y \<Longrightarrow> x < y"
  by (auto simp add: not_le [symmetric] ceiling_mono)

lemma ceiling_of_int [simp]: "ceiling (of_int z) = z"
  by (rule ceiling_unique) simp_all

lemma ceiling_of_nat [simp]: "ceiling (of_nat n) = int n"
  using ceiling_of_int [of "of_nat n"] by simp

lemma ceiling_add_le: "ceiling (x + y) \<le> ceiling x + ceiling y"
  by (simp only: ceiling_le_iff of_int_add add_mono le_of_int_ceiling)

text {* Ceiling with numerals *}

lemma ceiling_zero [simp]: "ceiling 0 = 0"
  using ceiling_of_int [of 0] by simp

lemma ceiling_one [simp]: "ceiling 1 = 1"
  using ceiling_of_int [of 1] by simp

lemma ceiling_numeral [simp]: "ceiling (numeral v) = numeral v"
  using ceiling_of_int [of "numeral v"] by simp

lemma ceiling_neg_numeral [simp]: "ceiling (neg_numeral v) = neg_numeral v"
  using ceiling_of_int [of "neg_numeral v"] by simp

lemma ceiling_le_zero [simp]: "ceiling x \<le> 0 \<longleftrightarrow> x \<le> 0"
  by (simp add: ceiling_le_iff)

lemma ceiling_le_one [simp]: "ceiling x \<le> 1 \<longleftrightarrow> x \<le> 1"
  by (simp add: ceiling_le_iff)

lemma ceiling_le_numeral [simp]:
  "ceiling x \<le> numeral v \<longleftrightarrow> x \<le> numeral v"
  by (simp add: ceiling_le_iff)

lemma ceiling_le_neg_numeral [simp]:
  "ceiling x \<le> neg_numeral v \<longleftrightarrow> x \<le> neg_numeral v"
  by (simp add: ceiling_le_iff)

lemma ceiling_less_zero [simp]: "ceiling x < 0 \<longleftrightarrow> x \<le> -1"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_one [simp]: "ceiling x < 1 \<longleftrightarrow> x \<le> 0"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_numeral [simp]:
  "ceiling x < numeral v \<longleftrightarrow> x \<le> numeral v - 1"
  by (simp add: ceiling_less_iff)

lemma ceiling_less_neg_numeral [simp]:
  "ceiling x < neg_numeral v \<longleftrightarrow> x \<le> neg_numeral v - 1"
  by (simp add: ceiling_less_iff)

lemma zero_le_ceiling [simp]: "0 \<le> ceiling x \<longleftrightarrow> -1 < x"
  by (simp add: le_ceiling_iff)

lemma one_le_ceiling [simp]: "1 \<le> ceiling x \<longleftrightarrow> 0 < x"
  by (simp add: le_ceiling_iff)

lemma numeral_le_ceiling [simp]:
  "numeral v \<le> ceiling x \<longleftrightarrow> numeral v - 1 < x"
  by (simp add: le_ceiling_iff)

lemma neg_numeral_le_ceiling [simp]:
  "neg_numeral v \<le> ceiling x \<longleftrightarrow> neg_numeral v - 1 < x"
  by (simp add: le_ceiling_iff)

lemma zero_less_ceiling [simp]: "0 < ceiling x \<longleftrightarrow> 0 < x"
  by (simp add: less_ceiling_iff)

lemma one_less_ceiling [simp]: "1 < ceiling x \<longleftrightarrow> 1 < x"
  by (simp add: less_ceiling_iff)

lemma numeral_less_ceiling [simp]:
  "numeral v < ceiling x \<longleftrightarrow> numeral v < x"
  by (simp add: less_ceiling_iff)

lemma neg_numeral_less_ceiling [simp]:
  "neg_numeral v < ceiling x \<longleftrightarrow> neg_numeral v < x"
  by (simp add: less_ceiling_iff)

text {* Addition and subtraction of integers *}

lemma ceiling_add_of_int [simp]: "ceiling (x + of_int z) = ceiling x + z"
  using ceiling_correct [of x] by (simp add: ceiling_unique)

lemma ceiling_add_numeral [simp]:
    "ceiling (x + numeral v) = ceiling x + numeral v"
  using ceiling_add_of_int [of x "numeral v"] by simp

lemma ceiling_add_neg_numeral [simp]:
    "ceiling (x + neg_numeral v) = ceiling x + neg_numeral v"
  using ceiling_add_of_int [of x "neg_numeral v"] by simp

lemma ceiling_add_one [simp]: "ceiling (x + 1) = ceiling x + 1"
  using ceiling_add_of_int [of x 1] by simp

lemma ceiling_diff_of_int [simp]: "ceiling (x - of_int z) = ceiling x - z"
  using ceiling_add_of_int [of x "- z"] by (simp add: algebra_simps)

lemma ceiling_diff_numeral [simp]:
  "ceiling (x - numeral v) = ceiling x - numeral v"
  using ceiling_diff_of_int [of x "numeral v"] by simp

lemma ceiling_diff_neg_numeral [simp]:
  "ceiling (x - neg_numeral v) = ceiling x - neg_numeral v"
  using ceiling_diff_of_int [of x "neg_numeral v"] by simp

lemma ceiling_diff_one [simp]: "ceiling (x - 1) = ceiling x - 1"
  using ceiling_diff_of_int [of x 1] by simp

lemma ceiling_diff_floor_le_1: "ceiling x - floor x \<le> 1"
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

subsection {* Negation *}

lemma floor_minus: "floor (- x) = - ceiling x"
  unfolding ceiling_def by simp

lemma ceiling_minus: "ceiling (- x) = - floor x"
  unfolding ceiling_def by simp

end
