(*  Title:      HOL/Real/HahnBanach/Aux.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Auxiliary theorems *}  (* FIXME clean: many are in Ring_and_Field *)

theory Aux = Real + Bounds + Zorn:

text {* Some existing theorems are declared as extra introduction
or elimination rules, respectively. *}

lemmas [dest?] = chainD
lemmas chainE2 [elim?] = chainD2 [elim_format, standard]


text{* \medskip Some lemmas about orders. *}

lemma lt_imp_not_eq: "x < (y::'a::order) \<Longrightarrow> x \<noteq> y"
  by (simp add: order_less_le)

lemma le_noteq_imp_less:
  "x \<le> (r::'a::order) \<Longrightarrow> x \<noteq> r \<Longrightarrow> x < r"
proof -
  assume "x \<le> r" and ne:"x \<noteq> r"
  hence "x < r \<or> x = r" by (simp add: order_le_less)
  with ne show ?thesis by simp
qed


text {* \medskip Some lemmas for the reals. *}

lemma real_add_minus_eq: "x - y = (0::real) \<Longrightarrow> x = y"
  by simp

lemma abs_minus_one: "abs (- (1::real)) = 1"
  by simp

lemma real_mult_le_le_mono1a:
  "(0::real) \<le> z \<Longrightarrow> x \<le> y \<Longrightarrow> z * x  \<le> z * y"
  by (simp add: mult_left_mono)

text{*The next two results are needlessly weak*}
lemma real_mult_less_le_anti:
  "z < (0::real) \<Longrightarrow> x \<le> y \<Longrightarrow> z * y \<le> z * x"
  by (simp add: mult_left_mono_neg order_less_imp_le)

lemma real_mult_less_le_mono:
  "(0::real) < z \<Longrightarrow> x \<le> y \<Longrightarrow> z * x \<le> z * y"
  by (simp add: mult_left_mono order_less_imp_le)

lemma real_mult_inv_right1: "(x::real) \<noteq> 0 \<Longrightarrow> x * inverse x = 1"
  by simp

lemma real_mult_inv_left1: "(x::real) \<noteq> 0 \<Longrightarrow> inverse x * x = 1"
  by simp

lemma real_le_mult_order1a:
  "(0::real) \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x * y"
  by (simp add: zero_le_mult_iff)

lemma real_mult_diff_distrib:
  "a * (- x - (y::real)) = - a * x - a * y"
proof -
  have "- x - y = - x + - y" by simp
  also have "a * ... = a * - x + a * - y"
    by (simp only: right_distrib)
  also have "... = - a * x - a * y"
    by simp
  finally show ?thesis .
qed

lemma real_mult_diff_distrib2: "a * (x - (y::real)) = a * x - a * y"
proof -
  have "x - y = x + - y" by simp
  also have "a * ... = a * x + a * - y"
    by (simp only: right_distrib)
  also have "... = a * x - a * y"
    by simp
  finally show ?thesis .
qed

lemma real_minus_le: "- (x::real) \<le> y \<Longrightarrow> - y \<le> x"
  by simp

lemma real_diff_ineq_swap:
    "(d::real) - b \<le> c + a \<Longrightarrow> - a - b \<le> c - d"
  by simp

end
