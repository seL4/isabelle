(*  Title:      HOL/Real/HahnBanach/Aux.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Auxiliary theorems *}

theory Aux = Real + Zorn:

text {* Some existing theorems are declared as extra introduction
or elimination rules, respectively. *}

lemmas [intro?] = isLub_isUb
lemmas [intro?] = chainD
lemmas chainE2 = chainD2 [elim_format, standard]


text {* \medskip Lemmas about sets. *}

lemma Int_singletonD: "A \\<inter> B = {v} \\<Longrightarrow> x \\<in> A \\<Longrightarrow> x \\<in> B \\<Longrightarrow> x = v"
  by (fast elim: equalityE)

lemma set_less_imp_diff_not_empty: "H < E \\<Longrightarrow> \\<exists>x0 \\<in> E. x0 \\<notin> H"
  by (auto simp add: psubset_eq)


text{* \medskip Some lemmas about orders. *}

lemma lt_imp_not_eq: "x < (y::'a::order) \\<Longrightarrow> x \\<noteq> y"
  by (simp add: order_less_le)

lemma le_noteq_imp_less:
  "x \\<le> (r::'a::order) \\<Longrightarrow> x \\<noteq> r \\<Longrightarrow> x < r"
proof -
  assume "x \\<le> r" and ne:"x \\<noteq> r"
  hence "x < r \\<or> x = r" by (simp add: order_le_less)
  with ne show ?thesis by simp
qed


text {* \medskip Some lemmas for the reals. *}

lemma real_add_minus_eq: "x - y = (#0::real) \\<Longrightarrow> x = y"
  by simp

lemma abs_minus_one: "abs (- (#1::real)) = #1"
  by simp

lemma real_mult_le_le_mono1a:
  "(#0::real) \\<le> z \\<Longrightarrow> x \\<le> y \\<Longrightarrow> z * x  \\<le> z * y"
proof -
  assume z: "(#0::real) \\<le> z" and "x \\<le> y"
  hence "x < y \\<or> x = y" by (auto simp add: order_le_less)
  thus ?thesis
  proof
    assume "x < y" show ?thesis by  (rule real_mult_le_less_mono2) simp
  next
    assume "x = y" thus ?thesis by simp
  qed
qed

lemma real_mult_le_le_mono2:
  "(#0::real) \\<le> z \\<Longrightarrow> x \\<le> y \\<Longrightarrow> x * z \\<le> y * z"
proof -
  assume "(#0::real) \\<le> z"  "x \\<le> y"
  hence "x < y \\<or> x = y" by (auto simp add: order_le_less)
  thus ?thesis
  proof
    assume "x < y"
    show ?thesis by (rule real_mult_le_less_mono1) (simp!)
  next
    assume "x = y"
    thus ?thesis by simp
  qed
qed

lemma real_mult_less_le_anti:
  "z < (#0::real) \\<Longrightarrow> x \\<le> y \\<Longrightarrow> z * y \\<le> z * x"
proof -
  assume "z < #0"  "x \\<le> y"
  hence "#0 < - z" by simp
  hence "#0 \\<le> - z" by (rule order_less_imp_le)
  hence "x * (- z) \\<le> y * (- z)"
    by (rule real_mult_le_le_mono2)
  hence  "- (x * z) \\<le> - (y * z)"
    by (simp only: real_minus_mult_eq2)
  thus ?thesis by (simp only: real_mult_commute)
qed

lemma real_mult_less_le_mono:
  "(#0::real) < z \\<Longrightarrow> x \\<le> y \\<Longrightarrow> z * x \\<le> z * y"
proof -
  assume "#0 < z"  "x \\<le> y"
  have "#0 \\<le> z" by (rule order_less_imp_le)
  hence "x * z \\<le> y * z"
    by (rule real_mult_le_le_mono2)
  thus ?thesis by (simp only: real_mult_commute)
qed

lemma real_inverse_gt_zero1: "#0 < (x::real) \\<Longrightarrow> #0 < inverse x"
proof -
  assume "#0 < x"
  have "0 < x" by simp
  hence "0 < inverse x" by (rule real_inverse_gt_zero)
  thus ?thesis by simp
qed

lemma real_mult_inv_right1: "(x::real) \\<noteq> #0 \\<Longrightarrow> x * inverse x = #1"
  by simp

lemma real_mult_inv_left1: "(x::real) \\<noteq> #0 \\<Longrightarrow> inverse x * x = #1"
  by simp

lemma real_le_mult_order1a:
  "(#0::real) \\<le> x \\<Longrightarrow> #0 \\<le> y \\<Longrightarrow> #0 \\<le> x * y"
proof -
  assume "#0 \\<le> x"  "#0 \\<le> y"
  have "0 \\<le> x \\<Longrightarrow> 0 \\<le> y \\<Longrightarrow> 0 \\<le> x * y"
    by (rule real_le_mult_order)
  thus ?thesis by (simp!)
qed

lemma real_mult_diff_distrib:
  "a * (- x - (y::real)) = - a * x - a * y"
proof -
  have "- x - y = - x + - y" by simp
  also have "a * ... = a * - x + a * - y"
    by (simp only: real_add_mult_distrib2)
  also have "... = - a * x - a * y"
    by simp
  finally show ?thesis .
qed

lemma real_mult_diff_distrib2: "a * (x - (y::real)) = a * x - a * y"
proof -
  have "x - y = x + - y" by simp
  also have "a * ... = a * x + a * - y"
    by (simp only: real_add_mult_distrib2)
  also have "... = a * x - a * y"
    by simp
  finally show ?thesis .
qed

lemma real_minus_le: "- (x::real) \\<le> y \\<Longrightarrow> - y \\<le> x"
  by simp

lemma real_diff_ineq_swap:
    "(d::real) - b \\<le> c + a \\<Longrightarrow> - a - b \\<le> c - d"
  by simp

end
