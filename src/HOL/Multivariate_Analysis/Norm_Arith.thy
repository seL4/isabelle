(*  Title:      HOL/Multivariate_Analysis/Norm_Arith.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* General linear decision procedure for normed spaces *}

theory Norm_Arith
imports "~~/src/HOL/Library/Sum_of_Squares"
uses ("normarith.ML")
begin

lemma norm_cmul_rule_thm:
  fixes x :: "'a::real_normed_vector"
  shows "b >= norm(x) ==> \<bar>c\<bar> * b >= norm(scaleR c x)"
  unfolding norm_scaleR
  apply (erule mult_left_mono)
  apply simp
  done

  (* FIXME: Move all these theorems into the ML code using lemma antiquotation *)
lemma norm_add_rule_thm:
  fixes x1 x2 :: "'a::real_normed_vector"
  shows "norm x1 \<le> b1 \<Longrightarrow> norm x2 \<le> b2 \<Longrightarrow> norm (x1 + x2) \<le> b1 + b2"
  by (rule order_trans [OF norm_triangle_ineq add_mono])

lemma ge_iff_diff_ge_0: "(a::'a::linordered_ring) \<ge> b == a - b \<ge> 0"
  by (simp add: field_simps)

lemma pth_1:
  fixes x :: "'a::real_normed_vector"
  shows "x == scaleR 1 x" by simp

lemma pth_2:
  fixes x :: "'a::real_normed_vector"
  shows "x - y == x + -y" by (atomize (full)) simp

lemma pth_3:
  fixes x :: "'a::real_normed_vector"
  shows "- x == scaleR (-1) x" by simp

lemma pth_4:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR 0 x == 0" and "scaleR c 0 = (0::'a)" by simp_all

lemma pth_5:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR c (scaleR d x) == scaleR (c * d) x" by simp

lemma pth_6:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR c (x + y) == scaleR c x + scaleR c y"
  by (simp add: scaleR_right_distrib)

lemma pth_7:
  fixes x :: "'a::real_normed_vector"
  shows "0 + x == x" and "x + 0 == x" by simp_all

lemma pth_8:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR c x + scaleR d x == scaleR (c + d) x"
  by (simp add: scaleR_left_distrib)

lemma pth_9:
  fixes x :: "'a::real_normed_vector" shows
  "(scaleR c x + z) + scaleR d x == scaleR (c + d) x + z"
  "scaleR c x + (scaleR d x + z) == scaleR (c + d) x + z"
  "(scaleR c x + w) + (scaleR d x + z) == scaleR (c + d) x + (w + z)"
  by (simp_all add: algebra_simps)

lemma pth_a:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR 0 x + y == y" by simp

lemma pth_b:
  fixes x :: "'a::real_normed_vector" shows
  "scaleR c x + scaleR d y == scaleR c x + scaleR d y"
  "(scaleR c x + z) + scaleR d y == scaleR c x + (z + scaleR d y)"
  "scaleR c x + (scaleR d y + z) == scaleR c x + (scaleR d y + z)"
  "(scaleR c x + w) + (scaleR d y + z) == scaleR c x + (w + (scaleR d y + z))"
  by (simp_all add: algebra_simps)

lemma pth_c:
  fixes x :: "'a::real_normed_vector" shows
  "scaleR c x + scaleR d y == scaleR d y + scaleR c x"
  "(scaleR c x + z) + scaleR d y == scaleR d y + (scaleR c x + z)"
  "scaleR c x + (scaleR d y + z) == scaleR d y + (scaleR c x + z)"
  "(scaleR c x + w) + (scaleR d y + z) == scaleR d y + ((scaleR c x + w) + z)"
  by (simp_all add: algebra_simps)

lemma pth_d:
  fixes x :: "'a::real_normed_vector"
  shows "x + 0 == x" by simp

lemma norm_imp_pos_and_ge:
  fixes x :: "'a::real_normed_vector"
  shows "norm x == n \<Longrightarrow> norm x \<ge> 0 \<and> n \<ge> norm x"
  by atomize auto

lemma real_eq_0_iff_le_ge_0: "(x::real) = 0 == x \<ge> 0 \<and> -x \<ge> 0" by arith

lemma norm_pths:
  fixes x :: "'a::real_normed_vector" shows
  "x = y \<longleftrightarrow> norm (x - y) \<le> 0"
  "x \<noteq> y \<longleftrightarrow> \<not> (norm (x - y) \<le> 0)"
  using norm_ge_zero[of "x - y"] by auto

lemmas arithmetic_simps =
  arith_simps
  add_numeral_special
  add_neg_numeral_special
  add_0_left
  add_0_right
  mult_zero_left
  mult_zero_right
  mult_1_left
  mult_1_right

use "normarith.ML"

method_setup norm = {* Scan.succeed (SIMPLE_METHOD' o NormArith.norm_arith_tac)
*} "prove simple linear statements about vector norms"

text{* Hence more metric properties. *}

lemma dist_triangle_add:
  fixes x y x' y' :: "'a::real_normed_vector"
  shows "dist (x + y) (x' + y') <= dist x x' + dist y y'"
  by norm

lemma dist_triangle_add_half:
  fixes x x' y y' :: "'a::real_normed_vector"
  shows "dist x x' < e / 2 \<Longrightarrow> dist y y' < e / 2 \<Longrightarrow> dist(x + y) (x' + y') < e"
  by norm

end
