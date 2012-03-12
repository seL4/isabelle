(*  Title:      HOL/Import/HOL_Light/HOLLightReal.thy
    Author:     Cezary Kaliszyk
*)

header {* Compatibility theorems for HOL Light reals *}

theory HOLLightReal imports Real begin

lemma REAL_OF_NUM_MAX:
  "max (real (m :: nat)) (real n) = real (max m n)"
  by simp

lemma REAL_OF_NUM_MIN:
  "min (real (m :: nat)) (real n) = real (min m n)"
  by simp

lemma REAL_POLY_NEG_CLAUSES:
  "(\<forall>(x :: real). - x = - 1 * x) \<and> (\<forall>(x :: real) y. x - y = x + - 1 * y)"
  by simp

lemma REAL_MUL_AC:
  "(m :: real) * n = n * m \<and> m * n * p = m * (n * p) \<and> m * (n * p) = n * (m * p)"
  by simp

lemma REAL_EQ_ADD_LCANCEL_0:
  "((x :: real) + y = x) = (y = 0)"
  by simp

lemma REAL_EQ_ADD_RCANCEL_0:
  "((x :: real) + y = y) = (x = 0)"
  by simp

lemma REAL_LT_ANTISYM:
  "\<not> ((x :: real) < y \<and> y < x)"
  by simp

lemma REAL_LET_ANTISYM:
  "\<not> ((x :: real) \<le> y \<and> y < x)"
  by simp

lemma REAL_LT_NEGTOTAL:
  "(x :: real) = 0 \<or> 0 < x \<or> 0 < - x"
  by auto

lemma REAL_LT_ADDNEG:
  "((y :: real) < x + - z) = (y + z < x)"
  by auto

lemma REAL_LT_ADDNEG2:
  "((x :: real) + - y < z) = (x < z + y)"
  by auto

lemma REAL_LT_ADD1:
  "(x :: real) \<le> y \<longrightarrow> x < y + 1"
  by simp

lemma REAL_SUB_ADD2:
  "(y :: real) + (x - y) = x"
  by simp

lemma REAL_ADD_SUB:
  "(x :: real) + y - x = y"
  by simp

lemma REAL_NEG_EQ:
  "(- (x :: real) = y) = (x = - y)"
  by auto

lemma REAL_LE_ADDR:
  "((x :: real) \<le> x + y) = (0 \<le> y)"
  by simp

lemma REAL_LE_ADDL:
  "((y :: real) \<le> x + y) = (0 \<le> x)"
  by simp

lemma REAL_LT_ADDR:
  "((x :: real) < x + y) = (0 < y)"
  by simp

lemma REAL_LT_ADDL:
  "((y :: real) < x + y) = (0 < x)"
  by simp

lemma REAL_SUB_SUB:
  "(x :: real) - y - x = - y"
  by simp

lemma REAL_SUB_LNEG:
  "- (x :: real) - y = - (x + y)"
  by simp

lemma REAL_SUB_NEG2:
  "- (x :: real) - - y = y - x"
  by simp

lemma REAL_SUB_TRIANGLE:
  "(a :: real) - b + (b - c) = a - c"
  by simp

lemma REAL_SUB_SUB2:
  "(x :: real) - (x - y) = y"
  by simp

lemma REAL_ADD_SUB2:
  "(x :: real) - (x + y) = - y"
  by simp

lemma REAL_POS_NZ:
  "0 < (x :: real) \<longrightarrow> x \<noteq> 0"
  by simp

lemma REAL_DIFFSQ:
  "((x :: real) + y) * (x - y) = x * x - y * y"
  by (simp add: comm_semiring_1_class.normalizing_semiring_rules(7) right_distrib mult_diff_mult)

lemma REAL_ABS_TRIANGLE_LE:
  "abs (x :: real) + abs (y - x) \<le> z \<longrightarrow> abs y \<le> z"
  by auto

lemma REAL_ABS_TRIANGLE_LT:
  "abs (x :: real) + abs (y - x) < z \<longrightarrow> abs y < z"
  by auto

lemma REAL_ABS_REFL:
  "(abs (x :: real) = x) = (0 \<le> x)"
  by auto

lemma REAL_ABS_BETWEEN:
  "(0 < (d :: real) \<and> x - d < y \<and> y < x + d) = (abs (y - x) < d)"
  by auto

lemma REAL_ABS_BOUND:
  "abs ((x :: real) - y) < d \<longrightarrow> y < x + d"
  by auto

lemma REAL_ABS_STILLNZ:
  "abs ((x :: real) - y) < abs y \<longrightarrow> x \<noteq> 0"
  by auto

lemma REAL_ABS_CASES:
  "(x :: real) = 0 \<or> 0 < abs x"
  by simp

lemma REAL_ABS_BETWEEN1:
  "(x :: real) < z \<and> abs (y - x) < z - x \<longrightarrow> y < z"
  by auto

lemma REAL_ABS_SIGN:
  "abs ((x :: real) - y) < y \<longrightarrow> 0 < x"
  by auto

lemma REAL_ABS_SIGN2:
  "abs ((x :: real) - y) < - y \<longrightarrow> x < 0"
  by auto

lemma REAL_ABS_CIRCLE:
  "abs (h :: real) < abs y - abs x \<longrightarrow> abs (x + h) < abs y"
  by auto

lemma REAL_BOUNDS_LT:
  "(- (k :: real) < x \<and> x < k) = (abs x < k)"
  by auto

lemma REAL_MIN_MAX:
  "min (x :: real) y = - max (- x) (- y)"
  by auto

lemma REAL_MAX_MIN:
  "max (x :: real) y = - min (- x) (- y)"
  by auto

lemma REAL_MAX_MAX:
  "(x :: real) \<le> max x y \<and> y \<le> max x y"
  by simp

lemma REAL_MIN_MIN:
  "min (x :: real) y \<le> x \<and> min x y \<le> y"
  by simp

lemma REAL_MAX_ACI:
  "max (x :: real) y = max y x \<and>
   max (max x y) z = max x (max y z) \<and>
   max x (max y z) = max y (max x z) \<and> max x x = x \<and> max x (max x y) = max x y"
  by auto


lemma REAL_MIN_ACI:
  "min (x :: real) y = min y x \<and>
   min (min x y) z = min x (min y z) \<and>
   min x (min y z) = min y (min x z) \<and> min x x = x \<and> min x (min x y) = min x y"
  by auto

lemma REAL_EQ_MUL_RCANCEL:
  "((x :: real) * z = y * z) = (x = y \<or> z = 0)"
  by auto

lemma REAL_MUL_LINV_UNIQ:
  "(x :: real) * y = 1 \<longrightarrow> inverse y = x"
  by (metis inverse_inverse_eq inverse_unique)

lemma REAL_DIV_RMUL:
  "(y :: real) \<noteq> 0 \<longrightarrow> x / y * y = x"
  by simp

lemma REAL_DIV_LMUL:
  "(y :: real) \<noteq> 0 \<longrightarrow> y * (x / y) = x"
  by simp

lemma REAL_LT_IMP_NZ:
  "0 < (x :: real) \<longrightarrow> x \<noteq> 0"
  by simp

lemma REAL_LT_LCANCEL_IMP:
  "0 < (x :: real) \<and> x * y < x * z \<longrightarrow> y < z"
  by (auto simp add: mult_less_cancel_left_disj not_less_iff_gr_or_eq)

lemma REAL_LT_RCANCEL_IMP:
  "0 < (z :: real) \<and> x * z < y * z \<longrightarrow> x < y"
  by (auto simp add: mult_less_cancel_left_disj not_less_iff_gr_or_eq)

lemma REAL_MUL_POS_LE:
  "(0 \<le> (x :: real) * y) = (x = 0 \<or> y = 0 \<or> 0 < x \<and> 0 < y \<or> x < 0 \<and> y < 0)"
  by (metis less_eq_real_def mult_eq_0_iff zero_le_mult_iff)

lemma REAL_EQ_RDIV_EQ:
  "0 < (z :: real) \<longrightarrow> (x = y / z) = (x * z = y)"
  by auto

lemma REAL_EQ_LDIV_EQ:
  "0 < (z :: real) \<longrightarrow> (x / z = y) = (x = y * z)"
  by auto

lemma REAL_SUB_INV:
  "(x :: real) \<noteq> 0 \<and> y \<noteq> 0 \<longrightarrow> inverse x - inverse y = (y - x) / (x * y)"
  by (simp add: division_ring_inverse_diff divide_real_def)

lemma REAL_DOWN:
  "0 < (d :: real) \<longrightarrow> (\<exists>e>0. e < d)"
  by (intro impI exI[of _ "d / 2"]) simp

lemma REAL_POW_MONO_LT:
  "1 < (x :: real) \<and> m < n \<longrightarrow> x ^ m < x ^ n"
  by simp

lemma REAL_POW_MONO:
  "1 \<le> (x :: real) \<and> m \<le> n \<longrightarrow> x ^ m \<le> x ^ n"
  by (cases "m < n", cases "x = 1") auto

lemma REAL_EQ_LCANCEL_IMP:
  "(z :: real) \<noteq> 0 \<and> z * x = z * y \<longrightarrow> x = y"
  by auto

lemma REAL_LE_DIV:
  "0 \<le> (x :: real) \<and> 0 \<le> y \<longrightarrow> 0 \<le> x / y"
  by (simp add: zero_le_divide_iff)

lemma REAL_10: "(1::real) \<noteq> 0"
  by simp

lemma REAL_ADD_ASSOC: "(x::real) + (y + z) = x + y + z"
  by simp

lemma REAL_MUL_ASSOC: "(x::real) * (y * z) = x * y * z"
  by simp

lemma REAL_ADD_LINV:  "-x + x = (0::real)"
  by simp

lemma REAL_MUL_LINV: "x \<noteq> (0::real) \<Longrightarrow> inverse x * x = 1"
  by simp

lemma REAL_LT_TOTAL: "((x::real) = y) \<or> x < y \<or> y < x"
  by auto

lemma real_lte: "((x::real) \<le> y) = (\<not>(y < x))"
  by auto

lemma real_of_num: "((0::real) = 0) \<and> (!n. real (Suc n) = real n + 1)"
  by (simp add: real_of_nat_Suc)

lemma abs: "abs (x::real) = (if 0 \<le> x then x else -x)"
  by (simp add: abs_if)

lemma pow: "(!x::real. x ^ 0 = 1) \<and> (!x::real. \<forall>n. x ^ (Suc n) = x * x ^ n)"
  by simp

lemma REAL_POLY_CLAUSES:
  "(\<forall>(x :: real) y z. x + (y + z) = x + y + z) \<and>
   (\<forall>(x :: real) y. x + y = y + x) \<and>
   (\<forall>(x :: real). 0 + x = x) \<and>
   (\<forall>(x :: real) y z. x * (y * z) = x * y * z) \<and>
   (\<forall>(x :: real) y. x * y = y * x) \<and>
   (\<forall>(x :: real). 1 * x = x) \<and>
   (\<forall>(x :: real). 0 * x = 0) \<and>
   (\<forall>(x :: real) y z. x * (y + z) = x * y + x * z) \<and>
   (\<forall>(x :: real). x ^ 0 = 1) \<and> (\<forall>(x :: real) n. x ^ Suc n = x * x ^ n)"
  by (auto simp add: right_distrib)

lemma REAL_COMPLETE:
  "(\<exists>(x :: real). P x) \<and> (\<exists>(M :: real). \<forall>x. P x \<longrightarrow> x \<le> M) \<longrightarrow>
   (\<exists>M. (\<forall>x. P x \<longrightarrow> x \<le> M) \<and>
          (\<forall>M'. (\<forall>x. P x \<longrightarrow> x \<le> M') \<longrightarrow> M \<le> M'))"
  using complete_real[unfolded Ball_def, of "Collect P"] by auto

lemma REAL_COMPLETE_SOMEPOS:
  "(\<exists>(x :: real). P x \<and> 0 \<le> x) \<and> (\<exists>M. \<forall>x. P x \<longrightarrow> x \<le> M) \<longrightarrow>
   (\<exists>M. (\<forall>x. P x \<longrightarrow> x \<le> M) \<and>
          (\<forall>M'. (\<forall>x. P x \<longrightarrow> x \<le> M') \<longrightarrow> M \<le> M'))"
  using REAL_COMPLETE by auto

lemma REAL_ADD_AC:
  "(m :: real) + n = n + m \<and> m + n + p = m + (n + p) \<and> m + (n + p) = n + (m + p)"
  by simp

lemma REAL_LE_RNEG:
  "((x :: real) \<le> - y) = (x + y \<le> 0)"
  by auto

lemma REAL_LE_NEGTOTAL:
  "0 \<le> (x :: real) \<or> 0 \<le> - x"
  by auto

lemma DEF_real_sgn:
  "sgn = (\<lambda>u. if (0 :: real) < u then 1 else if u < 0 then - 1 else 0)"
  by (simp add: ext)

end

