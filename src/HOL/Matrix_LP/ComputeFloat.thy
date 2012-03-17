(*  Title:      HOL/Matrix/ComputeFloat.thy
    Author:     Steven Obua
*)

header {* Floating Point Representation of the Reals *}

theory ComputeFloat
imports Complex_Main "~~/src/HOL/Library/Lattice_Algebras"
uses "~~/src/Tools/float.ML" ("~~/src/HOL/Tools/float_arith.ML")
begin

definition int_of_real :: "real \<Rightarrow> int"
  where "int_of_real x = (SOME y. real y = x)"

definition real_is_int :: "real \<Rightarrow> bool"
  where "real_is_int x = (EX (u::int). x = real u)"

lemma real_is_int_def2: "real_is_int x = (x = real (int_of_real x))"
  by (auto simp add: real_is_int_def int_of_real_def)

lemma real_is_int_real[simp]: "real_is_int (real (x::int))"
by (auto simp add: real_is_int_def int_of_real_def)

lemma int_of_real_real[simp]: "int_of_real (real x) = x"
by (simp add: int_of_real_def)

lemma real_int_of_real[simp]: "real_is_int x \<Longrightarrow> real (int_of_real x) = x"
by (auto simp add: int_of_real_def real_is_int_def)

lemma real_is_int_add_int_of_real: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> (int_of_real (a+b)) = (int_of_real a) + (int_of_real b)"
by (auto simp add: int_of_real_def real_is_int_def)

lemma real_is_int_add[simp]: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> real_is_int (a+b)"
apply (subst real_is_int_def2)
apply (simp add: real_is_int_add_int_of_real real_int_of_real)
done

lemma int_of_real_sub: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> (int_of_real (a-b)) = (int_of_real a) - (int_of_real b)"
by (auto simp add: int_of_real_def real_is_int_def)

lemma real_is_int_sub[simp]: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> real_is_int (a-b)"
apply (subst real_is_int_def2)
apply (simp add: int_of_real_sub real_int_of_real)
done

lemma real_is_int_rep: "real_is_int x \<Longrightarrow> ?! (a::int). real a = x"
by (auto simp add: real_is_int_def)

lemma int_of_real_mult:
  assumes "real_is_int a" "real_is_int b"
  shows "(int_of_real (a*b)) = (int_of_real a) * (int_of_real b)"
  using assms
  by (auto simp add: real_is_int_def real_of_int_mult[symmetric]
           simp del: real_of_int_mult)

lemma real_is_int_mult[simp]: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> real_is_int (a*b)"
apply (subst real_is_int_def2)
apply (simp add: int_of_real_mult)
done

lemma real_is_int_0[simp]: "real_is_int (0::real)"
by (simp add: real_is_int_def int_of_real_def)

lemma real_is_int_1[simp]: "real_is_int (1::real)"
proof -
  have "real_is_int (1::real) = real_is_int(real (1::int))" by auto
  also have "\<dots> = True" by (simp only: real_is_int_real)
  ultimately show ?thesis by auto
qed

lemma real_is_int_n1: "real_is_int (-1::real)"
proof -
  have "real_is_int (-1::real) = real_is_int(real (-1::int))" by auto
  also have "\<dots> = True" by (simp only: real_is_int_real)
  ultimately show ?thesis by auto
qed

lemma real_is_int_number_of[simp]: "real_is_int ((number_of \<Colon> int \<Rightarrow> real) x)"
  by (auto simp: real_is_int_def intro!: exI[of _ "number_of x"])

lemma int_of_real_0[simp]: "int_of_real (0::real) = (0::int)"
by (simp add: int_of_real_def)

lemma int_of_real_1[simp]: "int_of_real (1::real) = (1::int)"
proof -
  have 1: "(1::real) = real (1::int)" by auto
  show ?thesis by (simp only: 1 int_of_real_real)
qed

lemma int_of_real_number_of[simp]: "int_of_real (number_of b) = number_of b"
  unfolding int_of_real_def
  by (intro some_equality)
     (auto simp add: real_of_int_inject[symmetric] simp del: real_of_int_inject)

lemma int_div_zdiv: "int (a div b) = (int a) div (int b)"
by (rule zdiv_int)

lemma int_mod_zmod: "int (a mod b) = (int a) mod (int b)"
by (rule zmod_int)

lemma abs_div_2_less: "a \<noteq> 0 \<Longrightarrow> a \<noteq> -1 \<Longrightarrow> abs((a::int) div 2) < abs a"
by arith

lemma norm_0_1: "(0::_::number_ring) = Numeral0 & (1::_::number_ring) = Numeral1"
  by auto

lemma add_left_zero: "0 + a = (a::'a::comm_monoid_add)"
  by simp

lemma add_right_zero: "a + 0 = (a::'a::comm_monoid_add)"
  by simp

lemma mult_left_one: "1 * a = (a::'a::semiring_1)"
  by simp

lemma mult_right_one: "a * 1 = (a::'a::semiring_1)"
  by simp

lemma int_pow_0: "(a::int)^(Numeral0) = 1"
  by simp

lemma int_pow_1: "(a::int)^(Numeral1) = a"
  by simp

lemma zero_eq_Numeral0_nring: "(0::'a::number_ring) = Numeral0"
  by simp

lemma one_eq_Numeral1_nring: "(1::'a::number_ring) = Numeral1"
  by simp

lemma zero_eq_Numeral0_nat: "(0::nat) = Numeral0"
  by simp

lemma one_eq_Numeral1_nat: "(1::nat) = Numeral1"
  by simp

lemma zpower_Pls: "(z::int)^Numeral0 = Numeral1"
  by simp

lemma zpower_Min: "(z::int)^((-1)::nat) = Numeral1"
proof -
  have 1:"((-1)::nat) = 0"
    by simp
  show ?thesis by (simp add: 1)
qed

lemma fst_cong: "a=a' \<Longrightarrow> fst (a,b) = fst (a',b)"
  by simp

lemma snd_cong: "b=b' \<Longrightarrow> snd (a,b) = snd (a,b')"
  by simp

lemma lift_bool: "x \<Longrightarrow> x=True"
  by simp

lemma nlift_bool: "~x \<Longrightarrow> x=False"
  by simp

lemma not_false_eq_true: "(~ False) = True" by simp

lemma not_true_eq_false: "(~ True) = False" by simp

lemmas binarith =
  normalize_bin_simps
  pred_bin_simps succ_bin_simps
  add_bin_simps minus_bin_simps mult_bin_simps

lemma int_eq_number_of_eq:
  "(((number_of v)::int)=(number_of w)) = iszero ((number_of (v + uminus w))::int)"
  by (rule eq_number_of_eq)

lemma int_iszero_number_of_Pls: "iszero (Numeral0::int)"
  by (simp only: iszero_number_of_Pls)

lemma int_nonzero_number_of_Min: "~(iszero ((-1)::int))"
  by simp

lemma int_iszero_number_of_Bit0: "iszero ((number_of (Int.Bit0 w))::int) = iszero ((number_of w)::int)"
  by simp

lemma int_iszero_number_of_Bit1: "\<not> iszero ((number_of (Int.Bit1 w))::int)"
  by simp

lemma int_less_number_of_eq_neg: "(((number_of x)::int) < number_of y) = neg ((number_of (x + (uminus y)))::int)"
  unfolding neg_def number_of_is_id by simp

lemma int_not_neg_number_of_Pls: "\<not> (neg (Numeral0::int))"
  by simp

lemma int_neg_number_of_Min: "neg (-1::int)"
  by simp

lemma int_neg_number_of_Bit0: "neg ((number_of (Int.Bit0 w))::int) = neg ((number_of w)::int)"
  by simp

lemma int_neg_number_of_Bit1: "neg ((number_of (Int.Bit1 w))::int) = neg ((number_of w)::int)"
  by simp

lemma int_le_number_of_eq: "(((number_of x)::int) \<le> number_of y) = (\<not> neg ((number_of (y + (uminus x)))::int))"
  unfolding neg_def number_of_is_id by (simp add: not_less)

lemmas intarithrel =
  int_eq_number_of_eq
  lift_bool[OF int_iszero_number_of_Pls] nlift_bool[OF int_nonzero_number_of_Min] int_iszero_number_of_Bit0
  lift_bool[OF int_iszero_number_of_Bit1] int_less_number_of_eq_neg nlift_bool[OF int_not_neg_number_of_Pls] lift_bool[OF int_neg_number_of_Min]
  int_neg_number_of_Bit0 int_neg_number_of_Bit1 int_le_number_of_eq

lemma int_number_of_add_sym: "((number_of v)::int) + number_of w = number_of (v + w)"
  by simp

lemma int_number_of_diff_sym: "((number_of v)::int) - number_of w = number_of (v + (uminus w))"
  by simp

lemma int_number_of_mult_sym: "((number_of v)::int) * number_of w = number_of (v * w)"
  by simp

lemma int_number_of_minus_sym: "- ((number_of v)::int) = number_of (uminus v)"
  by simp

lemmas intarith = int_number_of_add_sym int_number_of_minus_sym int_number_of_diff_sym int_number_of_mult_sym

lemmas natarith = add_nat_number_of diff_nat_number_of mult_nat_number_of eq_nat_number_of less_nat_number_of

lemmas powerarith = nat_number_of zpower_number_of_even
  zpower_number_of_odd[simplified zero_eq_Numeral0_nring one_eq_Numeral1_nring]
  zpower_Pls zpower_Min

definition float :: "(int \<times> int) \<Rightarrow> real" where
  "float = (\<lambda>(a, b). real a * 2 powr real b)"

lemma float_add_l0: "float (0, e) + x = x"
  by (simp add: float_def)

lemma float_add_r0: "x + float (0, e) = x"
  by (simp add: float_def)

lemma float_add:
  "float (a1, e1) + float (a2, e2) =
  (if e1<=e2 then float (a1+a2*2^(nat(e2-e1)), e1) else float (a1*2^(nat (e1-e2))+a2, e2))"
  by (simp add: float_def algebra_simps powr_realpow[symmetric] powr_divide2[symmetric])

lemma float_mult_l0: "float (0, e) * x = float (0, 0)"
  by (simp add: float_def)

lemma float_mult_r0: "x * float (0, e) = float (0, 0)"
  by (simp add: float_def)

lemma float_mult:
  "float (a1, e1) * float (a2, e2) = (float (a1 * a2, e1 + e2))"
  by (simp add: float_def powr_add)

lemma float_minus:
  "- (float (a,b)) = float (-a, b)"
  by (simp add: float_def)

lemma zero_le_float:
  "(0 <= float (a,b)) = (0 <= a)"
  using powr_gt_zero[of 2 "real b", arith]
  by (simp add: float_def zero_le_mult_iff)

lemma float_le_zero:
  "(float (a,b) <= 0) = (a <= 0)"
  using powr_gt_zero[of 2 "real b", arith]
  by (simp add: float_def mult_le_0_iff)

lemma float_abs:
  "abs (float (a,b)) = (if 0 <= a then (float (a,b)) else (float (-a,b)))"
  using powr_gt_zero[of 2 "real b", arith]
  by (simp add: float_def abs_if mult_less_0_iff)

lemma float_zero:
  "float (0, b) = 0"
  by (simp add: float_def)

lemma float_pprt:
  "pprt (float (a, b)) = (if 0 <= a then (float (a,b)) else (float (0, b)))"
  by (auto simp add: zero_le_float float_le_zero float_zero)

lemma float_nprt:
  "nprt (float (a, b)) = (if 0 <= a then (float (0,b)) else (float (a, b)))"
  by (auto simp add: zero_le_float float_le_zero float_zero)

definition lbound :: "real \<Rightarrow> real"
  where "lbound x = min 0 x"

definition ubound :: "real \<Rightarrow> real"
  where "ubound x = max 0 x"

lemma lbound: "lbound x \<le> x"   
  by (simp add: lbound_def)

lemma ubound: "x \<le> ubound x"
  by (simp add: ubound_def)

lemma pprt_lbound: "pprt (lbound x) = float (0, 0)"
  by (auto simp: float_def lbound_def)

lemma nprt_ubound: "nprt (ubound x) = float (0, 0)"
  by (auto simp: float_def ubound_def)

lemmas floatarith[simplified norm_0_1] = float_add float_add_l0 float_add_r0 float_mult float_mult_l0 float_mult_r0 
          float_minus float_abs zero_le_float float_pprt float_nprt pprt_lbound nprt_ubound

(* for use with the compute oracle *)
lemmas arith = binarith intarith intarithrel natarith powerarith floatarith not_false_eq_true not_true_eq_false

use "~~/src/HOL/Tools/float_arith.ML"

end
