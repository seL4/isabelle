(*  Title       : HOL/Real/RealPow.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural powers theory

*)

theory RealPow = RealArith:

instance real :: power ..

primrec (realpow)
     realpow_0:   "r ^ 0       = 1"
     realpow_Suc: "r ^ (Suc n) = (r::real) * (r ^ n)"


lemma realpow_zero [simp]: "(0::real) ^ (Suc n) = 0"
by auto

lemma realpow_not_zero [rule_format]: "r \<noteq> (0::real) --> r ^ n \<noteq> 0"
by (induct_tac "n", auto)

lemma realpow_zero_zero: "r ^ n = (0::real) ==> r = 0"
apply (rule ccontr)
apply (auto dest: realpow_not_zero)
done

lemma realpow_inverse: "inverse ((r::real) ^ n) = (inverse r) ^ n"
apply (induct_tac "n")
apply (auto simp add: real_inverse_distrib)
done

lemma realpow_abs: "abs(r ^ n) = abs(r::real) ^ n"
apply (induct_tac "n")
apply (auto simp add: abs_mult)
done

lemma realpow_add: "(r::real) ^ (n + m) = (r ^ n) * (r ^ m)"
apply (induct_tac "n")
apply (auto simp add: real_mult_ac)
done

lemma realpow_one [simp]: "(r::real) ^ 1 = r"
by simp

lemma realpow_two: "(r::real)^ (Suc (Suc 0)) = r * r"
by simp

lemma realpow_gt_zero [rule_format]: "(0::real) < r --> 0 < r ^ n"
apply (induct_tac "n")
apply (auto intro: real_mult_order simp add: real_zero_less_one)
done

lemma realpow_ge_zero [rule_format]: "(0::real) \<le> r --> 0 \<le> r ^ n"
apply (induct_tac "n")
apply (auto simp add: real_0_le_mult_iff)
done

lemma realpow_le [rule_format]: "(0::real) \<le> x & x \<le> y --> x ^ n \<le> y ^ n"
apply (induct_tac "n")
apply (auto intro!: real_mult_le_mono)
apply (simp (no_asm_simp) add: realpow_ge_zero)
done

lemma realpow_0_left [rule_format, simp]:
     "0 < n --> 0 ^ n = (0::real)"
apply (induct_tac "n", auto) 
done

lemma realpow_less' [rule_format]:
     "[|(0::real) \<le> x; x < y |] ==> 0 < n --> x ^ n < y ^ n"
apply (induct n) 
apply (auto simp add: real_mult_less_mono' realpow_ge_zero) 
done

text{*Legacy: weaker version of the theorem above*}
lemma realpow_less:
     "[|(0::real) < x; x < y; 0 < n|] ==> x ^ n < y ^ n"
apply (rule realpow_less', auto) 
done

lemma realpow_eq_one [simp]: "1 ^ n = (1::real)"
by (induct_tac "n", auto)

lemma abs_realpow_minus_one [simp]: "abs((-1) ^ n) = (1::real)"
apply (induct_tac "n")
apply (auto simp add: abs_mult)
done

lemma realpow_mult: "((r::real) * s) ^ n = (r ^ n) * (s ^ n)"
apply (induct_tac "n")
apply (auto simp add: real_mult_ac)
done

lemma realpow_two_le [simp]: "(0::real) \<le> r^ Suc (Suc 0)"
by (simp add: real_le_square)

lemma abs_realpow_two [simp]: "abs((x::real)^Suc (Suc 0)) = x^Suc (Suc 0)"
by (simp add: abs_eqI1 real_le_square)

lemma realpow_two_abs [simp]: "abs(x::real)^Suc (Suc 0) = x^Suc (Suc 0)"
by (simp add: realpow_abs [symmetric] abs_eqI1 del: realpow_Suc)

lemma realpow_two_gt_one: "(1::real) < r ==> 1 < r^ (Suc (Suc 0))"
apply auto
apply (cut_tac real_zero_less_one)
apply (frule_tac x = 0 in order_less_trans, assumption)
apply (drule_tac  z = r and x = 1 in real_mult_less_mono1)
apply (auto intro: order_less_trans)
done

lemma realpow_ge_one [rule_format]: "(1::real) < r --> 1 \<le> r ^ n"
apply (induct_tac "n", auto)
apply (subgoal_tac "1*1 \<le> r * r^n")
apply (rule_tac [2] real_mult_le_mono, auto)
done

lemma realpow_ge_one2: "(1::real) \<le> r ==> 1 \<le> r ^ n"
apply (drule order_le_imp_less_or_eq)
apply (auto dest: realpow_ge_one)
done

lemma two_realpow_ge_one [simp]: "(1::real) \<le> 2 ^ n"
apply (rule_tac y = "1 ^ n" in order_trans)
apply (rule_tac [2] realpow_le)
apply (auto intro: order_less_imp_le)
done

lemma two_realpow_gt [simp]: "real (n::nat) < 2 ^ n"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_Suc)
apply (subst real_mult_2)
apply (rule real_add_less_le_mono)
apply (auto simp add: two_realpow_ge_one)
done

lemma realpow_minus_one [simp]: "(-1) ^ (2*n) = (1::real)"
by (induct_tac "n", auto)

lemma realpow_minus_one_odd [simp]: "(-1) ^ Suc (2*n) = -(1::real)"
by auto

lemma realpow_minus_one_even [simp]: "(-1) ^ Suc (Suc (2*n)) = (1::real)"
by auto

lemma realpow_Suc_less [rule_format]:
     "(0::real) < r & r < (1::real) --> r ^ Suc n < r ^ n"
  by (induct_tac "n", auto simp add: mult_less_cancel_left)

lemma realpow_Suc_le [rule_format]:
     "0 \<le> r & r < (1::real) --> r ^ Suc n \<le> r ^ n"
apply (induct_tac "n")
apply (auto intro: order_less_imp_le dest!: order_le_imp_less_or_eq)
done

lemma realpow_zero_le [simp]: "(0::real) \<le> 0 ^ n"
by (case_tac "n", auto)

lemma realpow_Suc_le2 [rule_format]: "0 < r & r < (1::real) --> r ^ Suc n \<le> r ^ n"
by (blast intro!: order_less_imp_le realpow_Suc_less)

lemma realpow_Suc_le3: "[| 0 \<le> r; r < (1::real) |] ==> r ^ Suc n \<le> r ^ n"
apply (erule order_le_imp_less_or_eq [THEN disjE])
apply (rule realpow_Suc_le2, auto)
done

lemma realpow_less_le [rule_format]: "0 \<le> r & r < (1::real) & n < N --> r ^ N \<le> r ^ n"
apply (induct_tac "N")
apply (simp_all (no_asm_simp))
apply clarify
apply (subgoal_tac "r * r ^ na \<le> 1 * r ^ n", simp)
apply (rule real_mult_le_mono)
apply (auto simp add: realpow_ge_zero less_Suc_eq)
done

lemma realpow_le_le: "[| 0 \<le> r; r < (1::real); n \<le> N |] ==> r ^ N \<le> r ^ n"
apply (drule_tac n = N in le_imp_less_or_eq)
apply (auto intro: realpow_less_le)
done

lemma realpow_Suc_le_self: "[| 0 < r; r < (1::real) |] ==> r ^ Suc n \<le> r"
by (drule_tac n = 1 and N = "Suc n" in order_less_imp_le [THEN realpow_le_le], auto)

lemma realpow_Suc_less_one: "[| 0 < r; r < (1::real) |] ==> r ^ Suc n < 1"
by (blast intro: realpow_Suc_le_self order_le_less_trans)

lemma realpow_le_Suc [rule_format]: "(1::real) \<le> r --> r ^ n \<le> r ^ Suc n"
by (induct_tac "n", auto)

lemma realpow_less_Suc [rule_format]: "(1::real) < r --> r ^ n < r ^ Suc n"
by (induct_tac "n", auto simp add: mult_less_cancel_left)

lemma realpow_le_Suc2 [rule_format]: "(1::real) < r --> r ^ n \<le> r ^ Suc n"
by (blast intro!: order_less_imp_le realpow_less_Suc)

(*One use in RealPow.thy*)
lemma real_mult_self_le2: "[| (1::real) \<le> r; (1::real) \<le> x |]  ==> x \<le> r * x"
apply (subgoal_tac "1 * x \<le> r * x", simp) 
apply (rule mult_right_mono, auto) 
done

lemma realpow_gt_ge2 [rule_format]: "(1::real) \<le> r & n < N --> r ^ n \<le> r ^ N"
apply (induct_tac "N", auto)
apply (frule_tac [!] n = na in realpow_ge_one2)
apply (drule_tac [!] real_mult_self_le2, assumption)
prefer 2 apply assumption
apply (auto intro: order_trans simp add: less_Suc_eq)
done

lemma realpow_ge_ge2: "[| (1::real) \<le> r; n \<le> N |] ==> r ^ n \<le> r ^ N"
apply (drule_tac n = N in le_imp_less_or_eq)
apply (auto intro: realpow_gt_ge2)
done

lemma realpow_Suc_ge_self2: "(1::real) \<le> r ==> r \<le> r ^ Suc n"
by (drule_tac n = 1 and N = "Suc n" in realpow_ge_ge2, auto)

(*Used ONCE in Hyperreal/NthRoot.ML*)
lemma realpow_ge_self2: "[| (1::real) \<le> r; 0 < n |] ==> r \<le> r ^ n"
apply (drule less_not_refl2 [THEN not0_implies_Suc])
apply (auto intro!: realpow_Suc_ge_self2)
done

lemma realpow_minus_mult [rule_format, simp]:
     "0 < n --> (x::real) ^ (n - 1) * x = x ^ n"
apply (induct_tac "n")
apply (auto simp add: real_mult_commute)
done

lemma realpow_two_mult_inverse [simp]: "r \<noteq> 0 ==> r * inverse r ^Suc (Suc 0) = inverse (r::real)"
by (simp add: realpow_two real_mult_assoc [symmetric])

(* 05/00 *)
lemma realpow_two_minus [simp]: "(-x)^Suc (Suc 0) = (x::real)^Suc (Suc 0)"
by simp

lemma realpow_two_diff: "(x::real)^Suc (Suc 0) - y^Suc (Suc 0) = (x - y) * (x + y)"
apply (unfold real_diff_def)
apply (simp add: real_add_mult_distrib2 real_add_mult_distrib real_mult_ac)
done

lemma realpow_two_disj: "((x::real)^Suc (Suc 0) = y^Suc (Suc 0)) = (x = y | x = -y)"
apply (cut_tac x = x and y = y in realpow_two_diff)
apply (auto simp del: realpow_Suc)
done

(* used in Transc *)
lemma realpow_diff: "[|(x::real) \<noteq> 0; m \<le> n |] ==> x ^ (n - m) = x ^ n * inverse (x ^ m)"
by (auto simp add: le_eq_less_or_eq less_iff_Suc_add realpow_add realpow_not_zero real_mult_ac)

lemma realpow_real_of_nat: "real (m::nat) ^ n = real (m ^ n)"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_one real_of_nat_mult)
done

lemma realpow_real_of_nat_two_pos [simp] : "0 < real (Suc (Suc 0) ^ n)"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_mult real_0_less_mult_iff)
done

lemma realpow_increasing:
  assumes xnonneg: "(0::real) \<le> x"
      and ynonneg: "0 \<le> y"
      and le: "x ^ Suc n \<le> y ^ Suc n"
  shows "x \<le> y"
 proof (rule ccontr)
   assume "~ x \<le> y"
   then have "y<x" by simp
   then have "y ^ Suc n < x ^ Suc n"
     by (simp only: prems realpow_less') 
   from le and this show "False"
     by simp
 qed
  
lemma realpow_Suc_cancel_eq: "[| (0::real) \<le> x; 0 \<le> y; x ^ Suc n = y ^ Suc n |] ==> x = y"
by (blast intro: realpow_increasing order_antisym order_eq_refl sym)


(*** Logical equivalences for inequalities ***)

lemma realpow_eq_0_iff [simp]: "(x^n = 0) = (x = (0::real) & 0<n)"
by (induct_tac "n", auto)

lemma zero_less_realpow_abs_iff [simp]: "(0 < (abs x)^n) = (x \<noteq> (0::real) | n=0)"
apply (induct_tac "n")
apply (auto simp add: real_0_less_mult_iff)
done

lemma zero_le_realpow_abs [simp]: "(0::real) \<le> (abs x)^n"
apply (induct_tac "n")
apply (auto simp add: real_0_le_mult_iff)
done


(*** Literal arithmetic involving powers, type real ***)

lemma real_of_int_power: "real (x::int) ^ n = real (x ^ n)"
apply (induct_tac "n")
apply (simp_all (no_asm_simp) add: nat_mult_distrib)
done
declare real_of_int_power [symmetric, simp]

lemma power_real_number_of: "(number_of v :: real) ^ n = real ((number_of v :: int) ^ n)"
by (simp only: real_number_of_def real_of_int_power)

declare power_real_number_of [of _ "number_of w", standard, simp]


lemma real_power_two: "(r::real)\<twosuperior> = r * r"
  by (simp add: numeral_2_eq_2)

lemma real_sqr_ge_zero [iff]: "0 \<le> (r::real)\<twosuperior>"
  by (simp add: real_power_two)

lemma real_sqr_gt_zero: "(r::real) \<noteq> 0 ==> 0 < r\<twosuperior>"
proof -
  assume "r \<noteq> 0"
  hence "0 \<noteq> r\<twosuperior>" by simp
  also have "0 \<le> r\<twosuperior>" by (simp add: real_sqr_ge_zero)
  finally show ?thesis .
qed

lemma real_sqr_not_zero: "r \<noteq> 0 ==> (r::real)\<twosuperior> \<noteq> 0"
  by simp


subsection{*Various Other Theorems*}

text{*Used several times in Hyperreal/Transcendental.ML*}
lemma real_sum_squares_cancel_a: "x * x = -(y * y) ==> x = (0::real) & y=0"
  by (auto intro: real_sum_squares_cancel)

lemma real_squared_diff_one_factored: "x*x - (1::real) = (x + 1)*(x - 1)"
apply (auto simp add: real_add_mult_distrib real_add_mult_distrib2 real_diff_def)
done

lemma real_mult_is_one: "(x*x = (1::real)) = (x = 1 | x = - 1)"
apply auto
apply (drule right_minus_eq [THEN iffD2]) 
apply (auto simp add: real_squared_diff_one_factored)
done
declare real_mult_is_one [iff]

lemma real_le_add_half_cancel: "(x + y/2 <= (y::real)) = (x <= y /2)"
apply auto
done
declare real_le_add_half_cancel [simp]

lemma real_minus_half_eq: "(x::real) - x/2 = x/2"
apply auto
done
declare real_minus_half_eq [simp]

lemma real_mult_inverse_cancel:
     "[|(0::real) < x; 0 < x1; x1 * y < x * u |] 
      ==> inverse x * y < inverse x1 * u"
apply (rule_tac c=x in mult_less_imp_less_left) 
apply (auto simp add: real_mult_assoc [symmetric])
apply (simp (no_asm) add: real_mult_ac)
apply (rule_tac c=x1 in mult_less_imp_less_right) 
apply (auto simp add: real_mult_ac)
done

text{*Used once: in Hyperreal/Transcendental.ML*}
lemma real_mult_inverse_cancel2: "[|(0::real) < x;0 < x1; x1 * y < x * u |] ==> y * inverse x < u * inverse x1"
apply (auto dest: real_mult_inverse_cancel simp add: real_mult_ac)
done

lemma inverse_real_of_nat_gt_zero: "0 < inverse (real (Suc n))"
apply auto
done
declare inverse_real_of_nat_gt_zero [simp]

lemma inverse_real_of_nat_ge_zero: "0 <= inverse (real (Suc n))"
apply auto
done
declare inverse_real_of_nat_ge_zero [simp]

lemma real_sum_squares_not_zero: "x ~= 0 ==> x * x + y * y ~= (0::real)"
apply (blast dest!: real_sum_squares_cancel) 
done

lemma real_sum_squares_not_zero2: "y ~= 0 ==> x * x + y * y ~= (0::real)"
apply (blast dest!: real_sum_squares_cancel2) 
done

(* nice theorem *)
lemma abs_mult_abs: "abs x * abs x = x * (x::real)"
apply (insert linorder_less_linear [of x 0]) 
apply (auto simp add: abs_eqI2 abs_minus_eqI2)
done
declare abs_mult_abs [simp]


subsection {*Various Other Theorems*}

lemma realpow_divide: 
    "(x/y) ^ n = ((x::real) ^ n/ y ^ n)"
apply (unfold real_divide_def)
apply (auto simp add: realpow_mult realpow_inverse)
done

lemma realpow_ge_zero2 [rule_format (no_asm)]: "(0::real) <= r --> 0 <= r ^ n"
apply (induct_tac "n")
apply (auto simp add: real_0_le_mult_iff)
done

lemma realpow_le2 [rule_format (no_asm)]: "(0::real) <= x & x <= y --> x ^ n <= y ^ n"
apply (induct_tac "n")
apply (auto intro!: real_mult_le_mono simp add: realpow_ge_zero2)
done

lemma realpow_Suc_gt_one: "(1::real) < r ==> 1 < r ^ (Suc n)"
apply (frule_tac n = "n" in realpow_ge_one)
apply (drule real_le_imp_less_or_eq, safe)
apply (frule real_zero_less_one [THEN real_less_trans])
apply (drule_tac y = "r ^ n" in real_mult_less_mono2)
apply assumption
apply (auto dest: real_less_trans)
done

lemma realpow_two_sum_zero_iff: "(x ^ 2 + y ^ 2 = (0::real)) = (x = 0 & y = 0)"
apply (auto intro: real_sum_squares_cancel real_sum_squares_cancel2 simp add: numeral_2_eq_2)
done
declare realpow_two_sum_zero_iff [simp]

lemma realpow_two_le_add_order: "(0::real) <= u ^ 2 + v ^ 2"
apply (rule real_le_add_order)
apply (auto simp add: numeral_2_eq_2)
done
declare realpow_two_le_add_order [simp]

lemma realpow_two_le_add_order2: "(0::real) <= u ^ 2 + v ^ 2 + w ^ 2"
apply (rule real_le_add_order)+
apply (auto simp add: numeral_2_eq_2)
done
declare realpow_two_le_add_order2 [simp]

lemma real_mult_self_sum_ge_zero: "(0::real) <= x*x + y*y"
apply (cut_tac u = "x" and v = "y" in realpow_two_le_add_order)
apply (auto simp add: numeral_2_eq_2)
done
declare real_mult_self_sum_ge_zero [simp]
declare real_mult_self_sum_ge_zero [THEN abs_eqI1, simp]

lemma real_sum_square_gt_zero: "x ~= 0 ==> (0::real) < x * x + y * y"
apply (cut_tac x = "x" and y = "y" in real_mult_self_sum_ge_zero)
apply (drule real_le_imp_less_or_eq)
apply (drule_tac y = "y" in real_sum_squares_not_zero)
apply auto
done

lemma real_sum_square_gt_zero2: "y ~= 0 ==> (0::real) < x * x + y * y"
apply (rule real_add_commute [THEN subst])
apply (erule real_sum_square_gt_zero)
done

lemma real_minus_mult_self_le: "-(u * u) <= (x * (x::real))"
apply (rule_tac j = "0" in real_le_trans)
apply auto
done
declare real_minus_mult_self_le [simp]

lemma realpow_square_minus_le: "-(u ^ 2) <= (x::real) ^ 2"
apply (auto simp add: numeral_2_eq_2)
done
declare realpow_square_minus_le [simp]

lemma realpow_num_eq_if: "(m::real) ^ n = (if n=0 then 1 else m * m ^ (n - 1))"
apply (case_tac "n")
apply auto
done

lemma real_num_zero_less_two_pow: "0 < (2::real) ^ (4*d)"
apply (induct_tac "d")
apply (auto simp add: realpow_num_eq_if)
done
declare real_num_zero_less_two_pow [simp]

lemma lemma_realpow_num_two_mono: "x * (4::real)   < y ==> x * (2 ^ 8) < y * (2 ^ 6)"
apply (subgoal_tac " (2::real) ^ 8 = 4 * (2 ^ 6) ")
apply (simp (no_asm_simp) add: real_mult_assoc [symmetric])
apply (auto simp add: realpow_num_eq_if)
done

lemma lemma_realpow_4: "2 ^ 2 = (4::real)"
apply (simp (no_asm) add: realpow_num_eq_if)
done
declare lemma_realpow_4 [simp]

lemma lemma_realpow_16: "2 ^ 4 = (16::real)"
apply (simp (no_asm) add: realpow_num_eq_if)
done
declare lemma_realpow_16 [simp]

lemma zero_le_x_squared: "(0::real) <= x^2"
apply (simp add: numeral_2_eq_2)
done
declare zero_le_x_squared [simp]



ML
{*
val realpow_0 = thm "realpow_0";
val realpow_Suc = thm "realpow_Suc";

val realpow_zero = thm "realpow_zero";
val realpow_not_zero = thm "realpow_not_zero";
val realpow_zero_zero = thm "realpow_zero_zero";
val realpow_inverse = thm "realpow_inverse";
val realpow_abs = thm "realpow_abs";
val realpow_add = thm "realpow_add";
val realpow_one = thm "realpow_one";
val realpow_two = thm "realpow_two";
val realpow_gt_zero = thm "realpow_gt_zero";
val realpow_ge_zero = thm "realpow_ge_zero";
val realpow_le = thm "realpow_le";
val realpow_0_left = thm "realpow_0_left";
val realpow_less = thm "realpow_less";
val realpow_eq_one = thm "realpow_eq_one";
val abs_realpow_minus_one = thm "abs_realpow_minus_one";
val realpow_mult = thm "realpow_mult";
val realpow_two_le = thm "realpow_two_le";
val abs_realpow_two = thm "abs_realpow_two";
val realpow_two_abs = thm "realpow_two_abs";
val realpow_two_gt_one = thm "realpow_two_gt_one";
val realpow_ge_one = thm "realpow_ge_one";
val realpow_ge_one2 = thm "realpow_ge_one2";
val two_realpow_ge_one = thm "two_realpow_ge_one";
val two_realpow_gt = thm "two_realpow_gt";
val realpow_minus_one = thm "realpow_minus_one";
val realpow_minus_one_odd = thm "realpow_minus_one_odd";
val realpow_minus_one_even = thm "realpow_minus_one_even";
val realpow_Suc_less = thm "realpow_Suc_less";
val realpow_Suc_le = thm "realpow_Suc_le";
val realpow_zero_le = thm "realpow_zero_le";
val realpow_Suc_le2 = thm "realpow_Suc_le2";
val realpow_Suc_le3 = thm "realpow_Suc_le3";
val realpow_less_le = thm "realpow_less_le";
val realpow_le_le = thm "realpow_le_le";
val realpow_Suc_le_self = thm "realpow_Suc_le_self";
val realpow_Suc_less_one = thm "realpow_Suc_less_one";
val realpow_le_Suc = thm "realpow_le_Suc";
val realpow_less_Suc = thm "realpow_less_Suc";
val realpow_le_Suc2 = thm "realpow_le_Suc2";
val realpow_gt_ge2 = thm "realpow_gt_ge2";
val realpow_ge_ge2 = thm "realpow_ge_ge2";
val realpow_Suc_ge_self2 = thm "realpow_Suc_ge_self2";
val realpow_ge_self2 = thm "realpow_ge_self2";
val realpow_minus_mult = thm "realpow_minus_mult";
val realpow_two_mult_inverse = thm "realpow_two_mult_inverse";
val realpow_two_minus = thm "realpow_two_minus";
val realpow_two_disj = thm "realpow_two_disj";
val realpow_diff = thm "realpow_diff";
val realpow_real_of_nat = thm "realpow_real_of_nat";
val realpow_real_of_nat_two_pos = thm "realpow_real_of_nat_two_pos";
val realpow_increasing = thm "realpow_increasing";
val realpow_Suc_cancel_eq = thm "realpow_Suc_cancel_eq";
val realpow_eq_0_iff = thm "realpow_eq_0_iff";
val zero_less_realpow_abs_iff = thm "zero_less_realpow_abs_iff";
val zero_le_realpow_abs = thm "zero_le_realpow_abs";
val real_of_int_power = thm "real_of_int_power";
val power_real_number_of = thm "power_real_number_of";
val real_power_two = thm "real_power_two";
val real_sqr_ge_zero = thm "real_sqr_ge_zero";
val real_sqr_gt_zero = thm "real_sqr_gt_zero";
val real_sqr_not_zero = thm "real_sqr_not_zero";
val real_sum_squares_cancel_a = thm "real_sum_squares_cancel_a";
val real_mult_inverse_cancel2 = thm "real_mult_inverse_cancel2";
val real_squared_diff_one_factored = thm "real_squared_diff_one_factored";
val real_mult_is_one = thm "real_mult_is_one";
val real_le_add_half_cancel = thm "real_le_add_half_cancel";
val real_minus_half_eq = thm "real_minus_half_eq";
val real_mult_inverse_cancel = thm "real_mult_inverse_cancel";
val real_mult_inverse_cancel2 = thm "real_mult_inverse_cancel2";
val inverse_real_of_nat_gt_zero = thm "inverse_real_of_nat_gt_zero";
val inverse_real_of_nat_ge_zero = thm "inverse_real_of_nat_ge_zero";
val real_sum_squares_not_zero = thm "real_sum_squares_not_zero";
val real_sum_squares_not_zero2 = thm "real_sum_squares_not_zero2";
val abs_mult_abs = thm "abs_mult_abs";

val realpow_divide = thm "realpow_divide";
val realpow_ge_zero2 = thm "realpow_ge_zero2";
val realpow_le2 = thm "realpow_le2";
val realpow_Suc_gt_one = thm "realpow_Suc_gt_one";
val realpow_two_sum_zero_iff = thm "realpow_two_sum_zero_iff";
val realpow_two_le_add_order = thm "realpow_two_le_add_order";
val realpow_two_le_add_order2 = thm "realpow_two_le_add_order2";
val real_mult_self_sum_ge_zero = thm "real_mult_self_sum_ge_zero";
val real_sum_square_gt_zero = thm "real_sum_square_gt_zero";
val real_sum_square_gt_zero2 = thm "real_sum_square_gt_zero2";
val real_minus_mult_self_le = thm "real_minus_mult_self_le";
val realpow_square_minus_le = thm "realpow_square_minus_le";
val realpow_num_eq_if = thm "realpow_num_eq_if";
val real_num_zero_less_two_pow = thm "real_num_zero_less_two_pow";
val lemma_realpow_num_two_mono = thm "lemma_realpow_num_two_mono";
val lemma_realpow_4 = thm "lemma_realpow_4";
val lemma_realpow_16 = thm "lemma_realpow_16";
val zero_le_x_squared = thm "zero_le_x_squared";
*}


end
