(*  Title       : HOL/Real/RealPow.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
*)

header {* Natural powers theory *}

theory RealPow
imports RealDef
begin

declare abs_mult_self [simp]

instance real :: power ..

primrec (realpow)
     realpow_0:   "r ^ 0       = 1"
     realpow_Suc: "r ^ (Suc n) = (r::real) * (r ^ n)"


instance real :: recpower
proof
  fix z :: real
  fix n :: nat
  show "z^0 = 1" by simp
  show "z^(Suc n) = z * (z^n)" by simp
qed


lemma realpow_zero_zero: "r ^ n = (0::real) ==> r = 0"
by simp

lemma realpow_two: "(r::real)^ (Suc (Suc 0)) = r * r"
by simp

text{*Legacy: weaker version of the theorem @{text power_strict_mono}*}
lemma realpow_less:
     "[|(0::real) < x; x < y; 0 < n|] ==> x ^ n < y ^ n"
apply (rule power_strict_mono, auto) 
done

lemma realpow_two_le [simp]: "(0::real) \<le> r^ Suc (Suc 0)"
by (simp add: real_le_square)

lemma abs_realpow_two [simp]: "abs((x::real)^Suc (Suc 0)) = x^Suc (Suc 0)"
by (simp add: abs_mult)

lemma realpow_two_abs [simp]: "abs(x::real)^Suc (Suc 0) = x^Suc (Suc 0)"
by (simp add: power_abs [symmetric] del: realpow_Suc)

lemma two_realpow_ge_one [simp]: "(1::real) \<le> 2 ^ n"
by (insert power_increasing [of 0 n "2::real"], simp)

lemma two_realpow_gt [simp]: "real (n::nat) < 2 ^ n"
apply (induct "n")
apply (auto simp add: real_of_nat_Suc)
apply (subst mult_2)
apply (rule add_less_le_mono)
apply (auto simp add: two_realpow_ge_one)
done

lemma realpow_Suc_le_self: "[| 0 \<le> r; r \<le> (1::real) |] ==> r ^ Suc n \<le> r"
by (insert power_decreasing [of 1 "Suc n" r], simp)

lemma realpow_minus_mult [rule_format]:
     "0 < n --> (x::real) ^ (n - 1) * x = x ^ n" 
apply (simp split add: nat_diff_split)
done

lemma realpow_two_mult_inverse [simp]:
     "r \<noteq> 0 ==> r * inverse r ^Suc (Suc 0) = inverse (r::real)"
by (simp add: realpow_two real_mult_assoc [symmetric])

lemma realpow_two_minus [simp]: "(-x)^Suc (Suc 0) = (x::real)^Suc (Suc 0)"
by simp

lemma realpow_two_diff:
     "(x::real)^Suc (Suc 0) - y^Suc (Suc 0) = (x - y) * (x + y)"
apply (unfold real_diff_def)
apply (simp add: right_distrib left_distrib mult_ac)
done

lemma realpow_two_disj:
     "((x::real)^Suc (Suc 0) = y^Suc (Suc 0)) = (x = y | x = -y)"
apply (cut_tac x = x and y = y in realpow_two_diff)
apply (auto simp del: realpow_Suc)
done

lemma realpow_real_of_nat: "real (m::nat) ^ n = real (m ^ n)"
apply (induct "n")
apply (auto simp add: real_of_nat_one real_of_nat_mult)
done

lemma realpow_real_of_nat_two_pos [simp] : "0 < real (Suc (Suc 0) ^ n)"
apply (induct "n")
apply (auto simp add: real_of_nat_mult zero_less_mult_iff)
done

(* used by AFP Integration theory *)
lemma realpow_increasing:
     "[|(0::real) \<le> x; 0 \<le> y; x ^ Suc n \<le> y ^ Suc n|] ==> x \<le> y"
  by (rule power_le_imp_le_base)


subsection{*Literal Arithmetic Involving Powers, Type @{typ real}*}

lemma real_of_int_power: "real (x::int) ^ n = real (x ^ n)"
apply (induct "n")
apply (simp_all add: nat_mult_distrib)
done
declare real_of_int_power [symmetric, simp]

lemma power_real_number_of:
     "(number_of v :: real) ^ n = real ((number_of v :: int) ^ n)"
by (simp only: real_number_of [symmetric] real_of_int_power)

declare power_real_number_of [of _ "number_of w", standard, simp]


subsection {* Properties of Squares *}

lemma sum_squares_ge_zero:
  fixes x y :: "'a::ordered_ring_strict"
  shows "0 \<le> x * x + y * y"
by (intro add_nonneg_nonneg zero_le_square)

lemma not_sum_squares_lt_zero:
  fixes x y :: "'a::ordered_ring_strict"
  shows "\<not> x * x + y * y < 0"
by (simp add: linorder_not_less sum_squares_ge_zero)

lemma sum_nonneg_eq_zero_iff:
  fixes x y :: "'a::pordered_ab_group_add"
  assumes x: "0 \<le> x" and y: "0 \<le> y"
  shows "(x + y = 0) = (x = 0 \<and> y = 0)"
proof (auto)
  from y have "x + 0 \<le> x + y" by (rule add_left_mono)
  also assume "x + y = 0"
  finally have "x \<le> 0" by simp
  thus "x = 0" using x by (rule order_antisym)
next
  from x have "0 + y \<le> x + y" by (rule add_right_mono)
  also assume "x + y = 0"
  finally have "y \<le> 0" by simp
  thus "y = 0" using y by (rule order_antisym)
qed

lemma sum_squares_eq_zero_iff:
  fixes x y :: "'a::ordered_ring_strict"
  shows "(x * x + y * y = 0) = (x = 0 \<and> y = 0)"
by (simp add: sum_nonneg_eq_zero_iff zero_le_square)

lemma sum_squares_le_zero_iff:
  fixes x y :: "'a::ordered_ring_strict"
  shows "(x * x + y * y \<le> 0) = (x = 0 \<and> y = 0)"
by (simp add: order_le_less not_sum_squares_lt_zero sum_squares_eq_zero_iff)

lemma sum_squares_gt_zero_iff:
  fixes x y :: "'a::ordered_ring_strict"
  shows "(0 < x * x + y * y) = (x \<noteq> 0 \<or> y \<noteq> 0)"
by (simp add: order_less_le sum_squares_ge_zero sum_squares_eq_zero_iff)

lemma sum_power2_ge_zero:
  fixes x y :: "'a::{ordered_idom,recpower}"
  shows "0 \<le> x\<twosuperior> + y\<twosuperior>"
unfolding power2_eq_square by (rule sum_squares_ge_zero)

lemma not_sum_power2_lt_zero:
  fixes x y :: "'a::{ordered_idom,recpower}"
  shows "\<not> x\<twosuperior> + y\<twosuperior> < 0"
unfolding power2_eq_square by (rule not_sum_squares_lt_zero)

lemma sum_power2_eq_zero_iff:
  fixes x y :: "'a::{ordered_idom,recpower}"
  shows "(x\<twosuperior> + y\<twosuperior> = 0) = (x = 0 \<and> y = 0)"
unfolding power2_eq_square by (rule sum_squares_eq_zero_iff)

lemma sum_power2_le_zero_iff:
  fixes x y :: "'a::{ordered_idom,recpower}"
  shows "(x\<twosuperior> + y\<twosuperior> \<le> 0) = (x = 0 \<and> y = 0)"
unfolding power2_eq_square by (rule sum_squares_le_zero_iff)

lemma sum_power2_gt_zero_iff:
  fixes x y :: "'a::{ordered_idom,recpower}"
  shows "(0 < x\<twosuperior> + y\<twosuperior>) = (x \<noteq> 0 \<or> y \<noteq> 0)"
unfolding power2_eq_square by (rule sum_squares_gt_zero_iff)


subsection{*Various Other Theorems*}

lemma real_sum_squares_cancel_a: "x * x = -(y * y) ==> x = (0::real) & y=0"
  apply (auto dest: real_sum_squares_cancel simp add: real_add_eq_0_iff [symmetric])
  apply (auto dest: real_sum_squares_cancel simp add: add_commute)
  done

lemma real_squared_diff_one_factored: "x*x - (1::real) = (x + 1)*(x - 1)"
by (auto simp add: left_distrib right_distrib real_diff_def)

lemma real_mult_is_one [simp]: "(x*x = (1::real)) = (x = 1 | x = - 1)"
apply auto
apply (drule right_minus_eq [THEN iffD2]) 
apply (auto simp add: real_squared_diff_one_factored)
done

lemma real_le_add_half_cancel: "(x + y/2 \<le> (y::real)) = (x \<le> y /2)"
by auto

lemma real_minus_half_eq [simp]: "(x::real) - x/2 = x/2"
by auto

lemma real_mult_inverse_cancel:
     "[|(0::real) < x; 0 < x1; x1 * y < x * u |] 
      ==> inverse x * y < inverse x1 * u"
apply (rule_tac c=x in mult_less_imp_less_left) 
apply (auto simp add: real_mult_assoc [symmetric])
apply (simp (no_asm) add: mult_ac)
apply (rule_tac c=x1 in mult_less_imp_less_right) 
apply (auto simp add: mult_ac)
done

lemma real_mult_inverse_cancel2:
     "[|(0::real) < x;0 < x1; x1 * y < x * u |] ==> y * inverse x < u * inverse x1"
apply (auto dest: real_mult_inverse_cancel simp add: mult_ac)
done

lemma inverse_real_of_nat_gt_zero [simp]: "0 < inverse (real (Suc n))"
by simp

lemma inverse_real_of_nat_ge_zero [simp]: "0 \<le> inverse (real (Suc n))"
by simp

lemma real_sum_squares_not_zero: "x ~= 0 ==> x * x + y * y ~= (0::real)"
by (blast dest!: real_sum_squares_cancel)

lemma real_sum_squares_not_zero2: "y ~= 0 ==> x * x + y * y ~= (0::real)"
by (blast dest!: real_sum_squares_cancel2)


subsection {*Various Other Theorems*}

lemma realpow_two_sum_zero_iff [simp]:
     "(x ^ 2 + y ^ 2 = (0::real)) = (x = 0 & y = 0)"
apply (auto intro: real_sum_squares_cancel real_sum_squares_cancel2 
                   simp add: power2_eq_square)
done

lemma realpow_two_le_add_order [simp]: "(0::real) \<le> u ^ 2 + v ^ 2"
apply (rule real_le_add_order)
apply (auto simp add: power2_eq_square)
done

lemma realpow_two_le_add_order2 [simp]: "(0::real) \<le> u ^ 2 + v ^ 2 + w ^ 2"
apply (rule real_le_add_order)+
apply (auto simp add: power2_eq_square)
done

lemma real_sum_square_gt_zero: "x ~= 0 ==> (0::real) < x * x + y * y"
apply (cut_tac x = x and y = y in real_mult_self_sum_ge_zero)
apply (drule real_le_imp_less_or_eq)
apply (drule_tac y = y in real_sum_squares_not_zero, auto)
done

lemma real_sum_square_gt_zero2: "y ~= 0 ==> (0::real) < x * x + y * y"
apply (rule real_add_commute [THEN subst])
apply (erule real_sum_square_gt_zero)
done

lemma real_minus_mult_self_le [simp]: "-(u * u) \<le> (x * (x::real))"
by (rule_tac j = 0 in real_le_trans, auto)

lemma realpow_square_minus_le [simp]: "-(u ^ 2) \<le> (x::real) ^ 2"
by (auto simp add: power2_eq_square)

(* The following theorem is by Benjamin Porter *)
lemma real_sq_order:
  fixes x::real
  assumes xgt0: "0 \<le> x" and ygt0: "0 \<le> y" and sq: "x^2 \<le> y^2"
  shows "x \<le> y"
proof -
  from sq have "x ^ Suc (Suc 0) \<le> y ^ Suc (Suc 0)"
    by (simp only: numeral_2_eq_2)
  thus "x \<le> y" using ygt0
    by (rule power_le_imp_le_base)
qed

lemma realpow_num_eq_if: "(m::real) ^ n = (if n=0 then 1 else m * m ^ (n - 1))"
by (case_tac "n", auto)

end
