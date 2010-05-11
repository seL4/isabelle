(*  Title       : HOL/RealPow.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
*)

header {* Natural powers theory *}

theory RealPow
imports RealDef RComplete
begin

(* FIXME: declare this in Rings.thy or not at all *)
declare abs_mult_self [simp]

(* used by Import/HOL/real.imp *)
lemma two_realpow_ge_one: "(1::real) \<le> 2 ^ n"
by simp

lemma two_realpow_gt [simp]: "real (n::nat) < 2 ^ n"
apply (induct "n")
apply (auto simp add: real_of_nat_Suc)
apply (subst mult_2)
apply (erule add_less_le_mono)
apply (rule two_realpow_ge_one)
done

(* TODO: no longer real-specific; rename and move elsewhere *)
lemma realpow_Suc_le_self:
  fixes r :: "'a::linordered_semidom"
  shows "[| 0 \<le> r; r \<le> 1 |] ==> r ^ Suc n \<le> r"
by (insert power_decreasing [of 1 "Suc n" r], simp)

(* TODO: no longer real-specific; rename and move elsewhere *)
lemma realpow_minus_mult:
  fixes x :: "'a::monoid_mult"
  shows "0 < n \<Longrightarrow> x ^ (n - 1) * x = x ^ n"
by (simp add: power_commutes split add: nat_diff_split)

(* TODO: no longer real-specific; rename and move elsewhere *)
lemma realpow_two_diff:
  fixes x :: "'a::comm_ring_1"
  shows "x^Suc (Suc 0) - y^Suc (Suc 0) = (x - y) * (x + y)"
by (simp add: algebra_simps)

(* TODO: move elsewhere *)
lemma add_eq_0_iff:
  fixes x y :: "'a::group_add"
  shows "x + y = 0 \<longleftrightarrow> y = - x"
by (auto dest: minus_unique)

(* TODO: no longer real-specific; rename and move elsewhere *)
lemma realpow_two_disj:
  fixes x :: "'a::idom"
  shows "(x^Suc (Suc 0) = y^Suc (Suc 0)) = (x = y | x = -y)"
using realpow_two_diff [of x y]
by (auto simp add: add_eq_0_iff)


subsection{* Squares of Reals *}

(* FIXME: declare this [simp] for all types, or not at all *)
lemma real_two_squares_add_zero_iff [simp]:
  "(x * x + y * y = 0) = ((x::real) = 0 \<and> y = 0)"
by (rule sum_squares_eq_zero_iff)

(* TODO: no longer real-specific; rename and move elsewhere *)
lemma real_squared_diff_one_factored:
  fixes x :: "'a::ring_1"
  shows "x * x - 1 = (x + 1) * (x - 1)"
by (simp add: algebra_simps)

(* FIXME: declare this [simp] for all types, or not at all *)
lemma realpow_two_sum_zero_iff [simp]:
     "(x ^ 2 + y ^ 2 = (0::real)) = (x = 0 & y = 0)"
by (rule sum_power2_eq_zero_iff)

(* FIXME: declare this [simp] for all types, or not at all *)
lemma realpow_two_le_add_order [simp]: "(0::real) \<le> u ^ 2 + v ^ 2"
by (rule sum_power2_ge_zero)

(* FIXME: declare this [simp] for all types, or not at all *)
lemma realpow_two_le_add_order2 [simp]: "(0::real) \<le> u ^ 2 + v ^ 2 + w ^ 2"
by (intro add_nonneg_nonneg zero_le_power2)

lemma real_minus_mult_self_le [simp]: "-(u * u) \<le> (x * (x::real))"
by (rule_tac y = 0 in order_trans, auto)

lemma realpow_square_minus_le [simp]: "-(u ^ 2) \<le> (x::real) ^ 2"
by (auto simp add: power2_eq_square)

(* The following theorem is by Benjamin Porter *)
(* TODO: no longer real-specific; rename and move elsewhere *)
lemma real_sq_order:
  fixes x :: "'a::linordered_semidom"
  assumes xgt0: "0 \<le> x" and ygt0: "0 \<le> y" and sq: "x^2 \<le> y^2"
  shows "x \<le> y"
proof -
  from sq have "x ^ Suc (Suc 0) \<le> y ^ Suc (Suc 0)"
    by (simp only: numeral_2_eq_2)
  thus "x \<le> y" using ygt0
    by (rule power_le_imp_le_base)
qed

subsection {*Floor*}

lemma floor_power:
  assumes "x = real (floor x)"
  shows "floor (x ^ n) = floor x ^ n"
proof -
  have *: "x ^ n = real (floor x ^ n)"
    using assms by (induct n arbitrary: x) simp_all
  show ?thesis unfolding real_of_int_inject[symmetric]
    unfolding * floor_real_of_int ..
qed

lemma natfloor_power:
  assumes "x = real (natfloor x)"
  shows "natfloor (x ^ n) = natfloor x ^ n"
proof -
  from assms have "0 \<le> floor x" by auto
  note assms[unfolded natfloor_def real_nat_eq_real[OF `0 \<le> floor x`]]
  from floor_power[OF this]
  show ?thesis unfolding natfloor_def nat_power_eq[OF `0 \<le> floor x`, symmetric]
    by simp
qed

subsection {*Various Other Theorems*}

lemma real_le_add_half_cancel: "(x + y/2 \<le> (y::real)) = (x \<le> y /2)"
by auto

lemma real_mult_inverse_cancel:
     "[|(0::real) < x; 0 < x1; x1 * y < x * u |] 
      ==> inverse x * y < inverse x1 * u"
apply (rule_tac c=x in mult_less_imp_less_left) 
apply (auto simp add: mult_assoc [symmetric])
apply (simp (no_asm) add: mult_ac)
apply (rule_tac c=x1 in mult_less_imp_less_right) 
apply (auto simp add: mult_ac)
done

lemma real_mult_inverse_cancel2:
     "[|(0::real) < x;0 < x1; x1 * y < x * u |] ==> y * inverse x < u * inverse x1"
apply (auto dest: real_mult_inverse_cancel simp add: mult_ac)
done

(* TODO: no longer real-specific; rename and move elsewhere *)
lemma realpow_num_eq_if:
  fixes m :: "'a::power"
  shows "m ^ n = (if n=0 then 1 else m * m ^ (n - 1))"
by (cases n, auto)


end
