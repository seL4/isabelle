theory RealArith = RealBin
files ("real_arith.ML"):

use "real_arith.ML"

setup real_arith_setup

subsection{* Simprules combining x+y and 0: ARE THEY NEEDED?*}

text{*Needed in this non-standard form by Hyperreal/Transcendental*}
lemma real_0_le_divide_iff:
     "((0::real) \<le> x/y) = ((x \<le> 0 | 0 \<le> y) & (0 \<le> x | y \<le> 0))"
by (simp add: real_divide_def zero_le_mult_iff, auto)

lemma real_add_minus_iff [simp]: "(x + - a = (0::real)) = (x=a)" 
by arith

lemma real_add_eq_0_iff [iff]: "(x+y = (0::real)) = (y = -x)"
by auto

lemma real_add_less_0_iff [iff]: "(x+y < (0::real)) = (y < -x)"
by auto

lemma real_0_less_add_iff [iff]: "((0::real) < x+y) = (-x < y)"
by auto

lemma real_add_le_0_iff [iff]: "(x+y \<le> (0::real)) = (y \<le> -x)"
by auto

lemma real_0_le_add_iff [iff]: "((0::real) \<le> x+y) = (-x \<le> y)"
by auto


(** Simprules combining x-y and 0 (needed??) **)

lemma real_0_less_diff_iff [iff]: "((0::real) < x-y) = (y < x)"
by auto

lemma real_0_le_diff_iff [iff]: "((0::real) \<le> x-y) = (y \<le> x)"
by auto

(*
FIXME: we should have this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric real_diff_def]
*)

subsubsection{*Division By @{term "-1"}*}

lemma real_divide_minus1 [simp]: "x/-1 = -(x::real)"
by simp

lemma real_minus1_divide [simp]: "-1/(x::real) = - (1/x)"
by (simp add: real_divide_def inverse_minus_eq)

lemma real_lbound_gt_zero:
     "[| (0::real) < d1; 0 < d2 |] ==> \<exists>e. 0 < e & e < d1 & e < d2"
apply (rule_tac x = " (min d1 d2) /2" in exI)
apply (simp add: min_def)
done

(*** Density of the Reals ***)

text{*Similar results are proved in @{text Ring_and_Field}*}
lemma real_less_half_sum: "x < y ==> x < (x+y) / (2::real)"
  by auto

lemma real_gt_half_sum: "x < y ==> (x+y)/(2::real) < y"
  by auto

lemma real_dense: "x < y ==> \<exists>r::real. x < r & r < y"
  by (rule Ring_and_Field.dense)


subsection{*Absolute Value Function for the Reals*}

lemma abs_nat_number_of [simp]: 
     "abs (number_of v :: real) =  
        (if neg (number_of v) then number_of (bin_minus v)  
         else number_of v)"
by (simp add: real_abs_def bin_arith_simps minus_real_number_of
       le_real_number_of_eq_not_less less_real_number_of real_of_int_le_iff)


(*----------------------------------------------------------------------------
       Properties of the absolute value function over the reals
       (adapted version of previously proved theorems about abs)
 ----------------------------------------------------------------------------*)

text{*FIXME: these should go!*}
lemma abs_eqI1: "(0::real)\<le>x ==> abs x = x"
by (unfold real_abs_def, simp)

lemma abs_eqI2: "(0::real) < x ==> abs x = x"
by (unfold real_abs_def, simp)

lemma abs_minus_eqI2: "x < (0::real) ==> abs x = -x"
by (unfold real_abs_def real_le_def, simp)

lemma abs_minus_add_cancel: "abs(x + (-y)) = abs (y + (-(x::real)))"
by (unfold real_abs_def, simp)

lemma abs_minus_one [simp]: "abs (-1) = (1::real)"
by (unfold real_abs_def, simp)

lemma abs_interval_iff: "(abs x < r) = (-r < x & x < (r::real))"
by (force simp add: Ring_and_Field.abs_less_iff)

lemma abs_le_interval_iff: "(abs x \<le> r) = (-r\<le>x & x\<le>(r::real))"
by (force simp add: Ring_and_Field.abs_le_iff)

lemma abs_add_one_gt_zero [simp]: "(0::real) < 1 + abs(x)"
by (unfold real_abs_def, auto)

lemma abs_real_of_nat_cancel [simp]: "abs (real x) = real (x::nat)"
by (auto intro: abs_eqI1 simp add: real_of_nat_ge_zero)

lemma abs_add_one_not_less_self [simp]: "~ abs(x) + (1::real) < x"
apply (simp add: linorder_not_less)
apply (auto intro: abs_ge_self [THEN order_trans])
done
 
text{*Used only in Hyperreal/Lim.ML*}
lemma abs_sum_triangle_ineq: "abs ((x::real) + y + (-l + -m)) \<le> abs(x + -l) + abs(y + -m)"
apply (simp add: real_add_assoc)
apply (rule_tac a1 = y in add_left_commute [THEN ssubst])
apply (rule real_add_assoc [THEN subst])
apply (rule abs_triangle_ineq)
done



ML
{*
val real_0_le_divide_iff = thm"real_0_le_divide_iff";
val real_add_minus_iff = thm"real_add_minus_iff";
val real_add_eq_0_iff = thm"real_add_eq_0_iff";
val real_add_less_0_iff = thm"real_add_less_0_iff";
val real_0_less_add_iff = thm"real_0_less_add_iff";
val real_add_le_0_iff = thm"real_add_le_0_iff";
val real_0_le_add_iff = thm"real_0_le_add_iff";
val real_0_less_diff_iff = thm"real_0_less_diff_iff";
val real_0_le_diff_iff = thm"real_0_le_diff_iff";
val real_divide_minus1 = thm"real_divide_minus1";
val real_minus1_divide = thm"real_minus1_divide";
val real_lbound_gt_zero = thm"real_lbound_gt_zero";
val real_less_half_sum = thm"real_less_half_sum";
val real_gt_half_sum = thm"real_gt_half_sum";
val real_dense = thm"real_dense";

val abs_nat_number_of = thm"abs_nat_number_of";
val abs_eqI1 = thm"abs_eqI1";
val abs_eqI2 = thm"abs_eqI2";
val abs_minus_eqI2 = thm"abs_minus_eqI2";
val abs_ge_zero = thm"abs_ge_zero";
val abs_idempotent = thm"abs_idempotent";
val abs_zero_iff = thm"abs_zero_iff";
val abs_ge_self = thm"abs_ge_self";
val abs_ge_minus_self = thm"abs_ge_minus_self";
val abs_mult = thm"abs_mult";
val abs_inverse = thm"abs_inverse";
val abs_triangle_ineq = thm"abs_triangle_ineq";
val abs_minus_cancel = thm"abs_minus_cancel";
val abs_minus_add_cancel = thm"abs_minus_add_cancel";
val abs_minus_one = thm"abs_minus_one";
val abs_interval_iff = thm"abs_interval_iff";
val abs_le_interval_iff = thm"abs_le_interval_iff";
val abs_add_one_gt_zero = thm"abs_add_one_gt_zero";
val abs_le_zero_iff = thm"abs_le_zero_iff";
val abs_real_of_nat_cancel = thm"abs_real_of_nat_cancel";
val abs_add_one_not_less_self = thm"abs_add_one_not_less_self";
val abs_sum_triangle_ineq = thm"abs_sum_triangle_ineq";

val abs_mult_less = thm"abs_mult_less";
*}

end
