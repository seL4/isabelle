theory RealArith0 = RealBin
files "real_arith0.ML":

setup real_arith_setup

subsection{*Assorted facts that need binary literals and the arithmetic decision procedure*}

lemma real_diff_minus_eq: "x - - y = x + (y::real)"
by simp
declare real_diff_minus_eq [simp]

(** Division and inverse **)

lemma real_0_divide: "0/x = (0::real)"
by (simp add: real_divide_def)
declare real_0_divide [simp]

lemma real_0_less_inverse_iff: "((0::real) < inverse x) = (0 < x)"
apply (case_tac "x=0") 
apply (auto dest: real_inverse_less_0 simp add: linorder_neq_iff real_inverse_gt_0)
done
declare real_0_less_inverse_iff [simp]

lemma real_inverse_less_0_iff: "(inverse x < (0::real)) = (x < 0)"
apply (case_tac "x=0")
apply (auto dest: real_inverse_less_0 simp add: linorder_neq_iff real_inverse_gt_0)
done
declare real_inverse_less_0_iff [simp]

lemma real_0_le_inverse_iff: "((0::real) <= inverse x) = (0 <= x)"
by (simp add: linorder_not_less [symmetric])
declare real_0_le_inverse_iff [simp]

lemma real_inverse_le_0_iff: "(inverse x <= (0::real)) = (x <= 0)"
by (simp add: linorder_not_less [symmetric])
declare real_inverse_le_0_iff [simp]

lemma real_inverse_eq_divide: "inverse (x::real) = 1/x"
by (simp add: real_divide_def)

lemma real_0_less_divide_iff: "((0::real) < x/y) = (0 < x & 0 < y | x < 0 & y < 0)"
by (simp add: real_divide_def real_0_less_mult_iff)
declare real_0_less_divide_iff [of "number_of w", standard, simp]

lemma real_divide_less_0_iff: "(x/y < (0::real)) = (0 < x & y < 0 | x < 0 & 0 < y)"
by (simp add: real_divide_def real_mult_less_0_iff)
declare real_divide_less_0_iff [of "number_of w", standard, simp]

lemma real_0_le_divide_iff: "((0::real) <= x/y) = ((x <= 0 | 0 <= y) & (0 <= x | y <= 0))"
by (simp add: real_divide_def real_0_le_mult_iff, auto)
declare real_0_le_divide_iff [of "number_of w", standard, simp]

lemma real_divide_le_0_iff: "(x/y <= (0::real)) = ((x <= 0 | y <= 0) & (0 <= x | 0 <= y))"
by (simp add: real_divide_def real_mult_le_0_iff, auto)
declare real_divide_le_0_iff [of "number_of w", standard, simp]

lemma real_inverse_zero_iff: "(inverse(x::real) = 0) = (x = 0)"
  by (rule Ring_and_Field.inverse_nonzero_iff_nonzero)

lemma real_divide_eq_0_iff: "(x/y = 0) = (x=0 | y=(0::real))"
by (auto simp add: real_divide_def)
declare real_divide_eq_0_iff [simp]

lemma real_divide_self_eq: "h ~= (0::real) ==> h/h = 1"
  by (rule Ring_and_Field.divide_self)



(**** Factor cancellation theorems for "real" ****)

(** Cancellation laws for k*m < k*n and m*k < n*k, also for <= and =,
    but not (yet?) for k*m < n*k. **)

lemma real_minus_less_minus: "(-y < -x) = ((x::real) < y)"
  by (rule Ring_and_Field.neg_less_iff_less)

lemma real_mult_less_mono1_neg: "[| i<j;  k < (0::real) |] ==> j*k < i*k"
  by (rule Ring_and_Field.mult_strict_right_mono_neg)

lemma real_mult_less_mono2_neg: "[| i<j;  k < (0::real) |] ==> k*j < k*i"
  by (rule Ring_and_Field.mult_strict_left_mono_neg)

lemma real_mult_le_mono1_neg: "[| i <= j;  k <= (0::real) |] ==> j*k <= i*k"
  by (rule Ring_and_Field.mult_right_mono_neg)

lemma real_mult_le_mono2_neg: "[| i <= j;  k <= (0::real) |] ==> k*j <= k*i"
  by (rule Ring_and_Field.mult_left_mono_neg)

lemma real_mult_less_cancel2:
     "(m*k < n*k) = (((0::real) < k & m<n) | (k < 0 & n<m))"
  by (rule Ring_and_Field.mult_less_cancel_right) 

lemma real_mult_le_cancel2:
     "(m*k <= n*k) = (((0::real) < k --> m<=n) & (k < 0 --> n<=m))"
  by (rule Ring_and_Field.mult_le_cancel_right) 

lemma real_mult_less_cancel1:
     "(k*m < k*n) = (((0::real) < k & m<n) | (k < 0 & n<m))"
  by (rule Ring_and_Field.mult_less_cancel_left) 

lemma real_mult_le_cancel1:
     "!!k::real. (k*m <= k*n) = ((0 < k --> m<=n) & (k < 0 --> n<=m))"
  by (rule Ring_and_Field.mult_le_cancel_left) 

lemma real_mult_eq_cancel1: "!!k::real. (k*m = k*n) = (k = 0 | m=n)"
  by (rule Ring_and_Field.mult_cancel_left) 

lemma real_mult_eq_cancel2: "!!k::real. (m*k = n*k) = (k = 0 | m=n)"
  by (rule Ring_and_Field.mult_cancel_right) 

lemma real_mult_div_cancel1: "!!k::real. k~=0 ==> (k*m) / (k*n) = (m/n)"
apply (simp add: real_divide_def real_inverse_distrib)
apply (subgoal_tac "k * m * (inverse k * inverse n) = (k * inverse k) * (m * inverse n) ")
apply simp
apply (simp only: mult_ac)
done

(*For ExtractCommonTerm*)
lemma real_mult_div_cancel_disj: "(k*m) / (k*n) = (if k = (0::real) then 0 else m/n)"
by (simp add: real_mult_div_cancel1)



end
