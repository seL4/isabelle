theory RealArith0 = RealBin
files "real_arith0.ML":

(*FIXME: move results further down to Ring_and_Field*)

setup real_arith_setup

subsection{*Facts that need the Arithmetic Decision Procedure*}

lemma real_diff_minus_eq: "x - - y = x + (y::real)"
by simp
declare real_diff_minus_eq [simp]

(** Division and inverse **)

lemma real_inverse_eq_divide: "inverse (x::real) = 1/x"
  by (rule Ring_and_Field.inverse_eq_divide) 

text{*Needed in this non-standard form by Hyperreal/Transcendental*}
lemma real_0_le_divide_iff:
     "((0::real) <= x/y) = ((x <= 0 | 0 <= y) & (0 <= x | y <= 0))"
by (simp add: real_divide_def real_0_le_mult_iff, auto)


(**** Factor cancellation theorems for "real" ****)

(** Cancellation laws for k*m < k*n and m*k < n*k, also for <= and =,
    but not (yet?) for k*m < n*k. **)

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
  by (rule Ring_and_Field.mult_divide_cancel_left) 

lemma real_mult_div_cancel_disj:
     "(k*m) / (k*n) = (if k = (0::real) then 0 else m/n)"
  by (rule Ring_and_Field.mult_divide_cancel_eq_if) 

subsection{* Simprules combining x+y and 0: ARE THEY NEEDED?*}

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


(** Simprules combining x-y and 0; see also real_less_iff_diff_less_0, etc.,
    in RealBin
**)

lemma real_0_less_diff_iff [iff]: "((0::real) < x-y) = (y < x)"
by auto

lemma real_0_le_diff_iff [iff]: "((0::real) \<le> x-y) = (y \<le> x)"
by auto

(*
FIXME: we should have this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric real_diff_def]
*)


(*FIXME: move most of these to Ring_and_Field*)

subsection{*Simplification of Inequalities Involving Literal Divisors*}

lemma pos_real_le_divide_eq: "0<z ==> ((x::real) \<le> y/z) = (x*z \<le> y)"
apply (subgoal_tac " (x*z \<le> y) = (x*z \<le> (y/z) *z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc) 
apply (erule ssubst)
apply (subst real_mult_le_cancel2, simp)
done

lemma neg_real_le_divide_eq: "z<0 ==> ((x::real) \<le> y/z) = (y \<le> x*z)"
apply (subgoal_tac " (y \<le> x*z) = ((y/z) *z \<le> x*z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_le_cancel2, simp)
done

lemma real_le_divide_eq:
  "((x::real) \<le> y/z) = (if 0<z then x*z \<le> y
                        else if z<0 then y \<le> x*z
                        else x\<le>0)"
apply (case_tac "z=0", simp) 
apply (simp add: pos_real_le_divide_eq neg_real_le_divide_eq) 
done

declare real_le_divide_eq [of _ _ "number_of w", standard, simp]

lemma pos_real_divide_le_eq: "0<z ==> (y/z \<le> (x::real)) = (y \<le> x*z)"
apply (subgoal_tac " (y \<le> x*z) = ((y/z) *z \<le> x*z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_le_cancel2, simp)
done

lemma neg_real_divide_le_eq: "z<0 ==> (y/z \<le> (x::real)) = (x*z \<le> y)"
apply (subgoal_tac " (x*z \<le> y) = (x*z \<le> (y/z) *z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_le_cancel2, simp)
done


lemma real_divide_le_eq:
  "(y/z \<le> (x::real)) = (if 0<z then y \<le> x*z
                        else if z<0 then x*z \<le> y
                        else 0 \<le> x)"
apply (case_tac "z=0", simp) 
apply (simp add: pos_real_divide_le_eq neg_real_divide_le_eq) 
done

declare real_divide_le_eq [of _ "number_of w", standard, simp]


lemma pos_real_less_divide_eq: "0<z ==> ((x::real) < y/z) = (x*z < y)"
apply (subgoal_tac " (x*z < y) = (x*z < (y/z) *z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_less_cancel2, simp)
done

lemma neg_real_less_divide_eq: "z<0 ==> ((x::real) < y/z) = (y < x*z)"
apply (subgoal_tac " (y < x*z) = ((y/z) *z < x*z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_less_cancel2, simp)
done

lemma real_less_divide_eq:
  "((x::real) < y/z) = (if 0<z then x*z < y
                        else if z<0 then y < x*z
                        else x<0)"
apply (case_tac "z=0", simp) 
apply (simp add: pos_real_less_divide_eq neg_real_less_divide_eq) 
done

declare real_less_divide_eq [of _ _ "number_of w", standard, simp]

lemma pos_real_divide_less_eq: "0<z ==> (y/z < (x::real)) = (y < x*z)"
apply (subgoal_tac " (y < x*z) = ((y/z) *z < x*z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_less_cancel2, simp)
done

lemma neg_real_divide_less_eq: "z<0 ==> (y/z < (x::real)) = (x*z < y)"
apply (subgoal_tac " (x*z < y) = (x*z < (y/z) *z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_less_cancel2, simp)
done

lemma real_divide_less_eq:
  "(y/z < (x::real)) = (if 0<z then y < x*z
                        else if z<0 then x*z < y
                        else 0 < x)"
apply (case_tac "z=0", simp) 
apply (simp add: pos_real_divide_less_eq neg_real_divide_less_eq) 
done

declare real_divide_less_eq [of _ "number_of w", standard, simp]

lemma nonzero_real_eq_divide_eq: "z\<noteq>0 ==> ((x::real) = y/z) = (x*z = y)"
apply (subgoal_tac " (x*z = y) = (x*z = (y/z) *z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_eq_cancel2, simp)
done

lemma real_eq_divide_eq:
  "((x::real) = y/z) = (if z\<noteq>0 then x*z = y else x=0)"
by (simp add: nonzero_real_eq_divide_eq) 

declare real_eq_divide_eq [of _ _ "number_of w", standard, simp]

lemma nonzero_real_divide_eq_eq: "z\<noteq>0 ==> (y/z = (x::real)) = (y = x*z)"
apply (subgoal_tac " (y = x*z) = ((y/z) *z = x*z) ")
 prefer 2 apply (simp add: real_divide_def real_mult_assoc)
apply (erule ssubst)
apply (subst real_mult_eq_cancel2, simp)
done

lemma real_divide_eq_eq:
  "(y/z = (x::real)) = (if z\<noteq>0 then y = x*z else x=0)"
by (simp add: nonzero_real_divide_eq_eq) 

declare real_divide_eq_eq [of _ "number_of w", standard, simp]

lemma real_divide_eq_cancel2: "(m/k = n/k) = (k = 0 | m = (n::real))"
apply (case_tac "k=0", simp) 
apply (simp add:divide_inverse) 
done

lemma real_divide_eq_cancel1: "(k/m = k/n) = (k = 0 | m = (n::real))" 
by (force simp add: real_divide_eq_eq real_eq_divide_eq)

lemma real_inverse_less_iff:
     "[| 0 < r; 0 < x|] ==> (inverse x < inverse (r::real)) = (r < x)"
by (rule Ring_and_Field.inverse_less_iff_less)

lemma real_inverse_le_iff:
     "[| 0 < r; 0 < x|] ==> (inverse x \<le> inverse r) = (r \<le> (x::real))"
by (rule Ring_and_Field.inverse_le_iff_le)


(** Division by 1, -1 **)

lemma real_divide_1: "(x::real)/1 = x"
by (simp add: real_divide_def)

lemma real_divide_minus1 [simp]: "x/-1 = -(x::real)"
by simp

lemma real_minus1_divide [simp]: "-1/(x::real) = - (1/x)"
by (simp add: real_divide_def real_minus_inverse)

lemma real_lbound_gt_zero:
     "[| (0::real) < d1; 0 < d2 |] ==> \<exists>e. 0 < e & e < d1 & e < d2"
apply (rule_tac x = " (min d1 d2) /2" in exI)
apply (simp add: min_def)
done

(*** Density of the Reals ***)

lemma real_less_half_sum: "x < y ==> x < (x+y) / (2::real)"
by auto

lemma real_gt_half_sum: "x < y ==> (x+y)/(2::real) < y"
by auto

lemma real_dense: "x < y ==> \<exists>r::real. x < r & r < y"
by (blast intro!: real_less_half_sum real_gt_half_sum)

end
