theory RealArith0 = RealBin
files "real_arith0.ML":

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



end
