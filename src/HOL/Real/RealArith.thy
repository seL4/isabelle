theory RealArith = RealArith0
files "real_arith.ML":

setup real_arith_setup

subsection{*Absolute Value Function for the Reals*}

(** abs (absolute value) **)

lemma abs_nat_number_of: 
     "abs (number_of v :: real) =  
        (if neg (number_of v) then number_of (bin_minus v)  
         else number_of v)"
apply (simp add: real_abs_def bin_arith_simps minus_real_number_of le_real_number_of_eq_not_less less_real_number_of real_of_int_le_iff)
done

declare abs_nat_number_of [simp]

lemma abs_split [arith_split]: 
  "P(abs (x::real)) = ((0 <= x --> P x) & (x < 0 --> P(-x)))"
apply (unfold real_abs_def, auto)
done


(*----------------------------------------------------------------------------
       Properties of the absolute value function over the reals
       (adapted version of previously proved theorems about abs)
 ----------------------------------------------------------------------------*)

lemma abs_iff: "abs (r::real) = (if 0<=r then r else -r)"
apply (unfold real_abs_def, auto)
done

lemma abs_zero: "abs 0 = (0::real)"
by (unfold real_abs_def, auto)
declare abs_zero [simp]

lemma abs_one: "abs (1::real) = 1"
by (unfold real_abs_def, simp)
declare abs_one [simp]

lemma abs_eqI1: "(0::real)<=x ==> abs x = x"
by (unfold real_abs_def, simp)

lemma abs_eqI2: "(0::real) < x ==> abs x = x"
by (unfold real_abs_def, simp)

lemma abs_minus_eqI2: "x < (0::real) ==> abs x = -x"
by (unfold real_abs_def real_le_def, simp)

lemma abs_minus_eqI1: "x<=(0::real) ==> abs x = -x"
by (unfold real_abs_def, simp)

lemma abs_ge_zero: "(0::real)<= abs x"
by (unfold real_abs_def, simp)
declare abs_ge_zero [simp]

lemma abs_idempotent: "abs(abs x)=abs (x::real)"
by (unfold real_abs_def, simp)
declare abs_idempotent [simp]

lemma abs_zero_iff: "(abs x = 0) = (x=(0::real))"
by (unfold real_abs_def, simp)
declare abs_zero_iff [iff]

lemma abs_ge_self: "x<=abs (x::real)"
by (unfold real_abs_def, simp)

lemma abs_ge_minus_self: "-x<=abs (x::real)"
by (unfold real_abs_def, simp)

lemma abs_mult: "abs (x * y) = abs x * abs (y::real)"
apply (unfold real_abs_def)
apply (auto dest!: order_antisym simp add: real_0_le_mult_iff)
done

lemma abs_inverse: "abs(inverse(x::real)) = inverse(abs(x))"
apply (unfold real_abs_def)
apply (case_tac "x=0")
apply (auto simp add: real_minus_inverse real_le_less INVERSE_ZERO real_inverse_gt_0)
done

lemma abs_mult_inverse: "abs (x * inverse y) = (abs x) * inverse (abs (y::real))"
by (simp add: abs_mult abs_inverse)

lemma abs_triangle_ineq: "abs(x+y) <= abs x + abs (y::real)"
by (unfold real_abs_def, simp)

(*Unused, but perhaps interesting as an example*)
lemma abs_triangle_ineq_four: "abs(w + x + y + z) <= abs(w) + abs(x) + abs(y) + abs(z::real)"
by (simp add: abs_triangle_ineq [THEN order_trans])

lemma abs_minus_cancel: "abs(-x)=abs(x::real)"
by (unfold real_abs_def, simp)
declare abs_minus_cancel [simp]

lemma abs_minus_add_cancel: "abs(x + (-y)) = abs (y + (-(x::real)))"
by (unfold real_abs_def, simp)

lemma abs_triangle_minus_ineq: "abs(x + (-y)) <= abs x + abs (y::real)"
by (unfold real_abs_def, simp)

lemma abs_add_less [rule_format (no_asm)]: "abs x < r --> abs y < s --> abs(x+y) < r+(s::real)"
by (unfold real_abs_def, simp)

lemma abs_add_minus_less: "abs x < r --> abs y < s --> abs(x+ (-y)) < r+(s::real)"
by (unfold real_abs_def, simp)

(* lemmas manipulating terms *)
lemma real_mult_0_less: "((0::real)*x < r)=(0 < r)"
by simp

lemma real_mult_less_trans: "[| (0::real) < y; x < r; y*r < t*s |] ==> y*x < t*s"
by (blast intro!: real_mult_less_mono2 intro: order_less_trans)

(*USED ONLY IN NEXT THM*)
lemma real_mult_le_less_trans:
     "[| (0::real)<=y; x < r; y*r < t*s; 0 < t*s|] ==> y*x < t*s"
apply (drule order_le_imp_less_or_eq)
apply (fast  elim: real_mult_0_less [THEN iffD2] real_mult_less_trans) 
done

lemma abs_mult_less: "[| abs x < r; abs y < s |] ==> abs(x*y) < r*(s::real)"
apply (simp add: abs_mult)
apply (rule real_mult_le_less_trans)
apply (rule abs_ge_zero, assumption)
apply (rule_tac [2] real_mult_order)
apply (auto intro!: real_mult_less_mono1 abs_ge_zero intro: order_le_less_trans)
done

lemma abs_mult_less2: "[| abs x < r; abs y < s |] ==> abs(x)*abs(y) < r*(s::real)"
by (auto intro: abs_mult_less simp add: abs_mult [symmetric])

lemma abs_less_gt_zero: "abs(x) < r ==> (0::real) < r"
by (blast intro!: order_le_less_trans abs_ge_zero)

lemma abs_minus_one: "abs (-1) = (1::real)"
by (unfold real_abs_def, simp)
declare abs_minus_one [simp]

lemma abs_disj: "abs x =x | abs x = -(x::real)"
by (unfold real_abs_def, auto)

lemma abs_interval_iff: "(abs x < r) = (-r < x & x < (r::real))"
by (unfold real_abs_def, auto)

lemma abs_le_interval_iff: "(abs x <= r) = (-r<=x & x<=(r::real))"
by (unfold real_abs_def, auto)

lemma abs_add_pos_gt_zero: "(0::real) < k ==> 0 < k + abs(x)"
by (unfold real_abs_def, auto)

lemma abs_add_one_gt_zero: "(0::real) < 1 + abs(x)"
by (unfold real_abs_def, auto)
declare abs_add_one_gt_zero [simp]

lemma abs_not_less_zero: "~ abs x < (0::real)"
by (unfold real_abs_def, auto)
declare abs_not_less_zero [simp]

lemma abs_circle: "abs h < abs y - abs x ==> abs (x + h) < abs (y::real)"
by (auto intro: abs_triangle_ineq [THEN order_le_less_trans])

lemma abs_le_zero_iff: "(abs x <= (0::real)) = (x = 0)"
by (unfold real_abs_def, auto)
declare abs_le_zero_iff [simp]

lemma real_0_less_abs_iff: "((0::real) < abs x) = (x ~= 0)"
by (simp add: real_abs_def, arith)
declare real_0_less_abs_iff [simp]

lemma abs_real_of_nat_cancel: "abs (real x) = real (x::nat)"
by (auto intro: abs_eqI1 simp add: real_of_nat_ge_zero)
declare abs_real_of_nat_cancel [simp]

lemma abs_add_one_not_less_self: "~ abs(x) + (1::real) < x"
apply (rule real_leD)
apply (auto intro: abs_ge_self [THEN order_trans])
done
declare abs_add_one_not_less_self [simp]
 
(* used in vector theory *)
lemma abs_triangle_ineq_three: "abs(w + x + (y::real)) <= abs(w) + abs(x) + abs(y)"
by (auto intro!: abs_triangle_ineq [THEN order_trans] real_add_left_mono
                 simp add: real_add_assoc)

lemma abs_diff_less_imp_gt_zero: "abs(x - y) < y ==> (0::real) < y"
apply (unfold real_abs_def)
apply (case_tac "0 <= x - y", auto)
done

lemma abs_diff_less_imp_gt_zero2: "abs(x - y) < x ==> (0::real) < x"
apply (unfold real_abs_def)
apply (case_tac "0 <= x - y", auto)
done

lemma abs_diff_less_imp_gt_zero3: "abs(x - y) < y ==> (0::real) < x"
by (auto simp add: abs_interval_iff)

lemma abs_diff_less_imp_gt_zero4: "abs(x - y) < -y ==> x < (0::real)"
by (auto simp add: abs_interval_iff)

lemma abs_triangle_ineq_minus_cancel: 
     "abs(x) <= abs(x + (-y)) + abs((y::real))"
apply (unfold real_abs_def, auto)
done

lemma abs_sum_triangle_ineq: "abs ((x::real) + y + (-l + -m)) <= abs(x + -l) + abs(y + -m)"
apply (simp add: real_add_assoc)
apply (rule_tac x1 = y in real_add_left_commute [THEN ssubst])
apply (rule real_add_assoc [THEN subst])
apply (rule abs_triangle_ineq)
done

ML
{*
val abs_nat_number_of = thm"abs_nat_number_of";
val abs_split = thm"abs_split";
val abs_iff = thm"abs_iff";
val abs_zero = thm"abs_zero";
val abs_one = thm"abs_one";
val abs_eqI1 = thm"abs_eqI1";
val abs_eqI2 = thm"abs_eqI2";
val abs_minus_eqI2 = thm"abs_minus_eqI2";
val abs_minus_eqI1 = thm"abs_minus_eqI1";
val abs_ge_zero = thm"abs_ge_zero";
val abs_idempotent = thm"abs_idempotent";
val abs_zero_iff = thm"abs_zero_iff";
val abs_ge_self = thm"abs_ge_self";
val abs_ge_minus_self = thm"abs_ge_minus_self";
val abs_mult = thm"abs_mult";
val abs_inverse = thm"abs_inverse";
val abs_mult_inverse = thm"abs_mult_inverse";
val abs_triangle_ineq = thm"abs_triangle_ineq";
val abs_triangle_ineq_four = thm"abs_triangle_ineq_four";
val abs_minus_cancel = thm"abs_minus_cancel";
val abs_minus_add_cancel = thm"abs_minus_add_cancel";
val abs_triangle_minus_ineq = thm"abs_triangle_minus_ineq";
val abs_add_less = thm"abs_add_less";
val abs_add_minus_less = thm"abs_add_minus_less";
val real_mult_0_less = thm"real_mult_0_less";
val real_mult_less_trans = thm"real_mult_less_trans";
val real_mult_le_less_trans = thm"real_mult_le_less_trans";
val abs_mult_less = thm"abs_mult_less";
val abs_mult_less2 = thm"abs_mult_less2";
val abs_less_gt_zero = thm"abs_less_gt_zero";
val abs_minus_one = thm"abs_minus_one";
val abs_disj = thm"abs_disj";
val abs_interval_iff = thm"abs_interval_iff";
val abs_le_interval_iff = thm"abs_le_interval_iff";
val abs_add_pos_gt_zero = thm"abs_add_pos_gt_zero";
val abs_add_one_gt_zero = thm"abs_add_one_gt_zero";
val abs_not_less_zero = thm"abs_not_less_zero";
val abs_circle = thm"abs_circle";
val abs_le_zero_iff = thm"abs_le_zero_iff";
val real_0_less_abs_iff = thm"real_0_less_abs_iff";
val abs_real_of_nat_cancel = thm"abs_real_of_nat_cancel";
val abs_add_one_not_less_self = thm"abs_add_one_not_less_self";
val abs_triangle_ineq_three = thm"abs_triangle_ineq_three";
val abs_diff_less_imp_gt_zero = thm"abs_diff_less_imp_gt_zero";
val abs_diff_less_imp_gt_zero2 = thm"abs_diff_less_imp_gt_zero2";
val abs_diff_less_imp_gt_zero3 = thm"abs_diff_less_imp_gt_zero3";
val abs_diff_less_imp_gt_zero4 = thm"abs_diff_less_imp_gt_zero4";
val abs_triangle_ineq_minus_cancel = thm"abs_triangle_ineq_minus_cancel";
val abs_sum_triangle_ineq = thm"abs_sum_triangle_ineq";
*}

end
