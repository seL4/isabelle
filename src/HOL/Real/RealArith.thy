(*  Title:      HOL/RealArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header{*Binary arithmetic and Simplification for the Reals*}

theory RealArith = RealDef
files ("real_arith.ML"):

instance real :: number ..

defs
  real_number_of_def:
    "number_of v == real (number_of v :: int)"
     (*::bin=>real           ::bin=>int*)

text{*Collapse applications of @{term real} to @{term number_of}*}
declare real_number_of_def [symmetric, simp]

lemma real_numeral_0_eq_0: "Numeral0 = (0::real)"
by (simp add: real_number_of_def)

lemma real_numeral_1_eq_1: "Numeral1 = (1::real)"
apply (unfold real_number_of_def)
apply (subst real_of_one [symmetric], simp)
done


subsection{*Arithmetic Operations On Numerals*}

lemma add_real_number_of [simp]:
     "(number_of v :: real) + number_of v' = number_of (bin_add v v')"
by (simp only: real_number_of_def real_of_int_add number_of_add)

lemma minus_real_number_of [simp]:
     "- (number_of w :: real) = number_of (bin_minus w)"
by (simp only: real_number_of_def number_of_minus real_of_int_minus)

lemma diff_real_number_of [simp]: 
   "(number_of v :: real) - number_of w = number_of (bin_add v (bin_minus w))"
by (simp only: real_number_of_def diff_number_of_eq real_of_int_diff)

lemma mult_real_number_of [simp]:
     "(number_of v :: real) * number_of v' = number_of (bin_mult v v')"
by (simp only: real_number_of_def real_of_int_mult number_of_mult)


text{*Lemmas for specialist use, NOT as default simprules*}
lemma real_mult_2: "2 * z = (z+z::real)"
proof -
  have eq: "(2::real) = 1 + 1" by (simp add: real_numeral_1_eq_1 [symmetric])
  thus ?thesis by (simp add: eq left_distrib)
qed

lemma real_mult_2_right: "z * 2 = (z+z::real)"
by (subst mult_commute, rule real_mult_2)


subsection{*Comparisons On Numerals*}

lemma eq_real_number_of [simp]:
     "((number_of v :: real) = number_of v') =  
      iszero (number_of (bin_add v (bin_minus v')))"
by (simp only: real_number_of_def real_of_int_inject eq_number_of_eq)

text{*@{term neg} is used in rewrite rules for binary comparisons*}
lemma less_real_number_of [simp]:
     "((number_of v :: real) < number_of v') =  
      neg (number_of (bin_add v (bin_minus v')))"
by (simp only: real_number_of_def real_of_int_less_iff less_number_of_eq_neg)


text{*New versions of existing theorems involving 0, 1*}

lemma real_minus_1_eq_m1 [simp]: "- 1 = (-1::real)"
by (simp add: real_numeral_1_eq_1 [symmetric])

lemma real_mult_minus1 [simp]: "-1 * z = -(z::real)"
proof -
  have  "-1 * z = (- 1) * z" by (simp add: real_minus_1_eq_m1)
  also have "... = - (1 * z)" by (simp only: minus_mult_left) 
  also have "... = -z" by simp
  finally show ?thesis .
qed

lemma real_mult_minus1_right [simp]: "z * -1 = -(z::real)"
by (subst mult_commute, rule real_mult_minus1)



(** real from type "nat" **)

lemma zero_less_real_of_nat_iff [iff]: "(0 < real (n::nat)) = (0<n)"
by (simp only: real_of_nat_less_iff real_of_nat_zero [symmetric])

lemma zero_le_real_of_nat_iff [iff]: "(0 <= real (n::nat)) = (0<=n)"
by (simp only: real_of_nat_le_iff real_of_nat_zero [symmetric])


(*Like the ones above, for "equals"*)
declare real_of_nat_zero_iff [iff]


subsection{*Simplification of Arithmetic when Nested to the Right*}

lemma real_add_number_of_left [simp]:
     "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::real)"
by (simp add: add_assoc [symmetric])

lemma real_mult_number_of_left [simp]:
     "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::real)"
apply (simp (no_asm) add: mult_assoc [symmetric])
done

lemma real_add_number_of_diff1 [simp]: 
     "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::real)"
apply (unfold real_diff_def)
apply (rule real_add_number_of_left)
done

lemma real_add_number_of_diff2 [simp]:
     "number_of v + (c - number_of w) =  
      number_of (bin_add v (bin_minus w)) + (c::real)"
apply (subst diff_real_number_of [symmetric])
apply (simp only: real_diff_def add_ac)
done


text{*The constant @{term neg} is used in rewrite rules for binary
comparisons. A complication in this proof is that both @{term real} and @{term
number_of} are polymorphic, so that it's difficult to know what types subterms
have. *}
lemma real_of_nat_number_of [simp]:
     "real (number_of v :: nat) =  
        (if neg (number_of v) then 0  
         else (number_of v :: real))"
proof cases
  assume "neg (number_of v)" thus ?thesis by simp
next
  assume neg: "~ neg (number_of v)"
  thus ?thesis
    by (simp only: nat_number_of_def real_of_nat_real_of_int [OF neg], simp) 
qed

declare real_numeral_0_eq_0 [simp] real_numeral_1_eq_1 [simp]


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
       less_real_number_of real_of_int_le_iff)

text{*FIXME: these should go!*}
lemma abs_eqI1: "(0::real)\<le>x ==> abs x = x"
by (unfold real_abs_def, simp)

lemma abs_eqI2: "(0::real) < x ==> abs x = x"
by (unfold real_abs_def, simp)

lemma abs_minus_eqI2: "x < (0::real) ==> abs x = -x"
by (simp add: real_abs_def linorder_not_less [symmetric])

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
