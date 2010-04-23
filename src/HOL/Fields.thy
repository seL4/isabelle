(*  Title:      HOL/Fields.thy
    Author:     Gertrud Bauer
    Author:     Steven Obua
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

header {* Fields *}

theory Fields
imports Rings
begin

class field = comm_ring_1 + inverse +
  assumes field_inverse: "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes field_divide_inverse: "a / b = a * inverse b"
begin

subclass division_ring
proof
  fix a :: 'a
  assume "a \<noteq> 0"
  thus "inverse a * a = 1" by (rule field_inverse)
  thus "a * inverse a = 1" by (simp only: mult_commute)
next
  fix a b :: 'a
  show "a / b = a * inverse b" by (rule field_divide_inverse)
qed

subclass idom ..

text{*There is no slick version using division by zero.*}
lemma inverse_add:
  "[| a \<noteq> 0;  b \<noteq> 0 |]
   ==> inverse a + inverse b = (a + b) * inverse a * inverse b"
by (simp add: division_ring_inverse_add mult_ac)

lemma nonzero_mult_divide_mult_cancel_left [simp, no_atp]:
assumes [simp]: "b\<noteq>0" and [simp]: "c\<noteq>0" shows "(c*a)/(c*b) = a/b"
proof -
  have "(c*a)/(c*b) = c * a * (inverse b * inverse c)"
    by (simp add: divide_inverse nonzero_inverse_mult_distrib)
  also have "... =  a * inverse b * (inverse c * c)"
    by (simp only: mult_ac)
  also have "... =  a * inverse b" by simp
    finally show ?thesis by (simp add: divide_inverse)
qed

lemma nonzero_mult_divide_mult_cancel_right [simp, no_atp]:
  "\<lbrakk>b \<noteq> 0; c \<noteq> 0\<rbrakk> \<Longrightarrow> (a * c) / (b * c) = a / b"
by (simp add: mult_commute [of _ c])

lemma times_divide_eq_left: "(b / c) * a = (b * a) / c"
  by (simp add: divide_inverse mult_ac)

text {* These are later declared as simp rules. *}
lemmas times_divide_eq [no_atp] = times_divide_eq_right times_divide_eq_left

lemma add_frac_eq:
  assumes "y \<noteq> 0" and "z \<noteq> 0"
  shows "x / y + w / z = (x * z + w * y) / (y * z)"
proof -
  have "x / y + w / z = (x * z) / (y * z) + (y * w) / (y * z)"
    using assms by simp
  also have "\<dots> = (x * z + y * w) / (y * z)"
    by (simp only: add_divide_distrib)
  finally show ?thesis
    by (simp only: mult_commute)
qed

text{*Special Cancellation Simprules for Division*}

lemma nonzero_mult_divide_cancel_right [simp, no_atp]:
  "b \<noteq> 0 \<Longrightarrow> a * b / b = a"
  using nonzero_mult_divide_mult_cancel_right [of 1 b a] by simp

lemma nonzero_mult_divide_cancel_left [simp, no_atp]:
  "a \<noteq> 0 \<Longrightarrow> a * b / a = b"
using nonzero_mult_divide_mult_cancel_left [of 1 a b] by simp

lemma nonzero_divide_mult_cancel_right [simp, no_atp]:
  "\<lbrakk>a \<noteq> 0; b \<noteq> 0\<rbrakk> \<Longrightarrow> b / (a * b) = 1 / a"
using nonzero_mult_divide_mult_cancel_right [of a b 1] by simp

lemma nonzero_divide_mult_cancel_left [simp, no_atp]:
  "\<lbrakk>a \<noteq> 0; b \<noteq> 0\<rbrakk> \<Longrightarrow> a / (a * b) = 1 / b"
using nonzero_mult_divide_mult_cancel_left [of b a 1] by simp

lemma nonzero_mult_divide_mult_cancel_left2 [simp, no_atp]:
  "\<lbrakk>b \<noteq> 0; c \<noteq> 0\<rbrakk> \<Longrightarrow> (c * a) / (b * c) = a / b"
using nonzero_mult_divide_mult_cancel_left [of b c a] by (simp add: mult_ac)

lemma nonzero_mult_divide_mult_cancel_right2 [simp, no_atp]:
  "\<lbrakk>b \<noteq> 0; c \<noteq> 0\<rbrakk> \<Longrightarrow> (a * c) / (c * b) = a / b"
using nonzero_mult_divide_mult_cancel_right [of b c a] by (simp add: mult_ac)

lemma add_divide_eq_iff:
  "z \<noteq> 0 \<Longrightarrow> x + y / z = (z * x + y) / z"
  by (simp add: add_divide_distrib)

lemma divide_add_eq_iff:
  "z \<noteq> 0 \<Longrightarrow> x / z + y = (x + z * y) / z"
  by (simp add: add_divide_distrib)

lemma diff_divide_eq_iff:
  "z \<noteq> 0 \<Longrightarrow> x - y / z = (z * x - y) / z"
  by (simp add: diff_divide_distrib)

lemma divide_diff_eq_iff:
  "z \<noteq> 0 \<Longrightarrow> x / z - y = (x - z * y) / z"
  by (simp add: diff_divide_distrib)

lemmas field_eq_simps[no_atp] = algebra_simps
  (* pull / out*)
  add_divide_eq_iff divide_add_eq_iff
  diff_divide_eq_iff divide_diff_eq_iff
  (* multiply eqn *)
  nonzero_eq_divide_eq nonzero_divide_eq_eq
  times_divide_eq_left times_divide_eq_right

text{*An example:*}
lemma "\<lbrakk>a\<noteq>b; c\<noteq>d; e\<noteq>f\<rbrakk> \<Longrightarrow> ((a-b)*(c-d)*(e-f))/((c-d)*(e-f)*(a-b)) = 1"
apply(subgoal_tac "(c-d)*(e-f)*(a-b) \<noteq> 0")
 apply(simp add:field_eq_simps)
apply(simp)
done

lemma diff_frac_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y - w / z = (x * z - w * y) / (y * z)"
  by (simp add: field_eq_simps times_divide_eq)

lemma frac_eq_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> (x / y = w / z) = (x * z = w * y)"
  by (simp add: field_eq_simps times_divide_eq)

end

text{*This version builds in division by zero while also re-orienting
      the right-hand side.*}
lemma inverse_mult_distrib [simp]:
     "inverse(a*b) = inverse(a) * inverse(b::'a::{field,division_by_zero})"
  proof cases
    assume "a \<noteq> 0 & b \<noteq> 0" 
    thus ?thesis by (simp add: nonzero_inverse_mult_distrib mult_ac)
  next
    assume "~ (a \<noteq> 0 & b \<noteq> 0)" 
    thus ?thesis by force
  qed

lemma inverse_divide [simp]:
  "inverse (a/b) = b / (a::'a::{field,division_by_zero})"
  by (simp add: divide_inverse mult_commute)


text {* Calculations with fractions *}

text{* There is a whole bunch of simp-rules just for class @{text
field} but none for class @{text field} and @{text nonzero_divides}
because the latter are covered by a simproc. *}

lemma mult_divide_mult_cancel_left:
  "c\<noteq>0 ==> (c*a) / (c*b) = a / (b::'a::{field,division_by_zero})"
apply (cases "b = 0")
apply simp_all
done

lemma mult_divide_mult_cancel_right:
  "c\<noteq>0 ==> (a*c) / (b*c) = a / (b::'a::{field,division_by_zero})"
apply (cases "b = 0")
apply simp_all
done

lemma divide_divide_eq_right [simp,no_atp]:
  "a / (b/c) = (a*c) / (b::'a::{field,division_by_zero})"
by (simp add: divide_inverse mult_ac)

lemma divide_divide_eq_left [simp,no_atp]:
  "(a / b) / (c::'a::{field,division_by_zero}) = a / (b*c)"
by (simp add: divide_inverse mult_assoc)


text {*Special Cancellation Simprules for Division*}

lemma mult_divide_mult_cancel_left_if[simp,no_atp]:
fixes c :: "'a :: {field,division_by_zero}"
shows "(c*a) / (c*b) = (if c=0 then 0 else a/b)"
by (simp add: mult_divide_mult_cancel_left)


text {* Division and Unary Minus *}

lemma minus_divide_right: "- (a/b) = a / -(b::'a::{field,division_by_zero})"
by (simp add: divide_inverse)

lemma divide_minus_right [simp, no_atp]:
  "a / -(b::'a::{field,division_by_zero}) = -(a / b)"
by (simp add: divide_inverse)

lemma minus_divide_divide:
  "(-a)/(-b) = a / (b::'a::{field,division_by_zero})"
apply (cases "b=0", simp) 
apply (simp add: nonzero_minus_divide_divide) 
done

lemma eq_divide_eq:
  "((a::'a::{field,division_by_zero}) = b/c) = (if c\<noteq>0 then a*c = b else a=0)"
by (simp add: nonzero_eq_divide_eq)

lemma divide_eq_eq:
  "(b/c = (a::'a::{field,division_by_zero})) = (if c\<noteq>0 then b = a*c else a=0)"
by (force simp add: nonzero_divide_eq_eq)

lemma inverse_eq_1_iff [simp]:
  "(inverse x = 1) = (x = (1::'a::{field,division_by_zero}))"
by (insert inverse_eq_iff_eq [of x 1], simp) 

lemma divide_eq_0_iff [simp,no_atp]:
     "(a/b = 0) = (a=0 | b=(0::'a::{field,division_by_zero}))"
by (simp add: divide_inverse)

lemma divide_cancel_right [simp,no_atp]:
     "(a/c = b/c) = (c = 0 | a = (b::'a::{field,division_by_zero}))"
apply (cases "c=0", simp)
apply (simp add: divide_inverse)
done

lemma divide_cancel_left [simp,no_atp]:
     "(c/a = c/b) = (c = 0 | a = (b::'a::{field,division_by_zero}))" 
apply (cases "c=0", simp)
apply (simp add: divide_inverse)
done

lemma divide_eq_1_iff [simp,no_atp]:
     "(a/b = 1) = (b \<noteq> 0 & a = (b::'a::{field,division_by_zero}))"
apply (cases "b=0", simp)
apply (simp add: right_inverse_eq)
done

lemma one_eq_divide_iff [simp,no_atp]:
     "(1 = a/b) = (b \<noteq> 0 & a = (b::'a::{field,division_by_zero}))"
by (simp add: eq_commute [of 1])


text {* Ordered Fields *}

class linordered_field = field + linordered_idom
begin

lemma positive_imp_inverse_positive: 
  assumes a_gt_0: "0 < a" 
  shows "0 < inverse a"
proof -
  have "0 < a * inverse a" 
    by (simp add: a_gt_0 [THEN less_imp_not_eq2])
  thus "0 < inverse a" 
    by (simp add: a_gt_0 [THEN less_not_sym] zero_less_mult_iff)
qed

lemma negative_imp_inverse_negative:
  "a < 0 \<Longrightarrow> inverse a < 0"
  by (insert positive_imp_inverse_positive [of "-a"], 
    simp add: nonzero_inverse_minus_eq less_imp_not_eq)

lemma inverse_le_imp_le:
  assumes invle: "inverse a \<le> inverse b" and apos: "0 < a"
  shows "b \<le> a"
proof (rule classical)
  assume "~ b \<le> a"
  hence "a < b"  by (simp add: linorder_not_le)
  hence bpos: "0 < b"  by (blast intro: apos less_trans)
  hence "a * inverse a \<le> a * inverse b"
    by (simp add: apos invle less_imp_le mult_left_mono)
  hence "(a * inverse a) * b \<le> (a * inverse b) * b"
    by (simp add: bpos less_imp_le mult_right_mono)
  thus "b \<le> a"  by (simp add: mult_assoc apos bpos less_imp_not_eq2)
qed

lemma inverse_positive_imp_positive:
  assumes inv_gt_0: "0 < inverse a" and nz: "a \<noteq> 0"
  shows "0 < a"
proof -
  have "0 < inverse (inverse a)"
    using inv_gt_0 by (rule positive_imp_inverse_positive)
  thus "0 < a"
    using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_negative_imp_negative:
  assumes inv_less_0: "inverse a < 0" and nz: "a \<noteq> 0"
  shows "a < 0"
proof -
  have "inverse (inverse a) < 0"
    using inv_less_0 by (rule negative_imp_inverse_negative)
  thus "a < 0" using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma linordered_field_no_lb:
  "\<forall>x. \<exists>y. y < x"
proof
  fix x::'a
  have m1: "- (1::'a) < 0" by simp
  from add_strict_right_mono[OF m1, where c=x] 
  have "(- 1) + x < x" by simp
  thus "\<exists>y. y < x" by blast
qed

lemma linordered_field_no_ub:
  "\<forall> x. \<exists>y. y > x"
proof
  fix x::'a
  have m1: " (1::'a) > 0" by simp
  from add_strict_right_mono[OF m1, where c=x] 
  have "1 + x > x" by simp
  thus "\<exists>y. y > x" by blast
qed

lemma less_imp_inverse_less:
  assumes less: "a < b" and apos:  "0 < a"
  shows "inverse b < inverse a"
proof (rule ccontr)
  assume "~ inverse b < inverse a"
  hence "inverse a \<le> inverse b" by simp
  hence "~ (a < b)"
    by (simp add: not_less inverse_le_imp_le [OF _ apos])
  thus False by (rule notE [OF _ less])
qed

lemma inverse_less_imp_less:
  "inverse a < inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b < a"
apply (simp add: less_le [of "inverse a"] less_le [of "b"])
apply (force dest!: inverse_le_imp_le nonzero_inverse_eq_imp_eq) 
done

text{*Both premises are essential. Consider -1 and 1.*}
lemma inverse_less_iff_less [simp,no_atp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  by (blast intro: less_imp_inverse_less dest: inverse_less_imp_less) 

lemma le_imp_inverse_le:
  "a \<le> b \<Longrightarrow> 0 < a \<Longrightarrow> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less)

lemma inverse_le_iff_le [simp,no_atp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le dest: inverse_le_imp_le) 


text{*These results refer to both operands being negative.  The opposite-sign
case is trivial, since inverse preserves signs.*}
lemma inverse_le_imp_le_neg:
  "inverse a \<le> inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b \<le> a"
apply (rule classical) 
apply (subgoal_tac "a < 0") 
 prefer 2 apply force
apply (insert inverse_le_imp_le [of "-b" "-a"])
apply (simp add: nonzero_inverse_minus_eq) 
done

lemma less_imp_inverse_less_neg:
   "a < b \<Longrightarrow> b < 0 \<Longrightarrow> inverse b < inverse a"
apply (subgoal_tac "a < 0") 
 prefer 2 apply (blast intro: less_trans) 
apply (insert less_imp_inverse_less [of "-b" "-a"])
apply (simp add: nonzero_inverse_minus_eq) 
done

lemma inverse_less_imp_less_neg:
   "inverse a < inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b < a"
apply (rule classical) 
apply (subgoal_tac "a < 0") 
 prefer 2
 apply force
apply (insert inverse_less_imp_less [of "-b" "-a"])
apply (simp add: nonzero_inverse_minus_eq) 
done

lemma inverse_less_iff_less_neg [simp,no_atp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
apply (insert inverse_less_iff_less [of "-b" "-a"])
apply (simp del: inverse_less_iff_less 
            add: nonzero_inverse_minus_eq)
done

lemma le_imp_inverse_le_neg:
  "a \<le> b \<Longrightarrow> b < 0 ==> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp,no_atp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg) 

lemma pos_le_divide_eq: "0 < c ==> (a \<le> b/c) = (a*c \<le> b)"
proof -
  assume less: "0<c"
  hence "(a \<le> b/c) = (a*c \<le> (b/c)*c)"
    by (simp add: mult_le_cancel_right less_not_sym [OF less])
  also have "... = (a*c \<le> b)"
    by (simp add: less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_le_divide_eq: "c < 0 ==> (a \<le> b/c) = (b \<le> a*c)"
proof -
  assume less: "c<0"
  hence "(a \<le> b/c) = ((b/c)*c \<le> a*c)"
    by (simp add: mult_le_cancel_right less_not_sym [OF less])
  also have "... = (b \<le> a*c)"
    by (simp add: less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma pos_less_divide_eq:
     "0 < c ==> (a < b/c) = (a*c < b)"
proof -
  assume less: "0<c"
  hence "(a < b/c) = (a*c < (b/c)*c)"
    by (simp add: mult_less_cancel_right_disj less_not_sym [OF less])
  also have "... = (a*c < b)"
    by (simp add: less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_less_divide_eq:
 "c < 0 ==> (a < b/c) = (b < a*c)"
proof -
  assume less: "c<0"
  hence "(a < b/c) = ((b/c)*c < a*c)"
    by (simp add: mult_less_cancel_right_disj less_not_sym [OF less])
  also have "... = (b < a*c)"
    by (simp add: less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma pos_divide_less_eq:
     "0 < c ==> (b/c < a) = (b < a*c)"
proof -
  assume less: "0<c"
  hence "(b/c < a) = ((b/c)*c < a*c)"
    by (simp add: mult_less_cancel_right_disj less_not_sym [OF less])
  also have "... = (b < a*c)"
    by (simp add: less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_divide_less_eq:
 "c < 0 ==> (b/c < a) = (a*c < b)"
proof -
  assume less: "c<0"
  hence "(b/c < a) = (a*c < (b/c)*c)"
    by (simp add: mult_less_cancel_right_disj less_not_sym [OF less])
  also have "... = (a*c < b)"
    by (simp add: less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma pos_divide_le_eq: "0 < c ==> (b/c \<le> a) = (b \<le> a*c)"
proof -
  assume less: "0<c"
  hence "(b/c \<le> a) = ((b/c)*c \<le> a*c)"
    by (simp add: mult_le_cancel_right less_not_sym [OF less])
  also have "... = (b \<le> a*c)"
    by (simp add: less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_divide_le_eq: "c < 0 ==> (b/c \<le> a) = (a*c \<le> b)"
proof -
  assume less: "c<0"
  hence "(b/c \<le> a) = (a*c \<le> (b/c)*c)"
    by (simp add: mult_le_cancel_right less_not_sym [OF less])
  also have "... = (a*c \<le> b)"
    by (simp add: less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

text{* Lemmas @{text field_simps} multiply with denominators in in(equations)
if they can be proved to be non-zero (for equations) or positive/negative
(for inequations). Can be too aggressive and is therefore separate from the
more benign @{text algebra_simps}. *}

lemmas field_simps[no_atp] = field_eq_simps
  (* multiply ineqn *)
  pos_divide_less_eq neg_divide_less_eq
  pos_less_divide_eq neg_less_divide_eq
  pos_divide_le_eq neg_divide_le_eq
  pos_le_divide_eq neg_le_divide_eq

thm field_eq_simps

text{* Lemmas @{text sign_simps} is a first attempt to automate proofs
of positivity/negativity needed for @{text field_simps}. Have not added @{text
sign_simps} to @{text field_simps} because the former can lead to case
explosions. *}

lemmas sign_simps[no_atp] = group_simps
  zero_less_mult_iff mult_less_0_iff

(* Only works once linear arithmetic is installed:
text{*An example:*}
lemma fixes a b c d e f :: "'a::linordered_field"
shows "\<lbrakk>a>b; c<d; e<f; 0 < u \<rbrakk> \<Longrightarrow>
 ((a-b)*(c-d)*(e-f))/((c-d)*(e-f)*(a-b)) <
 ((e-f)*(a-b)*(c-d))/((e-f)*(a-b)*(c-d)) + u"
apply(subgoal_tac "(c-d)*(e-f)*(a-b) > 0")
 prefer 2 apply(simp add:sign_simps)
apply(subgoal_tac "(c-d)*(e-f)*(a-b)*u > 0")
 prefer 2 apply(simp add:sign_simps)
apply(simp add:field_simps)
done
*)

lemma divide_pos_pos:
  "0 < x ==> 0 < y ==> 0 < x / y"
by(simp add:field_simps)

lemma divide_nonneg_pos:
  "0 <= x ==> 0 < y ==> 0 <= x / y"
by(simp add:field_simps)

lemma divide_neg_pos:
  "x < 0 ==> 0 < y ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonpos_pos:
  "x <= 0 ==> 0 < y ==> x / y <= 0"
by(simp add:field_simps)

lemma divide_pos_neg:
  "0 < x ==> y < 0 ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonneg_neg:
  "0 <= x ==> y < 0 ==> x / y <= 0" 
by(simp add:field_simps)

lemma divide_neg_neg:
  "x < 0 ==> y < 0 ==> 0 < x / y"
by(simp add:field_simps)

lemma divide_nonpos_neg:
  "x <= 0 ==> y < 0 ==> 0 <= x / y"
by(simp add:field_simps)

lemma divide_strict_right_mono:
     "[|a < b; 0 < c|] ==> a / c < b / c"
by (simp add: less_imp_not_eq2 divide_inverse mult_strict_right_mono 
              positive_imp_inverse_positive)


lemma divide_strict_right_mono_neg:
     "[|b < a; c < 0|] ==> a / c < b / c"
apply (drule divide_strict_right_mono [of _ _ "-c"], simp)
apply (simp add: less_imp_not_eq nonzero_minus_divide_right [symmetric])
done

text{*The last premise ensures that @{term a} and @{term b} 
      have the same sign*}
lemma divide_strict_left_mono:
  "[|b < a; 0 < c; 0 < a*b|] ==> c / a < c / b"
by(auto simp: field_simps times_divide_eq zero_less_mult_iff mult_strict_right_mono)

lemma divide_left_mono:
  "[|b \<le> a; 0 \<le> c; 0 < a*b|] ==> c / a \<le> c / b"
by(auto simp: field_simps times_divide_eq zero_less_mult_iff mult_right_mono)

lemma divide_strict_left_mono_neg:
  "[|a < b; c < 0; 0 < a*b|] ==> c / a < c / b"
by(auto simp: field_simps times_divide_eq zero_less_mult_iff mult_strict_right_mono_neg)

lemma mult_imp_div_pos_le: "0 < y ==> x <= z * y ==>
    x / y <= z"
by (subst pos_divide_le_eq, assumption+)

lemma mult_imp_le_div_pos: "0 < y ==> z * y <= x ==>
    z <= x / y"
by(simp add:field_simps)

lemma mult_imp_div_pos_less: "0 < y ==> x < z * y ==>
    x / y < z"
by(simp add:field_simps)

lemma mult_imp_less_div_pos: "0 < y ==> z * y < x ==>
    z < x / y"
by(simp add:field_simps)

lemma frac_le: "0 <= x ==> 
    x <= y ==> 0 < w ==> w <= z  ==> x / z <= y / w"
  apply (rule mult_imp_div_pos_le)
  apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_le_div_pos, assumption)
  apply (rule mult_mono)
  apply simp_all
done

lemma frac_less: "0 <= x ==> 
    x < y ==> 0 < w ==> w <= z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_less_le_imp_less)
  apply simp_all
done

lemma frac_less2: "0 < x ==> 
    x <= y ==> 0 < w ==> w < z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp_all
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_le_less_imp_less)
  apply simp_all
done

text{*It's not obvious whether these should be simprules or not. 
  Their effect is to gather terms into one big fraction, like
  a*b*c / x*y*z. The rationale for that is unclear, but many proofs 
  seem to need them.*}

declare times_divide_eq [simp]

lemma less_half_sum: "a < b ==> a < (a+b) / (1+1)"
by (simp add: field_simps zero_less_two)

lemma gt_half_sum: "a < b ==> (a+b)/(1+1) < b"
by (simp add: field_simps zero_less_two)

subclass dense_linorder
proof
  fix x y :: 'a
  from less_add_one show "\<exists>y. x < y" .. 
  from less_add_one have "x + (- 1) < (x + 1) + (- 1)" by (rule add_strict_right_mono)
  then have "x - 1 < x + 1 - 1" by (simp only: diff_minus [symmetric])
  then have "x - 1 < x" by (simp add: algebra_simps)
  then show "\<exists>y. y < x" ..
  show "x < y \<Longrightarrow> \<exists>z>x. z < y" by (blast intro!: less_half_sum gt_half_sum)
qed

lemma nonzero_abs_inverse:
     "a \<noteq> 0 ==> \<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
apply (auto simp add: neq_iff abs_if nonzero_inverse_minus_eq 
                      negative_imp_inverse_negative)
apply (blast intro: positive_imp_inverse_positive elim: less_asym) 
done

lemma nonzero_abs_divide:
     "b \<noteq> 0 ==> \<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
  by (simp add: divide_inverse abs_mult nonzero_abs_inverse) 

lemma field_le_epsilon:
  assumes e: "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (rule dense_le)
  fix t assume "t < x"
  hence "0 < x - t" by (simp add: less_diff_eq)
  from e [OF this] have "x + 0 \<le> x + (y - t)" by (simp add: algebra_simps)
  then have "0 \<le> y - t" by (simp only: add_le_cancel_left)
  then show "t \<le> y" by (simp add: algebra_simps)
qed

end

lemma le_divide_eq:
  "(a \<le> b/c) = 
   (if 0 < c then a*c \<le> b
             else if c < 0 then b \<le> a*c
             else  a \<le> (0::'a::{linordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_le_divide_eq neg_le_divide_eq linorder_neq_iff) 
done

lemma inverse_positive_iff_positive [simp]:
  "(0 < inverse a) = (0 < (a::'a::{linordered_field,division_by_zero}))"
apply (cases "a = 0", simp)
apply (blast intro: inverse_positive_imp_positive positive_imp_inverse_positive)
done

lemma inverse_negative_iff_negative [simp]:
  "(inverse a < 0) = (a < (0::'a::{linordered_field,division_by_zero}))"
apply (cases "a = 0", simp)
apply (blast intro: inverse_negative_imp_negative negative_imp_inverse_negative)
done

lemma inverse_nonnegative_iff_nonnegative [simp]:
  "(0 \<le> inverse a) = (0 \<le> (a::'a::{linordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric])

lemma inverse_nonpositive_iff_nonpositive [simp]:
  "(inverse a \<le> 0) = (a \<le> (0::'a::{linordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric])

lemma one_less_inverse_iff:
  "(1 < inverse x) = (0 < x & x < (1::'a::{linordered_field,division_by_zero}))"
proof cases
  assume "0 < x"
    with inverse_less_iff_less [OF zero_less_one, of x]
    show ?thesis by simp
next
  assume notless: "~ (0 < x)"
  have "~ (1 < inverse x)"
  proof
    assume "1 < inverse x"
    also with notless have "... \<le> 0" by (simp add: linorder_not_less)
    also have "... < 1" by (rule zero_less_one) 
    finally show False by auto
  qed
  with notless show ?thesis by simp
qed

lemma one_le_inverse_iff:
  "(1 \<le> inverse x) = (0 < x & x \<le> (1::'a::{linordered_field,division_by_zero}))"
by (force simp add: order_le_less one_less_inverse_iff)

lemma inverse_less_1_iff:
  "(inverse x < 1) = (x \<le> 0 | 1 < (x::'a::{linordered_field,division_by_zero}))"
by (simp add: linorder_not_le [symmetric] one_le_inverse_iff) 

lemma inverse_le_1_iff:
  "(inverse x \<le> 1) = (x \<le> 0 | 1 \<le> (x::'a::{linordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric] one_less_inverse_iff) 

lemma divide_le_eq:
  "(b/c \<le> a) = 
   (if 0 < c then b \<le> a*c
             else if c < 0 then a*c \<le> b
             else 0 \<le> (a::'a::{linordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_divide_le_eq neg_divide_le_eq linorder_neq_iff) 
done

lemma less_divide_eq:
  "(a < b/c) = 
   (if 0 < c then a*c < b
             else if c < 0 then b < a*c
             else  a < (0::'a::{linordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_less_divide_eq neg_less_divide_eq linorder_neq_iff) 
done

lemma divide_less_eq:
  "(b/c < a) = 
   (if 0 < c then b < a*c
             else if c < 0 then a*c < b
             else 0 < (a::'a::{linordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_divide_less_eq neg_divide_less_eq linorder_neq_iff) 
done

text {*Division and Signs*}

lemma zero_less_divide_iff:
     "((0::'a::{linordered_field,division_by_zero}) < a/b) = (0 < a & 0 < b | a < 0 & b < 0)"
by (simp add: divide_inverse zero_less_mult_iff)

lemma divide_less_0_iff:
     "(a/b < (0::'a::{linordered_field,division_by_zero})) = 
      (0 < a & b < 0 | a < 0 & 0 < b)"
by (simp add: divide_inverse mult_less_0_iff)

lemma zero_le_divide_iff:
     "((0::'a::{linordered_field,division_by_zero}) \<le> a/b) =
      (0 \<le> a & 0 \<le> b | a \<le> 0 & b \<le> 0)"
by (simp add: divide_inverse zero_le_mult_iff)

lemma divide_le_0_iff:
     "(a/b \<le> (0::'a::{linordered_field,division_by_zero})) =
      (0 \<le> a & b \<le> 0 | a \<le> 0 & 0 \<le> b)"
by (simp add: divide_inverse mult_le_0_iff)

text {* Division and the Number One *}

text{*Simplify expressions equated with 1*}

lemma zero_eq_1_divide_iff [simp,no_atp]:
     "((0::'a::{linordered_field,division_by_zero}) = 1/a) = (a = 0)"
apply (cases "a=0", simp)
apply (auto simp add: nonzero_eq_divide_eq)
done

lemma one_divide_eq_0_iff [simp,no_atp]:
     "(1/a = (0::'a::{linordered_field,division_by_zero})) = (a = 0)"
apply (cases "a=0", simp)
apply (insert zero_neq_one [THEN not_sym])
apply (auto simp add: nonzero_divide_eq_eq)
done

text{*Simplify expressions such as @{text "0 < 1/x"} to @{text "0 < x"}*}
lemmas zero_less_divide_1_iff = zero_less_divide_iff [of 1, simplified]
lemmas divide_less_0_1_iff = divide_less_0_iff [of 1, simplified]
lemmas zero_le_divide_1_iff = zero_le_divide_iff [of 1, simplified]
lemmas divide_le_0_1_iff = divide_le_0_iff [of 1, simplified]

declare zero_less_divide_1_iff [simp,no_atp]
declare divide_less_0_1_iff [simp,no_atp]
declare zero_le_divide_1_iff [simp,no_atp]
declare divide_le_0_1_iff [simp,no_atp]

lemma divide_right_mono:
     "[|a \<le> b; 0 \<le> c|] ==> a/c \<le> b/(c::'a::{linordered_field,division_by_zero})"
by (force simp add: divide_strict_right_mono order_le_less)

lemma divide_right_mono_neg: "(a::'a::{linordered_field,division_by_zero}) <= b 
    ==> c <= 0 ==> b / c <= a / c"
apply (drule divide_right_mono [of _ _ "- c"])
apply auto
done

lemma divide_left_mono_neg: "(a::'a::{linordered_field,division_by_zero}) <= b 
    ==> c <= 0 ==> 0 < a * b ==> c / a <= c / b"
  apply (drule divide_left_mono [of _ _ "- c"])
  apply (auto simp add: mult_commute)
done



text{*Simplify quotients that are compared with the value 1.*}

lemma le_divide_eq_1 [no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "(1 \<le> b / a) = ((0 < a & a \<le> b) | (a < 0 & b \<le> a))"
by (auto simp add: le_divide_eq)

lemma divide_le_eq_1 [no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "(b / a \<le> 1) = ((0 < a & b \<le> a) | (a < 0 & a \<le> b) | a=0)"
by (auto simp add: divide_le_eq)

lemma less_divide_eq_1 [no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "(1 < b / a) = ((0 < a & a < b) | (a < 0 & b < a))"
by (auto simp add: less_divide_eq)

lemma divide_less_eq_1 [no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "(b / a < 1) = ((0 < a & b < a) | (a < 0 & a < b) | a=0)"
by (auto simp add: divide_less_eq)


text {*Conditional Simplification Rules: No Case Splits*}

lemma le_divide_eq_1_pos [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (1 \<le> b/a) = (a \<le> b)"
by (auto simp add: le_divide_eq)

lemma le_divide_eq_1_neg [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> (1 \<le> b/a) = (b \<le> a)"
by (auto simp add: le_divide_eq)

lemma divide_le_eq_1_pos [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (b/a \<le> 1) = (b \<le> a)"
by (auto simp add: divide_le_eq)

lemma divide_le_eq_1_neg [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> (b/a \<le> 1) = (a \<le> b)"
by (auto simp add: divide_le_eq)

lemma less_divide_eq_1_pos [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (1 < b/a) = (a < b)"
by (auto simp add: less_divide_eq)

lemma less_divide_eq_1_neg [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> (1 < b/a) = (b < a)"
by (auto simp add: less_divide_eq)

lemma divide_less_eq_1_pos [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (b/a < 1) = (b < a)"
by (auto simp add: divide_less_eq)

lemma divide_less_eq_1_neg [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> b/a < 1 <-> a < b"
by (auto simp add: divide_less_eq)

lemma eq_divide_eq_1 [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "(1 = b/a) = ((a \<noteq> 0 & a = b))"
by (auto simp add: eq_divide_eq)

lemma divide_eq_eq_1 [simp,no_atp]:
  fixes a :: "'a :: {linordered_field,division_by_zero}"
  shows "(b/a = 1) = ((a \<noteq> 0 & a = b))"
by (auto simp add: divide_eq_eq)

lemma abs_inverse [simp]:
     "\<bar>inverse (a::'a::{linordered_field,division_by_zero})\<bar> = 
      inverse \<bar>a\<bar>"
apply (cases "a=0", simp) 
apply (simp add: nonzero_abs_inverse) 
done

lemma abs_divide [simp]:
     "\<bar>a / (b::'a::{linordered_field,division_by_zero})\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
apply (cases "b=0", simp) 
apply (simp add: nonzero_abs_divide) 
done

lemma abs_div_pos: "(0::'a::{linordered_field,division_by_zero}) < y ==> 
    \<bar>x\<bar> / y = \<bar>x / y\<bar>"
  apply (subst abs_divide)
  apply (simp add: order_less_imp_le)
done

lemma field_le_mult_one_interval:
  fixes x :: "'a\<Colon>{linordered_field,division_by_zero}"
  assumes *: "\<And>z. \<lbrakk> 0 < z ; z < 1 \<rbrakk> \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
proof (cases "0 < x")
  assume "0 < x"
  thus ?thesis
    using dense_le_bounded[of 0 1 "y/x"] *
    unfolding le_divide_eq if_P[OF `0 < x`] by simp
next
  assume "\<not>0 < x" hence "x \<le> 0" by simp
  obtain s::'a where s: "0 < s" "s < 1" using dense[of 0 "1\<Colon>'a"] by auto
  hence "x \<le> s * x" using mult_le_cancel_right[of 1 x s] `x \<le> 0` by auto
  also note *[OF s]
  finally show ?thesis .
qed

code_modulename SML
  Fields Arith

code_modulename OCaml
  Fields Arith

code_modulename Haskell
  Fields Arith

end
