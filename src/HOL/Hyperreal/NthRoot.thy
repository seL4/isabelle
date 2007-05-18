(*  Title       : NthRoot.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header {* Nth Roots of Real Numbers *}

theory NthRoot
imports SEQ Parity Deriv
begin

subsection {* Existence of Nth Root *}

text {* Existence follows from the Intermediate Value Theorem *}

lemma realpow_pos_nth:
  assumes n: "0 < n"
  assumes a: "0 < a"
  shows "\<exists>r>0. r ^ n = (a::real)"
proof -
  have "\<exists>r\<ge>0. r \<le> (max 1 a) \<and> r ^ n = a"
  proof (rule IVT)
    show "0 ^ n \<le> a" using n a by (simp add: power_0_left)
    show "0 \<le> max 1 a" by simp
    from n have n1: "1 \<le> n" by simp
    have "a \<le> max 1 a ^ 1" by simp
    also have "max 1 a ^ 1 \<le> max 1 a ^ n"
      using n1 by (rule power_increasing, simp)
    finally show "a \<le> max 1 a ^ n" .
    show "\<forall>r. 0 \<le> r \<and> r \<le> max 1 a \<longrightarrow> isCont (\<lambda>x. x ^ n) r"
      by (simp add: isCont_power isCont_Id)
  qed
  then obtain r where r: "0 \<le> r \<and> r ^ n = a" by fast
  with n a have "r \<noteq> 0" by (auto simp add: power_0_left)
  with r have "0 < r \<and> r ^ n = a" by simp
  thus ?thesis ..
qed

text {* Uniqueness of nth positive root *}

lemma realpow_pos_nth_unique:
  "\<lbrakk>0 < n; 0 < a\<rbrakk> \<Longrightarrow> \<exists>!r. 0 < r \<and> r ^ n = (a::real)"
apply (auto intro!: realpow_pos_nth)
apply (rule_tac n=n in power_eq_imp_eq_base, simp_all)
done

subsection {* Nth Root *}

text {* We define roots of negative reals such that
  @{term "root n (- x) = - root n x"}. This allows
  us to omit side conditions from many theorems. *}

definition
  root :: "[nat, real] \<Rightarrow> real" where
  "root n x = (if 0 < x then (THE u. 0 < u \<and> u ^ n = x) else
               if x < 0 then - (THE u. 0 < u \<and> u ^ n = - x) else 0)"

lemma real_root_zero [simp]: "root n 0 = 0"
unfolding root_def by simp

lemma real_root_minus: "0 < n \<Longrightarrow> root n (- x) = - root n x"
unfolding root_def by simp

lemma real_root_gt_zero: "\<lbrakk>0 < n; 0 < x\<rbrakk> \<Longrightarrow> 0 < root n x"
apply (simp add: root_def)
apply (drule (1) realpow_pos_nth_unique)
apply (erule theI' [THEN conjunct1])
done

lemma real_root_pow_pos: (* TODO: rename *)
  "\<lbrakk>0 < n; 0 < x\<rbrakk> \<Longrightarrow> root n x ^ n = x"
apply (simp add: root_def)
apply (drule (1) realpow_pos_nth_unique)
apply (erule theI' [THEN conjunct2])
done

lemma real_root_pow_pos2 [simp]: (* TODO: rename *)
  "\<lbrakk>0 < n; 0 \<le> x\<rbrakk> \<Longrightarrow> root n x ^ n = x"
by (auto simp add: order_le_less real_root_pow_pos)

lemma real_root_ge_zero: "\<lbrakk>0 < n; 0 \<le> x\<rbrakk> \<Longrightarrow> 0 \<le> root n x"
by (auto simp add: order_le_less real_root_gt_zero)

lemma real_root_power_cancel: "\<lbrakk>0 < n; 0 \<le> x\<rbrakk> \<Longrightarrow> root n (x ^ n) = x"
apply (subgoal_tac "0 \<le> x ^ n")
apply (subgoal_tac "0 \<le> root n (x ^ n)")
apply (subgoal_tac "root n (x ^ n) ^ n = x ^ n")
apply (erule (3) power_eq_imp_eq_base)
apply (erule (1) real_root_pow_pos2)
apply (erule (1) real_root_ge_zero)
apply (erule zero_le_power)
done

lemma real_root_pos_unique:
  "\<lbrakk>0 < n; 0 \<le> y; y ^ n = x\<rbrakk> \<Longrightarrow> root n x = y"
by (erule subst, rule real_root_power_cancel)

lemma real_root_one [simp]: "0 < n \<Longrightarrow> root n 1 = 1"
by (simp add: real_root_pos_unique)

text {* Root function is strictly monotonic, hence injective *}

lemma real_root_less_mono_lemma:
  "\<lbrakk>0 < n; 0 \<le> x; x < y\<rbrakk> \<Longrightarrow> root n x < root n y"
apply (subgoal_tac "0 \<le> y")
apply (subgoal_tac "root n x ^ n < root n y ^ n")
apply (erule power_less_imp_less_base)
apply (erule (1) real_root_ge_zero)
apply simp
apply simp
done

lemma real_root_less_mono: "\<lbrakk>0 < n; x < y\<rbrakk> \<Longrightarrow> root n x < root n y"
apply (cases "0 \<le> x")
apply (erule (2) real_root_less_mono_lemma)
apply (cases "0 \<le> y")
apply (rule_tac y=0 in order_less_le_trans)
apply (subgoal_tac "0 < root n (- x)")
apply (simp add: real_root_minus)
apply (simp add: real_root_gt_zero)
apply (simp add: real_root_ge_zero)
apply (subgoal_tac "root n (- y) < root n (- x)")
apply (simp add: real_root_minus)
apply (simp add: real_root_less_mono_lemma)
done

lemma real_root_le_mono: "\<lbrakk>0 < n; x \<le> y\<rbrakk> \<Longrightarrow> root n x \<le> root n y"
by (auto simp add: order_le_less real_root_less_mono)

lemma real_root_less_iff [simp]:
  "0 < n \<Longrightarrow> (root n x < root n y) = (x < y)"
apply (cases "x < y")
apply (simp add: real_root_less_mono)
apply (simp add: linorder_not_less real_root_le_mono)
done

lemma real_root_le_iff [simp]:
  "0 < n \<Longrightarrow> (root n x \<le> root n y) = (x \<le> y)"
apply (cases "x \<le> y")
apply (simp add: real_root_le_mono)
apply (simp add: linorder_not_le real_root_less_mono)
done

lemma real_root_eq_iff [simp]:
  "0 < n \<Longrightarrow> (root n x = root n y) = (x = y)"
by (simp add: order_eq_iff)

lemmas real_root_gt_0_iff [simp] = real_root_less_iff [where x=0, simplified]
lemmas real_root_lt_0_iff [simp] = real_root_less_iff [where y=0, simplified]
lemmas real_root_ge_0_iff [simp] = real_root_le_iff [where x=0, simplified]
lemmas real_root_le_0_iff [simp] = real_root_le_iff [where y=0, simplified]
lemmas real_root_eq_0_iff [simp] = real_root_eq_iff [where y=0, simplified]

text {* Roots of multiplication and division *}

lemma real_root_mult_lemma:
  "\<lbrakk>0 < n; 0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> root n (x * y) = root n x * root n y"
by (simp add: real_root_pos_unique mult_nonneg_nonneg power_mult_distrib)

lemma real_root_inverse_lemma:
  "\<lbrakk>0 < n; 0 \<le> x\<rbrakk> \<Longrightarrow> root n (inverse x) = inverse (root n x)"
by (simp add: real_root_pos_unique power_inverse [symmetric])

lemma real_root_mult:
  assumes n: "0 < n"
  shows "root n (x * y) = root n x * root n y"
proof (rule linorder_le_cases, rule_tac [!] linorder_le_cases)
  assume "0 \<le> x" and "0 \<le> y"
  thus ?thesis by (rule real_root_mult_lemma [OF n])
next
  assume "0 \<le> x" and "y \<le> 0"
  hence "0 \<le> x" and "0 \<le> - y" by simp_all
  hence "root n (x * - y) = root n x * root n (- y)"
    by (rule real_root_mult_lemma [OF n])
  thus ?thesis by (simp add: real_root_minus [OF n])
next
  assume "x \<le> 0" and "0 \<le> y"
  hence "0 \<le> - x" and "0 \<le> y" by simp_all
  hence "root n (- x * y) = root n (- x) * root n y"
    by (rule real_root_mult_lemma [OF n])
  thus ?thesis by (simp add: real_root_minus [OF n])
next
  assume "x \<le> 0" and "y \<le> 0"
  hence "0 \<le> - x" and "0 \<le> - y" by simp_all
  hence "root n (- x * - y) = root n (- x) * root n (- y)"
    by (rule real_root_mult_lemma [OF n])
  thus ?thesis by (simp add: real_root_minus [OF n])
qed

lemma real_root_inverse:
  assumes n: "0 < n"
  shows "root n (inverse x) = inverse (root n x)"
proof (rule linorder_le_cases)
  assume "0 \<le> x"
  thus ?thesis by (rule real_root_inverse_lemma [OF n])
next
  assume "x \<le> 0"
  hence "0 \<le> - x" by simp
  hence "root n (inverse (- x)) = inverse (root n (- x))"
    by (rule real_root_inverse_lemma [OF n])
  thus ?thesis by (simp add: real_root_minus [OF n])
qed

lemma real_root_divide:
  "0 < n \<Longrightarrow> root n (x / y) = root n x / root n y"
by (simp add: divide_inverse real_root_mult real_root_inverse)

lemma real_root_power:
  "0 < n \<Longrightarrow> root n (x ^ k) = root n x ^ k"
by (induct k, simp_all add: real_root_mult)

subsection {* Square Root *}

definition
  sqrt :: "real \<Rightarrow> real" where
  "sqrt = root 2"

lemma pos2: "0 < (2::nat)" by simp

lemma real_sqrt_unique: "\<lbrakk>y\<twosuperior> = x; 0 \<le> y\<rbrakk> \<Longrightarrow> sqrt x = y"
unfolding sqrt_def by (rule real_root_pos_unique [OF pos2])

lemma real_sqrt_abs [simp]: "sqrt (x\<twosuperior>) = \<bar>x\<bar>"
apply (rule real_sqrt_unique)
apply (rule power2_abs)
apply (rule abs_ge_zero)
done

lemma real_sqrt_pow2 [simp]: "0 \<le> x \<Longrightarrow> (sqrt x)\<twosuperior> = x"
unfolding sqrt_def by (rule real_root_pow_pos2 [OF pos2])

lemma real_sqrt_pow2_iff [simp]: "((sqrt x)\<twosuperior> = x) = (0 \<le> x)"
apply (rule iffI)
apply (erule subst)
apply (rule zero_le_power2)
apply (erule real_sqrt_pow2)
done

lemma real_sqrt_zero [simp]: "sqrt 0 = 0"
unfolding sqrt_def by (rule real_root_zero)

lemma real_sqrt_one [simp]: "sqrt 1 = 1"
unfolding sqrt_def by (rule real_root_one [OF pos2])

lemma real_sqrt_minus: "sqrt (- x) = - sqrt x"
unfolding sqrt_def by (rule real_root_minus [OF pos2])

lemma real_sqrt_mult: "sqrt (x * y) = sqrt x * sqrt y"
unfolding sqrt_def by (rule real_root_mult [OF pos2])

lemma real_sqrt_inverse: "sqrt (inverse x) = inverse (sqrt x)"
unfolding sqrt_def by (rule real_root_inverse [OF pos2])

lemma real_sqrt_divide: "sqrt (x / y) = sqrt x / sqrt y"
unfolding sqrt_def by (rule real_root_divide [OF pos2])

lemma real_sqrt_power: "sqrt (x ^ k) = sqrt x ^ k"
unfolding sqrt_def by (rule real_root_power [OF pos2])

lemma real_sqrt_gt_zero: "0 < x \<Longrightarrow> 0 < sqrt x"
unfolding sqrt_def by (rule real_root_gt_zero [OF pos2])

lemma real_sqrt_ge_zero: "0 \<le> x \<Longrightarrow> 0 \<le> sqrt x"
unfolding sqrt_def by (rule real_root_ge_zero [OF pos2])

lemma real_sqrt_less_mono: "x < y \<Longrightarrow> sqrt x < sqrt y"
unfolding sqrt_def by (rule real_root_less_mono [OF pos2])

lemma real_sqrt_le_mono: "x \<le> y \<Longrightarrow> sqrt x \<le> sqrt y"
unfolding sqrt_def by (rule real_root_le_mono [OF pos2])

lemma real_sqrt_less_iff [simp]: "(sqrt x < sqrt y) = (x < y)"
unfolding sqrt_def by (rule real_root_less_iff [OF pos2])

lemma real_sqrt_le_iff [simp]: "(sqrt x \<le> sqrt y) = (x \<le> y)"
unfolding sqrt_def by (rule real_root_le_iff [OF pos2])

lemma real_sqrt_eq_iff [simp]: "(sqrt x = sqrt y) = (x = y)"
unfolding sqrt_def by (rule real_root_eq_iff [OF pos2])

lemmas real_sqrt_gt_0_iff [simp] = real_sqrt_less_iff [where x=0, simplified]
lemmas real_sqrt_lt_0_iff [simp] = real_sqrt_less_iff [where y=0, simplified]
lemmas real_sqrt_ge_0_iff [simp] = real_sqrt_le_iff [where x=0, simplified]
lemmas real_sqrt_le_0_iff [simp] = real_sqrt_le_iff [where y=0, simplified]
lemmas real_sqrt_eq_0_iff [simp] = real_sqrt_eq_iff [where y=0, simplified]

lemmas real_sqrt_gt_1_iff [simp] = real_sqrt_less_iff [where x=1, simplified]
lemmas real_sqrt_lt_1_iff [simp] = real_sqrt_less_iff [where y=1, simplified]
lemmas real_sqrt_ge_1_iff [simp] = real_sqrt_le_iff [where x=1, simplified]
lemmas real_sqrt_le_1_iff [simp] = real_sqrt_le_iff [where y=1, simplified]
lemmas real_sqrt_eq_1_iff [simp] = real_sqrt_eq_iff [where y=1, simplified]

lemma not_real_square_gt_zero [simp]: "(~ (0::real) < x*x) = (x = 0)"
apply auto
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (simp add: zero_less_mult_iff)
done

lemma real_sqrt_abs2 [simp]: "sqrt(x*x) = \<bar>x\<bar>"
apply (subst power2_eq_square [symmetric])
apply (rule real_sqrt_abs)
done

lemma real_sqrt_pow2_gt_zero: "0 < x ==> 0 < (sqrt x)\<twosuperior>"
by simp (* TODO: delete *)

lemma real_sqrt_not_eq_zero: "0 < x ==> sqrt x \<noteq> 0"
by simp (* TODO: delete *)

lemma real_inv_sqrt_pow2: "0 < x ==> inverse (sqrt(x)) ^ 2 = inverse x"
by (simp add: power_inverse [symmetric])

lemma real_sqrt_eq_zero_cancel: "[| 0 \<le> x; sqrt(x) = 0|] ==> x = 0"
by simp

lemma real_sqrt_ge_one: "1 \<le> x ==> 1 \<le> sqrt x"
by simp

lemma sqrt_divide_self_eq:
  assumes nneg: "0 \<le> x"
  shows "sqrt x / x = inverse (sqrt x)"
proof cases
  assume "x=0" thus ?thesis by simp
next
  assume nz: "x\<noteq>0" 
  hence pos: "0<x" using nneg by arith
  show ?thesis
  proof (rule right_inverse_eq [THEN iffD1, THEN sym]) 
    show "sqrt x / x \<noteq> 0" by (simp add: divide_inverse nneg nz) 
    show "inverse (sqrt x) / (sqrt x / x) = 1"
      by (simp add: divide_inverse mult_assoc [symmetric] 
                  power2_eq_square [symmetric] real_inv_sqrt_pow2 pos nz) 
  qed
qed

lemma real_divide_square_eq [simp]: "(((r::real) * a) / (r * r)) = a / r"
apply (simp add: divide_inverse)
apply (case_tac "r=0")
apply (auto simp add: mult_ac)
done

subsection {* Square Root of Sum of Squares *}

lemma real_sqrt_mult_self_sum_ge_zero [simp]: "0 \<le> sqrt(x*x + y*y)"
by (rule real_sqrt_ge_zero [OF sum_squares_ge_zero])

lemma real_sqrt_sum_squares_ge_zero [simp]: "0 \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
by simp

lemma real_sqrt_sum_squares_mult_ge_zero [simp]:
     "0 \<le> sqrt ((x\<twosuperior> + y\<twosuperior>)*(xa\<twosuperior> + ya\<twosuperior>))"
by (auto intro!: real_sqrt_ge_zero simp add: zero_le_mult_iff)

lemma real_sqrt_sum_squares_mult_squared_eq [simp]:
     "sqrt ((x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)) ^ 2 = (x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)"
by (auto simp add: zero_le_mult_iff)

lemma real_sqrt_sum_squares_ge1 [simp]: "x \<le> sqrt(x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_sum_squares_ge2 [simp]: "y \<le> sqrt(x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma power2_sum:
  fixes x y :: "'a::{number_ring,recpower}"
  shows "(x + y)\<twosuperior> = x\<twosuperior> + y\<twosuperior> + 2 * x * y"
by (simp add: left_distrib right_distrib power2_eq_square)

lemma power2_diff:
  fixes x y :: "'a::{number_ring,recpower}"
  shows "(x - y)\<twosuperior> = x\<twosuperior> + y\<twosuperior> - 2 * x * y"
by (simp add: left_diff_distrib right_diff_distrib power2_eq_square)

lemma real_sqrt_sum_squares_triangle_ineq:
  "sqrt ((a + c)\<twosuperior> + (b + d)\<twosuperior>) \<le> sqrt (a\<twosuperior> + b\<twosuperior>) + sqrt (c\<twosuperior> + d\<twosuperior>)"
apply (rule power2_le_imp_le, simp)
apply (simp add: power2_sum)
apply (simp only: mult_assoc right_distrib [symmetric])
apply (rule mult_left_mono)
apply (rule power2_le_imp_le)
apply (simp add: power2_sum power_mult_distrib)
apply (simp add: ring_distrib)
apply (subgoal_tac "0 \<le> b\<twosuperior> * c\<twosuperior> + a\<twosuperior> * d\<twosuperior> - 2 * (a * c) * (b * d)", simp)
apply (rule_tac b="(a * d - b * c)\<twosuperior>" in ord_le_eq_trans)
apply (rule zero_le_power2)
apply (simp add: power2_diff power_mult_distrib)
apply (simp add: mult_nonneg_nonneg)
apply simp
apply (simp add: add_increasing)
done

text "Legacy theorem names:"
lemmas real_root_pos2 = real_root_power_cancel
lemmas real_root_pos_pos = real_root_gt_zero [THEN order_less_imp_le]
lemmas real_root_pos_pos_le = real_root_ge_zero
lemmas real_sqrt_mult_distrib = real_sqrt_mult
lemmas real_sqrt_mult_distrib2 = real_sqrt_mult
lemmas real_sqrt_eq_zero_cancel_iff = real_sqrt_eq_0_iff

(* needed for CauchysMeanTheorem.het_base from AFP *)
lemma real_root_pos: "0 < x \<Longrightarrow> root (Suc n) (x ^ (Suc n)) = x"
by (rule real_root_power_cancel [OF zero_less_Suc order_less_imp_le])

(* FIXME: the stronger version of real_root_less_iff
 breaks CauchysMeanTheorem.list_gmean_gt_iff from AFP. *)

declare real_root_less_iff [simp del]
lemma real_root_less_iff_nonneg [simp]:
  "\<lbrakk>0 < n; 0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> (root n x < root n y) = (x < y)"
by (rule real_root_less_iff)

end
