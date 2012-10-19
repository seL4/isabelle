(*  Title       : NthRoot.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header {* Nth Roots of Real Numbers *}

theory NthRoot
imports Parity Deriv
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
      by simp
  qed
  then obtain r where r: "0 \<le> r \<and> r ^ n = a" by fast
  with n a have "r \<noteq> 0" by (auto simp add: power_0_left)
  with r have "0 < r \<and> r ^ n = a" by simp
  thus ?thesis ..
qed

(* Used by Integration/RealRandVar.thy in AFP *)
lemma realpow_pos_nth2: "(0::real) < a \<Longrightarrow> \<exists>r>0. r ^ Suc n = a"
by (blast intro: realpow_pos_nth)

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

lemma odd_real_root_pow: "odd n \<Longrightarrow> root n x ^ n = x"
apply (rule_tac x=0 and y=x in linorder_le_cases)
apply (erule (1) real_root_pow_pos2 [OF odd_pos])
apply (subgoal_tac "root n (- x) ^ n = - x")
apply (simp add: real_root_minus odd_pos)
apply (simp add: odd_pos)
done

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

lemma odd_real_root_power_cancel: "odd n \<Longrightarrow> root n (x ^ n) = x"
apply (rule_tac x=0 and y=x in linorder_le_cases)
apply (erule (1) real_root_power_cancel [OF odd_pos])
apply (subgoal_tac "root n ((- x) ^ n) = - x")
apply (simp add: real_root_minus odd_pos)
apply (erule real_root_power_cancel [OF odd_pos], simp)
done

lemma real_root_pos_unique:
  "\<lbrakk>0 < n; 0 \<le> y; y ^ n = x\<rbrakk> \<Longrightarrow> root n x = y"
by (erule subst, rule real_root_power_cancel)

lemma odd_real_root_unique:
  "\<lbrakk>odd n; y ^ n = x\<rbrakk> \<Longrightarrow> root n x = y"
by (erule subst, rule odd_real_root_power_cancel)

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

lemma real_root_gt_1_iff [simp]: "0 < n \<Longrightarrow> (1 < root n y) = (1 < y)"
by (insert real_root_less_iff [where x=1], simp)

lemma real_root_lt_1_iff [simp]: "0 < n \<Longrightarrow> (root n x < 1) = (x < 1)"
by (insert real_root_less_iff [where y=1], simp)

lemma real_root_ge_1_iff [simp]: "0 < n \<Longrightarrow> (1 \<le> root n y) = (1 \<le> y)"
by (insert real_root_le_iff [where x=1], simp)

lemma real_root_le_1_iff [simp]: "0 < n \<Longrightarrow> (root n x \<le> 1) = (x \<le> 1)"
by (insert real_root_le_iff [where y=1], simp)

lemma real_root_eq_1_iff [simp]: "0 < n \<Longrightarrow> (root n x = 1) = (x = 1)"
by (insert real_root_eq_iff [where y=1], simp)

text {* Roots of roots *}

lemma real_root_Suc_0 [simp]: "root (Suc 0) x = x"
by (simp add: odd_real_root_unique)

lemma real_root_pos_mult_exp:
  "\<lbrakk>0 < m; 0 < n; 0 < x\<rbrakk> \<Longrightarrow> root (m * n) x = root m (root n x)"
by (rule real_root_pos_unique, simp_all add: power_mult)

lemma real_root_mult_exp:
  "\<lbrakk>0 < m; 0 < n\<rbrakk> \<Longrightarrow> root (m * n) x = root m (root n x)"
apply (rule linorder_cases [where x=x and y=0])
apply (subgoal_tac "root (m * n) (- x) = root m (root n (- x))")
apply (simp add: real_root_minus)
apply (simp_all add: real_root_pos_mult_exp)
done

lemma real_root_commute:
  "\<lbrakk>0 < m; 0 < n\<rbrakk> \<Longrightarrow> root m (root n x) = root n (root m x)"
by (simp add: real_root_mult_exp [symmetric] mult_commute)

text {* Monotonicity in first argument *}

lemma real_root_strict_decreasing:
  "\<lbrakk>0 < n; n < N; 1 < x\<rbrakk> \<Longrightarrow> root N x < root n x"
apply (subgoal_tac "root n (root N x) ^ n < root N (root n x) ^ N", simp)
apply (simp add: real_root_commute power_strict_increasing
            del: real_root_pow_pos2)
done

lemma real_root_strict_increasing:
  "\<lbrakk>0 < n; n < N; 0 < x; x < 1\<rbrakk> \<Longrightarrow> root n x < root N x"
apply (subgoal_tac "root N (root n x) ^ N < root n (root N x) ^ n", simp)
apply (simp add: real_root_commute power_strict_decreasing
            del: real_root_pow_pos2)
done

lemma real_root_decreasing:
  "\<lbrakk>0 < n; n < N; 1 \<le> x\<rbrakk> \<Longrightarrow> root N x \<le> root n x"
by (auto simp add: order_le_less real_root_strict_decreasing)

lemma real_root_increasing:
  "\<lbrakk>0 < n; n < N; 0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> root n x \<le> root N x"
by (auto simp add: order_le_less real_root_strict_increasing)

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

lemma real_root_abs: "0 < n \<Longrightarrow> root n \<bar>x\<bar> = \<bar>root n x\<bar>"
by (simp add: abs_if real_root_minus)

text {* Continuity and derivatives *}

lemma isCont_root_pos:
  assumes n: "0 < n"
  assumes x: "0 < x"
  shows "isCont (root n) x"
proof -
  have "isCont (root n) (root n x ^ n)"
  proof (rule isCont_inverse_function [where f="\<lambda>a. a ^ n"])
    show "0 < root n x" using n x by simp
    show "\<forall>z. \<bar>z - root n x\<bar> \<le> root n x \<longrightarrow> root n (z ^ n) = z"
      by (simp add: abs_le_iff real_root_power_cancel n)
    show "\<forall>z. \<bar>z - root n x\<bar> \<le> root n x \<longrightarrow> isCont (\<lambda>a. a ^ n) z"
      by simp
  qed
  thus ?thesis using n x by simp
qed

lemma isCont_root_neg:
  "\<lbrakk>0 < n; x < 0\<rbrakk> \<Longrightarrow> isCont (root n) x"
apply (subgoal_tac "isCont (\<lambda>x. - root n (- x)) x")
apply (simp add: real_root_minus)
apply (rule isCont_o2 [OF isCont_minus [OF isCont_ident]])
apply (simp add: isCont_root_pos)
done

lemma isCont_root_zero:
  "0 < n \<Longrightarrow> isCont (root n) 0"
unfolding isCont_def
apply (rule LIM_I)
apply (rule_tac x="r ^ n" in exI, safe)
apply (simp)
apply (simp add: real_root_abs [symmetric])
apply (rule_tac n="n" in power_less_imp_less_base, simp_all)
done

lemma isCont_real_root: "0 < n \<Longrightarrow> isCont (root n) x"
apply (rule_tac x=x and y=0 in linorder_cases)
apply (simp_all add: isCont_root_pos isCont_root_neg isCont_root_zero)
done

lemma DERIV_real_root:
  assumes n: "0 < n"
  assumes x: "0 < x"
  shows "DERIV (root n) x :> inverse (real n * root n x ^ (n - Suc 0))"
proof (rule DERIV_inverse_function)
  show "0 < x" using x .
  show "x < x + 1" by simp
  show "\<forall>y. 0 < y \<and> y < x + 1 \<longrightarrow> root n y ^ n = y"
    using n by simp
  show "DERIV (\<lambda>x. x ^ n) (root n x) :> real n * root n x ^ (n - Suc 0)"
    by (rule DERIV_pow)
  show "real n * root n x ^ (n - Suc 0) \<noteq> 0"
    using n x by simp
  show "isCont (root n) x"
    using n by (rule isCont_real_root)
qed

lemma DERIV_odd_real_root:
  assumes n: "odd n"
  assumes x: "x \<noteq> 0"
  shows "DERIV (root n) x :> inverse (real n * root n x ^ (n - Suc 0))"
proof (rule DERIV_inverse_function)
  show "x - 1 < x" by simp
  show "x < x + 1" by simp
  show "\<forall>y. x - 1 < y \<and> y < x + 1 \<longrightarrow> root n y ^ n = y"
    using n by (simp add: odd_real_root_pow)
  show "DERIV (\<lambda>x. x ^ n) (root n x) :> real n * root n x ^ (n - Suc 0)"
    by (rule DERIV_pow)
  show "real n * root n x ^ (n - Suc 0) \<noteq> 0"
    using odd_pos [OF n] x by simp
  show "isCont (root n) x"
    using odd_pos [OF n] by (rule isCont_real_root)
qed

lemma DERIV_even_real_root:
  assumes n: "0 < n" and "even n"
  assumes x: "x < 0"
  shows "DERIV (root n) x :> inverse (- real n * root n x ^ (n - Suc 0))"
proof (rule DERIV_inverse_function)
  show "x - 1 < x" by simp
  show "x < 0" using x .
next
  show "\<forall>y. x - 1 < y \<and> y < 0 \<longrightarrow> - (root n y ^ n) = y"
  proof (rule allI, rule impI, erule conjE)
    fix y assume "x - 1 < y" and "y < 0"
    hence "root n (-y) ^ n = -y" using `0 < n` by simp
    with real_root_minus[OF `0 < n`] and `even n`
    show "- (root n y ^ n) = y" by simp
  qed
next
  show "DERIV (\<lambda>x. - (x ^ n)) (root n x) :> - real n * root n x ^ (n - Suc 0)"
    by  (auto intro!: DERIV_intros)
  show "- real n * root n x ^ (n - Suc 0) \<noteq> 0"
    using n x by simp
  show "isCont (root n) x"
    using n by (rule isCont_real_root)
qed

lemma DERIV_real_root_generic:
  assumes "0 < n" and "x \<noteq> 0"
    and "\<lbrakk> even n ; 0 < x \<rbrakk> \<Longrightarrow> D = inverse (real n * root n x ^ (n - Suc 0))"
    and "\<lbrakk> even n ; x < 0 \<rbrakk> \<Longrightarrow> D = - inverse (real n * root n x ^ (n - Suc 0))"
    and "odd n \<Longrightarrow> D = inverse (real n * root n x ^ (n - Suc 0))"
  shows "DERIV (root n) x :> D"
using assms by (cases "even n", cases "0 < x",
  auto intro: DERIV_real_root[THEN DERIV_cong]
              DERIV_odd_real_root[THEN DERIV_cong]
              DERIV_even_real_root[THEN DERIV_cong])

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

lemma isCont_real_sqrt: "isCont sqrt x"
unfolding sqrt_def by (rule isCont_real_root [OF pos2])

lemma DERIV_real_sqrt_generic:
  assumes "x \<noteq> 0"
  assumes "x > 0 \<Longrightarrow> D = inverse (sqrt x) / 2"
  assumes "x < 0 \<Longrightarrow> D = - inverse (sqrt x) / 2"
  shows "DERIV sqrt x :> D"
  using assms unfolding sqrt_def
  by (auto intro!: DERIV_real_root_generic)

lemma DERIV_real_sqrt:
  "0 < x \<Longrightarrow> DERIV sqrt x :> inverse (sqrt x) / 2"
  using DERIV_real_sqrt_generic by simp

declare
  DERIV_real_sqrt_generic[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]
  DERIV_real_root_generic[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]

lemma not_real_square_gt_zero [simp]: "(~ (0::real) < x*x) = (x = 0)"
apply auto
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (simp add: zero_less_mult_iff)
done

lemma real_sqrt_abs2 [simp]: "sqrt(x*x) = \<bar>x\<bar>"
apply (subst power2_eq_square [symmetric])
apply (rule real_sqrt_abs)
done

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

lemma lemma_real_divide_sqrt_less: "0 < u ==> u / sqrt 2 < u"
by (simp add: divide_less_eq)

lemma four_x_squared: 
  fixes x::real
  shows "4 * x\<twosuperior> = (2 * x)\<twosuperior>"
by (simp add: power2_eq_square)

subsection {* Square Root of Sum of Squares *}

lemma real_sqrt_sum_squares_ge_zero: "0 \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
  by simp (* TODO: delete *)

declare real_sqrt_sum_squares_ge_zero [THEN abs_of_nonneg, simp]

lemma real_sqrt_sum_squares_mult_ge_zero [simp]:
     "0 \<le> sqrt ((x\<twosuperior> + y\<twosuperior>)*(xa\<twosuperior> + ya\<twosuperior>))"
  by (simp add: zero_le_mult_iff)

lemma real_sqrt_sum_squares_mult_squared_eq [simp]:
     "sqrt ((x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)) ^ 2 = (x\<twosuperior> + y\<twosuperior>) * (xa\<twosuperior> + ya\<twosuperior>)"
  by (simp add: zero_le_mult_iff)

lemma real_sqrt_sum_squares_eq_cancel: "sqrt (x\<twosuperior> + y\<twosuperior>) = x \<Longrightarrow> y = 0"
by (drule_tac f = "%x. x\<twosuperior>" in arg_cong, simp)

lemma real_sqrt_sum_squares_eq_cancel2: "sqrt (x\<twosuperior> + y\<twosuperior>) = y \<Longrightarrow> x = 0"
by (drule_tac f = "%x. x\<twosuperior>" in arg_cong, simp)

lemma real_sqrt_sum_squares_ge1 [simp]: "x \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_sum_squares_ge2 [simp]: "y \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_ge_abs1 [simp]: "\<bar>x\<bar> \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_ge_abs2 [simp]: "\<bar>y\<bar> \<le> sqrt (x\<twosuperior> + y\<twosuperior>)"
by (rule power2_le_imp_le, simp_all)

lemma le_real_sqrt_sumsq [simp]: "x \<le> sqrt (x * x + y * y)"
by (simp add: power2_eq_square [symmetric])

lemma real_sqrt_sum_squares_triangle_ineq:
  "sqrt ((a + c)\<twosuperior> + (b + d)\<twosuperior>) \<le> sqrt (a\<twosuperior> + b\<twosuperior>) + sqrt (c\<twosuperior> + d\<twosuperior>)"
apply (rule power2_le_imp_le, simp)
apply (simp add: power2_sum)
apply (simp only: mult_assoc distrib_left [symmetric])
apply (rule mult_left_mono)
apply (rule power2_le_imp_le)
apply (simp add: power2_sum power_mult_distrib)
apply (simp add: ring_distribs)
apply (subgoal_tac "0 \<le> b\<twosuperior> * c\<twosuperior> + a\<twosuperior> * d\<twosuperior> - 2 * (a * c) * (b * d)", simp)
apply (rule_tac b="(a * d - b * c)\<twosuperior>" in ord_le_eq_trans)
apply (rule zero_le_power2)
apply (simp add: power2_diff power_mult_distrib)
apply (simp add: mult_nonneg_nonneg)
apply simp
apply (simp add: add_increasing)
done

lemma real_sqrt_sum_squares_less:
  "\<lbrakk>\<bar>x\<bar> < u / sqrt 2; \<bar>y\<bar> < u / sqrt 2\<rbrakk> \<Longrightarrow> sqrt (x\<twosuperior> + y\<twosuperior>) < u"
apply (rule power2_less_imp_less, simp)
apply (drule power_strict_mono [OF _ abs_ge_zero pos2])
apply (drule power_strict_mono [OF _ abs_ge_zero pos2])
apply (simp add: power_divide)
apply (drule order_le_less_trans [OF abs_ge_zero])
apply (simp add: zero_less_divide_iff)
done

text{*Needed for the infinitely close relation over the nonstandard
    complex numbers*}
lemma lemma_sqrt_hcomplex_capprox:
     "[| 0 < u; x < u/2; y < u/2; 0 \<le> x; 0 \<le> y |] ==> sqrt (x\<twosuperior> + y\<twosuperior>) < u"
apply (rule_tac y = "u/sqrt 2" in order_le_less_trans)
apply (erule_tac [2] lemma_real_divide_sqrt_less)
apply (rule power2_le_imp_le)
apply (auto simp add: zero_le_divide_iff power_divide)
apply (rule_tac t = "u\<twosuperior>" in real_sum_of_halves [THEN subst])
apply (rule add_mono)
apply (auto simp add: four_x_squared intro: power_mono)
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

end
