(*  Title       : NthRoot.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header {* Nth Roots of Real Numbers *}

theory NthRoot
imports Parity Deriv
begin

lemma abs_sgn_eq: "abs (sgn x :: real) = (if x = 0 then 0 else 1)"
  by (simp add: sgn_real_def)

lemma inverse_sgn: "sgn (inverse a) = inverse (sgn a :: real)"
  by (simp add: sgn_real_def)

lemma power_eq_iff_eq_base: 
  fixes a b :: "_ :: linordered_semidom"
  shows "0 < n \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a ^ n = b ^ n \<longleftrightarrow> a = b"
  using power_eq_imp_eq_base[of a n b] by auto

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

lemma realpow_pos_nth_unique: "\<lbrakk>0 < n; 0 < a\<rbrakk> \<Longrightarrow> \<exists>!r. 0 < r \<and> r ^ n = (a::real)"
  by (auto intro!: realpow_pos_nth simp: power_eq_iff_eq_base)

subsection {* Nth Root *}

text {* We define roots of negative reals such that
  @{term "root n (- x) = - root n x"}. This allows
  us to omit side conditions from many theorems. *}

lemma inj_sgn_power: assumes "0 < n" shows "inj (\<lambda>y. sgn y * \<bar>y\<bar>^n :: real)" (is "inj ?f")
proof (rule injI)
  have x: "\<And>a b :: real. (0 < a \<and> b < 0) \<or> (a < 0 \<and> 0 < b) \<Longrightarrow> a \<noteq> b" by auto
  fix x y assume "?f x = ?f y" with power_eq_iff_eq_base[of n "\<bar>x\<bar>" "\<bar>y\<bar>"] `0<n` show "x = y"
    by (cases rule: linorder_cases[of 0 x, case_product linorder_cases[of 0 y]])
       (simp_all add: x)
qed

lemma sgn_power_injE: "sgn a * \<bar>a\<bar> ^ n = x \<Longrightarrow> x = sgn b * \<bar>b\<bar> ^ n \<Longrightarrow> 0 < n \<Longrightarrow> a = (b::real)"
  using inj_sgn_power[THEN injD, of n a b] by simp

definition root :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "root n x = (if n = 0 then 0 else the_inv (\<lambda>y. sgn y * \<bar>y\<bar>^n) x)"

lemma root_0 [simp]: "root 0 x = 0"
  by (simp add: root_def)

lemma root_sgn_power: "0 < n \<Longrightarrow> root n (sgn y * \<bar>y\<bar>^n) = y"
  using the_inv_f_f[OF inj_sgn_power] by (simp add: root_def)

lemma sgn_power_root:
  assumes "0 < n" shows "sgn (root n x) * \<bar>(root n x)\<bar>^n = x" (is "?f (root n x) = x")
proof cases
  assume "x \<noteq> 0"
  with realpow_pos_nth[OF `0 < n`, of "\<bar>x\<bar>"] obtain r where "0 < r" "r ^ n = \<bar>x\<bar>" by auto
  with `x \<noteq> 0` have S: "x \<in> range ?f"
    by (intro image_eqI[of _ _ "sgn x * r"])
       (auto simp: abs_mult sgn_mult power_mult_distrib abs_sgn_eq mult_sgn_abs)
  from `0 < n` f_the_inv_into_f[OF inj_sgn_power[OF `0 < n`] this]  show ?thesis
    by (simp add: root_def)
qed (insert `0 < n` root_sgn_power[of n 0], simp)

lemma split_root: "P (root n x) \<longleftrightarrow> (n = 0 \<longrightarrow> P 0) \<and> (0 < n \<longrightarrow> (\<forall>y. sgn y * \<bar>y\<bar>^n = x \<longrightarrow> P y))"
  apply (cases "n = 0")
  apply simp_all
  apply (metis root_sgn_power sgn_power_root)
  done

lemma real_root_zero [simp]: "root n 0 = 0"
  by (simp split: split_root add: sgn_zero_iff)

lemma real_root_minus: "root n (- x) = - root n x"
  by (clarsimp split: split_root elim!: sgn_power_injE simp: sgn_minus)

lemma real_root_less_mono: "\<lbrakk>0 < n; x < y\<rbrakk> \<Longrightarrow> root n x < root n y"
proof (clarsimp split: split_root)
  have x: "\<And>a b :: real. (0 < b \<and> a < 0) \<Longrightarrow> \<not> a > b" by auto
  fix a b :: real assume "0 < n" "sgn a * \<bar>a\<bar> ^ n < sgn b * \<bar>b\<bar> ^ n" then show "a < b"
    using power_less_imp_less_base[of a n b]  power_less_imp_less_base[of "-b" n "-a"]
    by (simp add: sgn_real_def power_less_zero_eq x[of "a ^ n" "- ((- b) ^ n)"] split: split_if_asm)
qed

lemma real_root_gt_zero: "\<lbrakk>0 < n; 0 < x\<rbrakk> \<Longrightarrow> 0 < root n x"
  using real_root_less_mono[of n 0 x] by simp

lemma real_root_ge_zero: "0 \<le> x \<Longrightarrow> 0 \<le> root n x"
  using real_root_gt_zero[of n x] by (cases "n = 0") (auto simp add: le_less)

lemma real_root_pow_pos: (* TODO: rename *)
  "\<lbrakk>0 < n; 0 < x\<rbrakk> \<Longrightarrow> root n x ^ n = x"
  using sgn_power_root[of n x] real_root_gt_zero[of n x] by simp

lemma real_root_pow_pos2 [simp]: (* TODO: rename *)
  "\<lbrakk>0 < n; 0 \<le> x\<rbrakk> \<Longrightarrow> root n x ^ n = x"
by (auto simp add: order_le_less real_root_pow_pos)

lemma sgn_root: "0 < n \<Longrightarrow> sgn (root n x) = sgn x"
  by (auto split: split_root simp: sgn_real_def power_less_zero_eq)

lemma odd_real_root_pow: "odd n \<Longrightarrow> root n x ^ n = x"
  using sgn_power_root[of n x] by (simp add: odd_pos sgn_real_def split: split_if_asm)

lemma real_root_power_cancel: "\<lbrakk>0 < n; 0 \<le> x\<rbrakk> \<Longrightarrow> root n (x ^ n) = x"
  using root_sgn_power[of n x] by (auto simp add: le_less power_0_left)

lemma odd_real_root_power_cancel: "odd n \<Longrightarrow> root n (x ^ n) = x"
  using root_sgn_power[of n x] by (simp add: odd_pos sgn_real_def power_0_left split: split_if_asm)

lemma real_root_pos_unique: "\<lbrakk>0 < n; 0 \<le> y; y ^ n = x\<rbrakk> \<Longrightarrow> root n x = y"
  using root_sgn_power[of n y] by (auto simp add: le_less power_0_left)

lemma odd_real_root_unique:
  "\<lbrakk>odd n; y ^ n = x\<rbrakk> \<Longrightarrow> root n x = y"
by (erule subst, rule odd_real_root_power_cancel)

lemma real_root_one [simp]: "0 < n \<Longrightarrow> root n 1 = 1"
by (simp add: real_root_pos_unique)

text {* Root function is strictly monotonic, hence injective *}

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

text {* Roots of multiplication and division *}

lemma real_root_mult: "root n (x * y) = root n x * root n y"
  by (auto split: split_root elim!: sgn_power_injE simp: sgn_mult abs_mult power_mult_distrib)

lemma real_root_inverse: "root n (inverse x) = inverse (root n x)"
  by (auto split: split_root elim!: sgn_power_injE simp: inverse_sgn power_inverse)

lemma real_root_divide: "root n (x / y) = root n x / root n y"
  by (simp add: divide_inverse real_root_mult real_root_inverse)

lemma real_root_abs: "0 < n \<Longrightarrow> root n \<bar>x\<bar> = \<bar>root n x\<bar>"
  by (simp add: abs_if real_root_minus)

lemma real_root_power: "0 < n \<Longrightarrow> root n (x ^ k) = root n x ^ k"
  by (induct k) (simp_all add: real_root_mult)

text {* Roots of roots *}

lemma real_root_Suc_0 [simp]: "root (Suc 0) x = x"
by (simp add: odd_real_root_unique)

lemma real_root_mult_exp: "root (m * n) x = root m (root n x)"
  by (auto split: split_root elim!: sgn_power_injE
           simp: sgn_zero_iff sgn_mult power_mult[symmetric] abs_mult power_mult_distrib abs_sgn_eq)

lemma real_root_commute: "root m (root n x) = root n (root m x)"
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

text {* Continuity and derivatives *}

lemma isCont_real_root: "isCont (root n) x"
proof cases
  assume n: "0 < n"
  let ?f = "\<lambda>y::real. sgn y * \<bar>y\<bar>^n"
  have "continuous_on ({0..} \<union> {.. 0}) (\<lambda>x. if 0 < x then x ^ n else - ((-x) ^ n) :: real)"
    using n by (intro continuous_on_If continuous_intros) auto
  then have "continuous_on UNIV ?f"
    by (rule continuous_on_cong[THEN iffD1, rotated 2]) (auto simp: not_less real_sgn_neg le_less n)
  then have [simp]: "\<And>x. isCont ?f x"
    by (simp add: continuous_on_eq_continuous_at)

  have "isCont (root n) (?f (root n x))"
    by (rule isCont_inverse_function [where f="?f" and d=1]) (auto simp: root_sgn_power n)
  then show ?thesis
    by (simp add: sgn_power_root n)
qed (simp add: root_def[abs_def])

lemma tendsto_real_root[tendsto_intros]:
  "(f ---> x) F \<Longrightarrow> ((\<lambda>x. root n (f x)) ---> root n x) F"
  using isCont_tendsto_compose[OF isCont_real_root, of f x F] .

lemma continuous_real_root[continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. root n (f x))"
  unfolding continuous_def by (rule tendsto_real_root)
  
lemma continuous_on_real_root[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. root n (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_real_root)

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
qed (rule isCont_real_root)

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
qed (rule isCont_real_root)

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
    with real_root_minus and `even n`
    show "- (root n y ^ n) = y" by simp
  qed
next
  show "DERIV (\<lambda>x. - (x ^ n)) (root n x) :> - real n * root n x ^ (n - Suc 0)"
    by  (auto intro!: derivative_eq_intros simp: real_of_nat_def)
  show "- real n * root n x ^ (n - Suc 0) \<noteq> 0"
    using n x by simp
qed (rule isCont_real_root)

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

definition sqrt :: "real \<Rightarrow> real" where
  "sqrt = root 2"

lemma pos2: "0 < (2::nat)" by simp

lemma real_sqrt_unique: "\<lbrakk>y\<^sup>2 = x; 0 \<le> y\<rbrakk> \<Longrightarrow> sqrt x = y"
unfolding sqrt_def by (rule real_root_pos_unique [OF pos2])

lemma real_sqrt_abs [simp]: "sqrt (x\<^sup>2) = \<bar>x\<bar>"
apply (rule real_sqrt_unique)
apply (rule power2_abs)
apply (rule abs_ge_zero)
done

lemma real_sqrt_pow2 [simp]: "0 \<le> x \<Longrightarrow> (sqrt x)\<^sup>2 = x"
unfolding sqrt_def by (rule real_root_pow_pos2 [OF pos2])

lemma real_sqrt_pow2_iff [simp]: "((sqrt x)\<^sup>2 = x) = (0 \<le> x)"
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
unfolding sqrt_def by (rule real_root_minus)

lemma real_sqrt_mult: "sqrt (x * y) = sqrt x * sqrt y"
unfolding sqrt_def by (rule real_root_mult)

lemma real_sqrt_inverse: "sqrt (inverse x) = inverse (sqrt x)"
unfolding sqrt_def by (rule real_root_inverse)

lemma real_sqrt_divide: "sqrt (x / y) = sqrt x / sqrt y"
unfolding sqrt_def by (rule real_root_divide)

lemma real_sqrt_power: "sqrt (x ^ k) = sqrt x ^ k"
unfolding sqrt_def by (rule real_root_power [OF pos2])

lemma real_sqrt_gt_zero: "0 < x \<Longrightarrow> 0 < sqrt x"
unfolding sqrt_def by (rule real_root_gt_zero [OF pos2])

lemma real_sqrt_ge_zero: "0 \<le> x \<Longrightarrow> 0 \<le> sqrt x"
unfolding sqrt_def by (rule real_root_ge_zero)

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

lemma real_le_lsqrt: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> x \<le> y\<^sup>2 \<Longrightarrow> sqrt x \<le> y"
  using real_sqrt_le_iff[of x "y\<^sup>2"] by simp

lemma real_le_rsqrt: "x\<^sup>2 \<le> y \<Longrightarrow> x \<le> sqrt y"
  using real_sqrt_le_mono[of "x\<^sup>2" y] by simp

lemma real_less_rsqrt: "x\<^sup>2 < y \<Longrightarrow> x < sqrt y"
  using real_sqrt_less_mono[of "x\<^sup>2" y] by simp

lemma sqrt_even_pow2:
  assumes n: "even n"
  shows "sqrt (2 ^ n) = 2 ^ (n div 2)"
proof -
  from n obtain m where m: "n = 2 * m"
    unfolding even_mult_two_ex ..
  from m have "sqrt (2 ^ n) = sqrt ((2 ^ m)\<^sup>2)"
    by (simp only: power_mult[symmetric] mult_commute)
  then show ?thesis
    using m by simp
qed

lemmas real_sqrt_gt_0_iff [simp] = real_sqrt_less_iff [where x=0, unfolded real_sqrt_zero]
lemmas real_sqrt_lt_0_iff [simp] = real_sqrt_less_iff [where y=0, unfolded real_sqrt_zero]
lemmas real_sqrt_ge_0_iff [simp] = real_sqrt_le_iff [where x=0, unfolded real_sqrt_zero]
lemmas real_sqrt_le_0_iff [simp] = real_sqrt_le_iff [where y=0, unfolded real_sqrt_zero]
lemmas real_sqrt_eq_0_iff [simp] = real_sqrt_eq_iff [where y=0, unfolded real_sqrt_zero]

lemmas real_sqrt_gt_1_iff [simp] = real_sqrt_less_iff [where x=1, unfolded real_sqrt_one]
lemmas real_sqrt_lt_1_iff [simp] = real_sqrt_less_iff [where y=1, unfolded real_sqrt_one]
lemmas real_sqrt_ge_1_iff [simp] = real_sqrt_le_iff [where x=1, unfolded real_sqrt_one]
lemmas real_sqrt_le_1_iff [simp] = real_sqrt_le_iff [where y=1, unfolded real_sqrt_one]
lemmas real_sqrt_eq_1_iff [simp] = real_sqrt_eq_iff [where y=1, unfolded real_sqrt_one]

lemma isCont_real_sqrt: "isCont sqrt x"
unfolding sqrt_def by (rule isCont_real_root)

lemma tendsto_real_sqrt[tendsto_intros]:
  "(f ---> x) F \<Longrightarrow> ((\<lambda>x. sqrt (f x)) ---> sqrt x) F"
  unfolding sqrt_def by (rule tendsto_real_root)

lemma continuous_real_sqrt[continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. sqrt (f x))"
  unfolding sqrt_def by (rule continuous_real_root)
  
lemma continuous_on_real_sqrt[continuous_intros]:
  "continuous_on s f \<Longrightarrow> 0 < n \<Longrightarrow> continuous_on s (\<lambda>x. sqrt (f x))"
  unfolding sqrt_def by (rule continuous_on_real_root)

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
  DERIV_real_sqrt_generic[THEN DERIV_chain2, derivative_intros]
  DERIV_real_root_generic[THEN DERIV_chain2, derivative_intros]

lemma not_real_square_gt_zero [simp]: "(~ (0::real) < x*x) = (x = 0)"
apply auto
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (simp add: zero_less_mult_iff)
done

lemma real_sqrt_abs2 [simp]: "sqrt(x*x) = \<bar>x\<bar>"
apply (subst power2_eq_square [symmetric])
apply (rule real_sqrt_abs)
done

lemma real_inv_sqrt_pow2: "0 < x ==> (inverse (sqrt x))\<^sup>2 = inverse x"
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

lemma real_div_sqrt: "0 \<le> x \<Longrightarrow> x / sqrt x = sqrt x"
  apply (cases "x = 0")
  apply simp_all
  using sqrt_divide_self_eq[of x]
  apply (simp add: inverse_eq_divide field_simps)
  done

lemma real_divide_square_eq [simp]: "(((r::real) * a) / (r * r)) = a / r"
apply (simp add: divide_inverse)
apply (case_tac "r=0")
apply (auto simp add: mult_ac)
done

lemma lemma_real_divide_sqrt_less: "0 < u ==> u / sqrt 2 < u"
by (simp add: divide_less_eq)

lemma four_x_squared: 
  fixes x::real
  shows "4 * x\<^sup>2 = (2 * x)\<^sup>2"
by (simp add: power2_eq_square)

subsection {* Square Root of Sum of Squares *}

lemma sum_squares_bound: 
  fixes x:: "'a::linordered_field"
  shows "2*x*y \<le> x^2 + y^2"
proof -
  have "(x-y)^2 = x*x - 2*x*y + y*y"
    by algebra
  then have "0 \<le> x^2 - 2*x*y + y^2"
    by (metis sum_power2_ge_zero zero_le_double_add_iff_zero_le_single_add power2_eq_square)
  then show ?thesis
    by arith
qed

lemma arith_geo_mean: 
  fixes u:: "'a::linordered_field" assumes "u\<^sup>2 = x*y" "x\<ge>0" "y\<ge>0" shows "u \<le> (x + y)/2"
    apply (rule power2_le_imp_le)
    using sum_squares_bound assms
    apply (auto simp: zero_le_mult_iff)
    by (auto simp: algebra_simps power2_eq_square)

lemma arith_geo_mean_sqrt: 
  fixes x::real assumes "x\<ge>0" "y\<ge>0" shows "sqrt(x*y) \<le> (x + y)/2"
  apply (rule arith_geo_mean)
  using assms
  apply (auto simp: zero_le_mult_iff)
  done

lemma real_sqrt_sum_squares_mult_ge_zero [simp]:
     "0 \<le> sqrt ((x\<^sup>2 + y\<^sup>2)*(xa\<^sup>2 + ya\<^sup>2))"
  by (metis real_sqrt_ge_0_iff split_mult_pos_le sum_power2_ge_zero)

lemma real_sqrt_sum_squares_mult_squared_eq [simp]:
     "(sqrt ((x\<^sup>2 + y\<^sup>2) * (xa\<^sup>2 + ya\<^sup>2)))\<^sup>2 = (x\<^sup>2 + y\<^sup>2) * (xa\<^sup>2 + ya\<^sup>2)"
  by (simp add: zero_le_mult_iff)

lemma real_sqrt_sum_squares_eq_cancel: "sqrt (x\<^sup>2 + y\<^sup>2) = x \<Longrightarrow> y = 0"
by (drule_tac f = "%x. x\<^sup>2" in arg_cong, simp)

lemma real_sqrt_sum_squares_eq_cancel2: "sqrt (x\<^sup>2 + y\<^sup>2) = y \<Longrightarrow> x = 0"
by (drule_tac f = "%x. x\<^sup>2" in arg_cong, simp)

lemma real_sqrt_sum_squares_ge1 [simp]: "x \<le> sqrt (x\<^sup>2 + y\<^sup>2)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_sum_squares_ge2 [simp]: "y \<le> sqrt (x\<^sup>2 + y\<^sup>2)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_ge_abs1 [simp]: "\<bar>x\<bar> \<le> sqrt (x\<^sup>2 + y\<^sup>2)"
by (rule power2_le_imp_le, simp_all)

lemma real_sqrt_ge_abs2 [simp]: "\<bar>y\<bar> \<le> sqrt (x\<^sup>2 + y\<^sup>2)"
by (rule power2_le_imp_le, simp_all)

lemma le_real_sqrt_sumsq [simp]: "x \<le> sqrt (x * x + y * y)"
by (simp add: power2_eq_square [symmetric])

lemma real_sqrt_sum_squares_triangle_ineq:
  "sqrt ((a + c)\<^sup>2 + (b + d)\<^sup>2) \<le> sqrt (a\<^sup>2 + b\<^sup>2) + sqrt (c\<^sup>2 + d\<^sup>2)"
apply (rule power2_le_imp_le, simp)
apply (simp add: power2_sum)
apply (simp only: mult_assoc distrib_left [symmetric])
apply (rule mult_left_mono)
apply (rule power2_le_imp_le)
apply (simp add: power2_sum power_mult_distrib)
apply (simp add: ring_distribs)
apply (subgoal_tac "0 \<le> b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * d\<^sup>2 - 2 * (a * c) * (b * d)", simp)
apply (rule_tac b="(a * d - b * c)\<^sup>2" in ord_le_eq_trans)
apply (rule zero_le_power2)
apply (simp add: power2_diff power_mult_distrib)
apply (simp)
apply simp
apply (simp add: add_increasing)
done

lemma real_sqrt_sum_squares_less:
  "\<lbrakk>\<bar>x\<bar> < u / sqrt 2; \<bar>y\<bar> < u / sqrt 2\<rbrakk> \<Longrightarrow> sqrt (x\<^sup>2 + y\<^sup>2) < u"
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
     "[| 0 < u; x < u/2; y < u/2; 0 \<le> x; 0 \<le> y |] ==> sqrt (x\<^sup>2 + y\<^sup>2) < u"
apply (rule_tac y = "u/sqrt 2" in order_le_less_trans)
apply (erule_tac [2] lemma_real_divide_sqrt_less)
apply (rule power2_le_imp_le)
apply (auto simp add: zero_le_divide_iff power_divide)
apply (rule_tac t = "u\<^sup>2" in real_sum_of_halves [THEN subst])
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
