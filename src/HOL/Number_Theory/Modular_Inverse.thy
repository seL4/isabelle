section \<open>Modular Inverses\<close>
theory Modular_Inverse
  imports Cong "HOL-Library.FuncSet"
begin

text \<open>
  The following returns the unique number $m$ such that $mn \equiv 1\pmod{p}$ if there is one,
  i.e.\ if $n$ and $p$ are coprime, and otherwise $0$ by convention.
\<close>
definition modular_inverse where
  "modular_inverse p n = (if coprime p n then fst (bezout_coefficients n p) mod p else 0)"

lemma cong_modular_inverse1:
  assumes "coprime n p"
  shows   "[n * modular_inverse p n = 1] (mod p)"
proof -
  have "[fst (bezout_coefficients n p) * n + snd (bezout_coefficients n p) * p =
         modular_inverse p n * n + 0] (mod p)"
    unfolding modular_inverse_def using assms
    by (intro cong_add cong_mult) (auto simp: Cong.cong_def coprime_commute)
  also have "fst (bezout_coefficients n p) * n + snd (bezout_coefficients n p) * p = gcd n p"
    by (simp add: bezout_coefficients_fst_snd)
  also have "\<dots> = 1"
    using assms by simp
  finally show ?thesis
    by (simp add: cong_sym mult_ac)
qed

lemma cong_modular_inverse2:
  assumes "coprime n p"
  shows   "[modular_inverse p n * n = 1] (mod p)"
  using cong_modular_inverse1[OF assms] by (simp add: mult.commute)

lemma coprime_modular_inverse [simp, intro]:
  fixes n :: "'a :: {euclidean_ring_gcd,unique_euclidean_semiring}"
  assumes "coprime n p"
  shows   "coprime (modular_inverse p n) p"
  using cong_modular_inverse1[OF assms] assms
  by (meson cong_imp_coprime cong_sym coprime_1_left coprime_mult_left_iff)

lemma modular_inverse_int_nonneg: "p > 0 \<Longrightarrow> modular_inverse p (n :: int) \<ge> 0"
  by (simp add: modular_inverse_def)

lemma modular_inverse_int_less: "p > 0 \<Longrightarrow> modular_inverse p (n :: int) < p"
  by (simp add: modular_inverse_def)

lemma modular_inverse_int_eqI:
  fixes x y :: int
  assumes "y \<in> {0..<m}" "[x * y = 1] (mod m)"
  shows   "modular_inverse m x = y"
proof -
  from assms have "coprime x m"
    using cong_gcd_eq by force
  have "[modular_inverse m x * 1 = modular_inverse m x * (x * y)] (mod m)"
    by (rule cong_sym, intro cong_mult assms cong_refl)
  also have "modular_inverse m x * (x * y) = (modular_inverse m x * x) * y"
    by (simp add: mult_ac)
  also have "[\<dots> = 1 * y] (mod m)"
    using \<open>coprime x m\<close> by (intro cong_mult cong_refl cong_modular_inverse2)
  finally have "[modular_inverse m x = y] (mod m)"
    by simp
  thus "modular_inverse m x = y"
    using assms by (simp add: Cong.cong_def modular_inverse_def)
qed

lemma modular_inverse_1 [simp]:
  assumes "m > (1 :: int)"
  shows   "modular_inverse m 1 = 1"
  by (rule modular_inverse_int_eqI) (use assms in auto)

lemma modular_inverse_int_mult:
  fixes x y :: int
  assumes "coprime x m" "coprime y m" "m > 0"
  shows "modular_inverse m (x * y) = (modular_inverse m y * modular_inverse m x) mod m"
proof (rule modular_inverse_int_eqI)
  show "modular_inverse m y * modular_inverse m x mod m \<in> {0..<m}"
    using assms by auto
next
  have "[x * y * (modular_inverse m y * modular_inverse m x mod m) =
         x * y * (modular_inverse m y * modular_inverse m x)] (mod m)"
    by (intro cong_mult cong_refl) auto
  also have "x * y * (modular_inverse m y * modular_inverse m x) =
             (x * modular_inverse m x) * (y * modular_inverse m y)"
    by (simp add: mult_ac)
  also have "[\<dots> = 1 * 1] (mod m)"
    by (intro cong_mult cong_modular_inverse1 assms)
  finally show "[x * y * (modular_inverse m y * modular_inverse m x mod m) = 1] (mod m)"
    by simp
qed

lemma bij_betw_int_remainders_mult:
  fixes a n :: int
  assumes a: "coprime a n"
  shows   "bij_betw (\<lambda>m. a * m mod n) {1..<n} {1..<n}"
proof -
  define a' where "a' = modular_inverse n a"

  have *: "a' * (a * m mod n) mod n = m \<and> a * m mod n \<in> {1..<n}"
    if a: "[a * a' = 1] (mod n)" and m: "m \<in> {1..<n}" for m a a' :: int
  proof
    have "[a' * (a * m mod n) = a' * (a * m)] (mod n)"
      by (intro cong_mult cong_refl) (auto simp: Cong.cong_def)
    also have "a' * (a * m) = (a * a') * m"
      by (simp add: mult_ac)
    also have "[(a * a') * m = 1 * m] (mod n)"
      unfolding a'_def by (intro cong_mult cong_refl) (use a in auto)
    finally show "a' * (a * m mod n) mod n = m"
      using m by (simp add: Cong.cong_def)
  next
    have "coprime a n"
      using a coprime_iff_invertible_int by auto
    hence "\<not>n dvd (a * m)"
      using m by (simp add: coprime_commute coprime_dvd_mult_right_iff zdvd_not_zless)
    hence "a * m mod n > 0"
      using m order_le_less by fastforce
    thus "a * m mod n \<in> {1..<n}"
      using m by auto
  qed

  have "[a * a' = 1] (mod n)" "[a' * a = 1] (mod n)"
    unfolding a'_def by (rule cong_modular_inverse1 cong_modular_inverse2; fact)+
  from this[THEN *] show ?thesis
    by (intro bij_betwI[of _ _ _ "\<lambda>m. a' * m mod n"]) auto
qed

lemma mult_modular_inverse_of_not_coprime [simp]: "\<not>coprime a m \<Longrightarrow> modular_inverse m a = 0"
  by (simp add: coprime_commute modular_inverse_def)

lemma mult_modular_inverse_eq_0_iff:
  fixes a :: "'a :: {unique_euclidean_semiring, euclidean_ring_gcd}"
  shows "\<not>is_unit m \<Longrightarrow> modular_inverse m a = 0 \<longleftrightarrow> \<not>coprime a m"
  by (metis coprime_modular_inverse mult_modular_inverse_of_not_coprime coprime_0_left_iff)

lemma mult_modular_inverse_int_pos: "m > 1 \<Longrightarrow> coprime a m \<Longrightarrow> modular_inverse m a > (0 :: int)"
  by (simp add: modular_inverse_int_nonneg mult_modular_inverse_eq_0_iff order.strict_iff_order)

lemma abs_mult_modular_inverse_int_less: "m \<noteq> 0 \<Longrightarrow> \<bar>modular_inverse m a :: int\<bar> < \<bar>m\<bar>"
  by (auto simp: modular_inverse_def intro!: abs_mod_less)

lemma modular_inverse_int_less': "m \<noteq> 0 \<Longrightarrow> (modular_inverse m a :: int) < \<bar>m\<bar>"
  using abs_mult_modular_inverse_int_less[of m a] by linarith

end