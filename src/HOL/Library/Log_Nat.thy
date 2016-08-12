(*  Title:      HOL/Library/Log_Nat.thy
    Author:     Johannes Hölzl, Fabian Immler
    Copyright   2012  TU München
*)

section \<open>Logarithm of Natural Numbers\<close>

theory Log_Nat
imports Complex_Main
begin

definition floorlog :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"floorlog b a = (if a > 0 \<and> b > 1 then nat \<lfloor>log b a\<rfloor> + 1 else 0)"

lemma floorlog_mono: "x \<le> y \<Longrightarrow> floorlog b x \<le> floorlog b y"
by(auto simp: floorlog_def floor_mono nat_mono)

lemma floorlog_bounds:
  assumes "x > 0" "b > 1"
  shows "b ^ (floorlog b x - 1) \<le> x \<and> x < b ^ (floorlog b x)"
proof
  show "b ^ (floorlog b x - 1) \<le> x"
  proof -
    have "b ^ nat \<lfloor>log b x\<rfloor> = b powr \<lfloor>log b x\<rfloor>"
      using powr_realpow[symmetric, of b "nat \<lfloor>log b x\<rfloor>"] \<open>x > 0\<close> \<open>b > 1\<close>
      by simp
    also have "\<dots> \<le> b powr log b x" using \<open>b > 1\<close> by simp
    also have "\<dots> = real_of_int x" using \<open>0 < x\<close> \<open>b > 1\<close> by simp
    finally have "b ^ nat \<lfloor>log b x\<rfloor> \<le> real_of_int x" by simp
    then show ?thesis
      using \<open>0 < x\<close> \<open>b > 1\<close> of_nat_le_iff
      by (fastforce simp add: floorlog_def)
  qed
  show "x < b ^ (floorlog b x)"
  proof -
    have "x \<le> b powr (log b x)" using \<open>x > 0\<close> \<open>b > 1\<close> by simp
    also have "\<dots> < b powr (\<lfloor>log b x\<rfloor> + 1)"
      using assms by (intro powr_less_mono) auto
    also have "\<dots> = b ^ nat (\<lfloor>log b (real_of_int x)\<rfloor> + 1)"
      using assms by (simp add: powr_realpow[symmetric])
    finally
    have "x < b ^ nat (\<lfloor>log b (int x)\<rfloor> + 1)"
      by (rule of_nat_less_imp_less)
    then show ?thesis
      using \<open>x > 0\<close> \<open>b > 1\<close> by (simp add: floorlog_def nat_add_distrib)
  qed
qed

lemma floorlog_power[simp]:
  assumes "a > 0" "b > 1"
  shows "floorlog b (a * b ^ c) = floorlog b a + c"
proof -
  have "\<lfloor>log b a + real c\<rfloor> = \<lfloor>log b a\<rfloor> + c" by arith
  then show ?thesis using assms
    by (auto simp: floorlog_def log_mult powr_realpow[symmetric] nat_add_distrib)
qed

lemma floor_log_add_eqI:
  fixes a::nat and b::nat and r::real
  assumes "b > 1" "a \<ge> 1" "0 \<le> r" "r < 1"
  shows "\<lfloor>log b (a + r)\<rfloor> = \<lfloor>log b a\<rfloor>"
proof (rule floor_eq2)
  have "log b a \<le> log b (a + r)" using assms by force
  then show "\<lfloor>log b a\<rfloor> \<le> log b (a + r)" by arith
next
  define l::int where "l = int b ^ (nat \<lfloor>log b a\<rfloor> + 1)"
  have l_def_real: "l = b powr (\<lfloor>log b a\<rfloor> + 1)"
    using assms by (simp add: l_def powr_add powr_real_of_int)
  have "a < l"
  proof -
    have "a = b powr (log b a)" using assms by simp
    also have "\<dots> < b powr floor ((log b a) + 1)"
      using assms(1) by auto
    also have "\<dots> = l"
      using assms by (simp add: l_def powr_real_of_int powr_add)
    finally show ?thesis by simp
  qed
  then have "a + r < l" using assms by simp
  then have "log b (a + r) < log b l" using assms by simp
  also have "\<dots> = real_of_int \<lfloor>log b a\<rfloor> + 1"
    using assms by (simp add: l_def_real)
  finally show "log b (a + r) < real_of_int \<lfloor>log b a\<rfloor> + 1" .
qed

lemma divide_nat_diff_div_nat_less_one:
  fixes x b::nat shows "x / b - x div b < 1"
proof -
  have "int 0 \<noteq> \<lfloor>1::real\<rfloor>" by simp
  thus ?thesis
    by (metis add_diff_cancel_left' floor_divide_of_nat_eq less_eq_real_def
        mod_div_trivial real_of_nat_div3 real_of_nat_div_aux)
qed

lemma floor_log_div:
  fixes b x :: nat assumes "b > 1" "x > 0" "x div b > 0"
  shows "\<lfloor>log b x\<rfloor> = \<lfloor>log b (x div b)\<rfloor> + 1"
proof-
  have "\<lfloor>log b x\<rfloor> = \<lfloor>log b (x / b * b)\<rfloor>" using assms by simp
  also have "\<dots> = \<lfloor>log b (x / b) + log b b\<rfloor>"
    using assms by (subst log_mult) auto
  also have "\<dots> = \<lfloor>log b (x / b)\<rfloor> + 1" using assms by simp
  also have "\<lfloor>log b (x / b)\<rfloor> = \<lfloor>log b (x div b + (x / b - x div b))\<rfloor>" by simp
  also have "\<dots> = \<lfloor>log b (x div b)\<rfloor>"
    using assms real_of_nat_div4 divide_nat_diff_div_nat_less_one
    by (intro floor_log_add_eqI) auto
  finally show ?thesis .
qed

lemma compute_floorlog[code]:
  "floorlog b x = (if x > 0 \<and> b > 1 then floorlog b (x div b) + 1 else 0)"
by (auto simp: floorlog_def floor_log_div[of b x] div_eq_0_iff nat_add_distrib
    intro!: floor_eq2)

lemma floor_log_eq_if:
  fixes b x y :: nat
  assumes "x div b = y div b" "b > 1" "x > 0" "x div b \<ge> 1"
  shows "floor(log b x) = floor(log b y)"
proof -
  have "y > 0" using assms by(auto intro: ccontr)
  thus ?thesis using assms by (simp add: floor_log_div)
qed

lemma floorlog_eq_if:
  fixes b x y :: nat
  assumes "x div b = y div b" "b > 1" "x > 0" "x div b \<ge> 1"
  shows "floorlog b x = floorlog b y"
proof -
  have "y > 0" using assms by(auto intro: ccontr)
  thus ?thesis using assms
    by(auto simp add: floorlog_def eq_nat_nat_iff intro: floor_log_eq_if)
qed


definition bitlen :: "int \<Rightarrow> int" where "bitlen a = floorlog 2 (nat a)"

lemma bitlen_alt_def: "bitlen a = (if a > 0 then \<lfloor>log 2 a\<rfloor> + 1 else 0)"
by (simp add: bitlen_def floorlog_def)

lemma bitlen_nonneg: "0 \<le> bitlen x"
by (simp add: bitlen_def)

lemma bitlen_bounds:
  assumes "x > 0"
  shows "2 ^ nat (bitlen x - 1) \<le> x \<and> x < 2 ^ nat (bitlen x)"
proof -
  from assms have "bitlen x \<ge> 1" by (auto simp: bitlen_alt_def)
  with assms floorlog_bounds[of "nat x" 2] show ?thesis
    by (auto simp add: bitlen_def le_nat_iff nat_less_iff nat_diff_distrib)
qed

lemma bitlen_pow2[simp]:
  assumes "b > 0"
  shows "bitlen (b * 2 ^ c) = bitlen b + c"
  using assms
  by (simp add: bitlen_def nat_mult_distrib nat_power_eq)

lemma compute_bitlen[code]:
  "bitlen x = (if x > 0 then bitlen (x div 2) + 1 else 0)"
by (simp add: bitlen_def nat_div_distrib compute_floorlog)

lemma bitlen_eq_zero_iff: "bitlen x = 0 \<longleftrightarrow> x \<le> 0"
by (auto simp add: bitlen_alt_def)
   (metis compute_bitlen add.commute bitlen_alt_def bitlen_nonneg less_add_same_cancel2
      not_less zero_less_one)

lemma bitlen_div:
  assumes "0 < m"
  shows "1 \<le> real_of_int m / 2^nat (bitlen m - 1)"
    and "real_of_int m / 2^nat (bitlen m - 1) < 2"
proof -
  let ?B = "2^nat (bitlen m - 1)"

  have "?B \<le> m" using bitlen_bounds[OF \<open>0 <m\<close>] ..
  then have "1 * ?B \<le> real_of_int m"
    unfolding of_int_le_iff[symmetric] by auto
  then show "1 \<le> real_of_int m / ?B" by auto

  from assms have "m \<noteq> 0" by auto
  from assms have "0 \<le> bitlen m - 1" by (auto simp: bitlen_alt_def)

  have "m < 2^nat(bitlen m)" using bitlen_bounds[OF assms] ..
  also from assms have "\<dots> = 2^nat(bitlen m - 1 + 1)"
    by (auto simp: bitlen_def)
  also have "\<dots> = ?B * 2"
    unfolding nat_add_distrib[OF \<open>0 \<le> bitlen m - 1\<close> zero_le_one] by auto
  finally have "real_of_int m < 2 * ?B"
    by (metis (full_types) mult.commute power.simps(2) real_of_int_less_numeral_power_cancel_iff)
  then have "real_of_int m / ?B < 2 * ?B / ?B"
    by (rule divide_strict_right_mono) auto
  then show "real_of_int m / ?B < 2" by auto
qed

end
