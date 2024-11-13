(*  Title:      HOL/Library/Log_Nat.thy
    Author:     Johannes Hölzl, Fabian Immler, Manuel Eberl
    Copyright   2012  TU München
*)

section \<open>Logarithm of Natural Numbers\<close>

theory Log_Nat
imports Complex_Main
begin

subsection \<open>Preliminaries\<close>

lemma divide_nat_diff_div_nat_less_one:
  "real x / real b - real (x div b) < 1" for x b :: nat
proof (cases "b = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  then have "real (x div b) + real (x mod b) / real b - real (x div b) < 1"
    by (simp add: field_simps)
  then show ?thesis
    by (metis of_nat_of_nat_div_aux)
qed


subsection \<open>Floorlog\<close>

definition floorlog :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "floorlog b a = (if a > 0 \<and> b > 1 then nat \<lfloor>log b a\<rfloor> + 1 else 0)"

lemma floorlog_mono: "x \<le> y \<Longrightarrow> floorlog b x \<le> floorlog b y"
  by (auto simp: floorlog_def floor_mono nat_mono)

lemma floorlog_bounds:
  "b ^ (floorlog b x - 1) \<le> x \<and> x < b ^ (floorlog b x)" if "x > 0" "b > 1"
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
      using that by (intro powr_less_mono) auto
    also have "\<dots> = b ^ nat (\<lfloor>log b (real_of_int x)\<rfloor> + 1)"
      using that by (simp flip: powr_realpow)
    finally
    have "x < b ^ nat (\<lfloor>log b (int x)\<rfloor> + 1)"
      by (rule of_nat_less_imp_less)
    then show ?thesis
      using \<open>x > 0\<close> \<open>b > 1\<close> by (simp add: floorlog_def nat_add_distrib)
  qed
qed

lemma floorlog_power [simp]:
  "floorlog b (a * b ^ c) = floorlog b a + c" if "a > 0" "b > 1"
proof -
  have "\<lfloor>log b a + real c\<rfloor> = \<lfloor>log b a\<rfloor> + c" by arith
  then show ?thesis using that
    by (auto simp: floorlog_def log_mult powr_realpow[symmetric] nat_add_distrib)
qed

lemma floor_log_add_eqI:
  "\<lfloor>log b (a + r)\<rfloor> = \<lfloor>log b a\<rfloor>" if "b > 1" "a \<ge> 1" "0 \<le> r" "r < 1"
    for a b :: nat and r :: real
proof (rule floor_eq2)
  have "log b a \<le> log b (a + r)" using that by force
  then show "\<lfloor>log b a\<rfloor> \<le> log b (a + r)" by arith
next
  define l::int where "l = int b ^ (nat \<lfloor>log b a\<rfloor> + 1)"
  have l_def_real: "l = b powr (\<lfloor>log b a\<rfloor> + 1)"
    using that by (simp add: l_def powr_add powr_real_of_int)
  have "a < l"
  proof -
    have "a = b powr (log b a)" using that by simp
    also have "\<dots> < b powr floor ((log b a) + 1)"
      using that(1) by auto
    also have "\<dots> = l"
      using that by (simp add: l_def powr_real_of_int powr_add)
    finally show ?thesis by simp
  qed
  then have "a + r < l" using that by simp
  then have "log b (a + r) < log b l" using that by simp
  also have "\<dots> = real_of_int \<lfloor>log b a\<rfloor> + 1"
    using that by (simp add: l_def_real)
  finally show "log b (a + r) < real_of_int \<lfloor>log b a\<rfloor> + 1" .
qed

lemma floor_log_div:
  "\<lfloor>log b x\<rfloor> = \<lfloor>log b (x div b)\<rfloor> + 1" if "b > 1" "x > 0" "x div b > 0"
    for b x :: nat
proof-
  have "\<lfloor>log b x\<rfloor> = \<lfloor>log b (x / b * b)\<rfloor>" using that by simp
  also have "\<dots> = \<lfloor>log b (x / b) + log b b\<rfloor>"
    using that by (subst log_mult) auto
  also have "\<dots> = \<lfloor>log b (x / b)\<rfloor> + 1" using that by simp
  also have "\<lfloor>log b (x / b)\<rfloor> = \<lfloor>log b (x div b + (x / b - x div b))\<rfloor>" by simp
  also have "\<dots> = \<lfloor>log b (x div b)\<rfloor>"
    using that of_nat_div_le_of_nat divide_nat_diff_div_nat_less_one
    by (intro floor_log_add_eqI) auto
  finally show ?thesis .
qed

lemma compute_floorlog [code]:
  "floorlog b x = (if x > 0 \<and> b > 1 then floorlog b (x div b) + 1 else 0)"
  by (auto simp: floorlog_def floor_log_div[of b x] div_eq_0_iff nat_add_distrib
    intro!: floor_eq2)

lemma floor_log_eq_if:
  "\<lfloor>log b x\<rfloor> = \<lfloor>log b y\<rfloor>" if "x div b = y div b" "b > 1" "x > 0" "x div b \<ge> 1"
    for b x y :: nat
proof -
  have "y > 0" using that by (auto intro: ccontr)
  thus ?thesis using that by (simp add: floor_log_div)
qed

lemma floorlog_eq_if:
  "floorlog b x = floorlog b y" if "x div b = y div b" "b > 1" "x > 0" "x div b \<ge> 1"
    for b x y :: nat
proof -
  have "y > 0" using that by (auto intro: ccontr)
  then show ?thesis using that
    by (auto simp add: floorlog_def eq_nat_nat_iff intro: floor_log_eq_if)
qed

lemma floorlog_leD:
  "floorlog b x \<le> w \<Longrightarrow> b > 1 \<Longrightarrow> x < b ^ w"
  by (metis floorlog_bounds leD linorder_neqE_nat order.strict_trans power_strict_increasing_iff
      zero_less_one zero_less_power)

lemma floorlog_leI:
  "x < b ^ w \<Longrightarrow> 0 \<le> w \<Longrightarrow> b > 1 \<Longrightarrow> floorlog b x \<le> w"
  by (drule less_imp_of_nat_less[where 'a=real])
    (auto simp: floorlog_def Suc_le_eq nat_less_iff floor_less_iff log_of_power_less)

lemma floorlog_eq_zero_iff:
  "floorlog b x = 0 \<longleftrightarrow> b \<le> 1 \<or> x \<le> 0"
  by (auto simp: floorlog_def)

lemma floorlog_le_iff:
  "floorlog b x \<le> w \<longleftrightarrow> b \<le> 1 \<or> b > 1 \<and> 0 \<le> w \<and> x < b ^ w"
  using floorlog_leD[of b x w] floorlog_leI[of x b w]
  by (auto simp: floorlog_eq_zero_iff[THEN iffD2])

lemma floorlog_ge_SucI:
  "Suc w \<le> floorlog b x" if "b ^ w \<le> x" "b > 1"
  using that le_log_of_power[of b w x] power_not_zero
  by (force simp: floorlog_def Suc_le_eq powr_realpow not_less Suc_nat_eq_nat_zadd1
      zless_nat_eq_int_zless int_add_floor less_floor_iff
      simp del: floor_add2)

lemma floorlog_geI:
  "w \<le> floorlog b x" if "b ^ (w - 1) \<le> x" "b > 1"
  using floorlog_ge_SucI[of b "w - 1" x] that
  by auto

lemma floorlog_geD:
  "b ^ (w - 1) \<le> x" if "w \<le> floorlog b x" "w > 0"
proof -
  have "b > 1" "0 < x"
    using that by (auto simp: floorlog_def split: if_splits)
  have "b ^ (w - 1) \<le> x" if "b ^ w \<le> x"
  proof -
    have "b ^ (w - 1) \<le> b ^ w"
      using \<open>b > 1\<close>
      by (auto intro!: power_increasing)
    also note that
    finally show ?thesis .
  qed
  moreover have "b ^ nat \<lfloor>log (real b) (real x)\<rfloor> \<le> x" (is "?l \<le> _")
  proof -
    have "0 \<le> log (real b) (real x)"
      using \<open>b > 1\<close> \<open>0 < x\<close>
      by auto
    then have "?l \<le> b powr log (real b) (real x)"
      using \<open>b > 1\<close>
      by (auto simp flip: powr_realpow intro!: powr_mono of_nat_floor)
    also have "\<dots> = x" using \<open>b > 1\<close> \<open>0 < x\<close>
      by auto
    finally show ?thesis
      unfolding of_nat_le_iff .
  qed
  ultimately show ?thesis
    using that
    by (auto simp: floorlog_def le_nat_iff le_floor_iff le_log_iff powr_realpow
        split: if_splits elim!: le_SucE)
qed


subsection \<open>\<close>


definition ceillog2 :: "nat \<Rightarrow> nat" where
  "ceillog2 n = (if n = 0 then 0 else nat \<lceil>log 2 (real n)\<rceil>)"

lemma ceillog2_0 [simp]: "ceillog2 0 = 0"
  and ceillog2_Suc_0 [simp]: "ceillog2 (Suc 0) = 0"
  and ceillog2_2 [simp]: "ceillog2 2 = 1"
  by (auto simp: ceillog2_def)

lemma ceillog2_le1_eq_0 [simp]: "n \<le> 1 \<Longrightarrow> ceillog2 n = 0"
  by (cases n) auto

lemma ceillog2_2_power [simp]: "ceillog2 (2 ^ n) = n"
  by (auto simp: ceillog2_def)

lemma ceillog2_ge_log:
  assumes "n > 0"
  shows   "real (ceillog2 n) \<ge> log 2 (real n)"
proof -
  have "real_of_int \<lceil>log 2 (real n)\<rceil> \<ge> log 2 (real n)"
    by linarith
  thus ?thesis
    using assms unfolding ceillog2_def by auto
qed

lemma ceillog2_less_log:
  assumes "n > 0"
  shows   "real (ceillog2 n) < log 2 (real n) + 1"
proof -
  have "real_of_int \<lceil>log 2 (real n)\<rceil> < log 2 (real n) + 1"
    by linarith
  thus ?thesis
    using assms unfolding ceillog2_def by auto
qed

lemma ceillog2_le_iff:
  assumes "n > 0"
  shows   "ceillog2 n \<le> l \<longleftrightarrow> n \<le> 2 ^ l"
proof -
  have "ceillog2 n \<le> l \<longleftrightarrow> real n \<le> 2 ^ l"
    unfolding ceillog2_def using assms by (auto simp: log_le_iff powr_realpow)
  also have "2 ^ l = real (2 ^ l)"
    by simp
  also have "real n \<le> real (2 ^ l) \<longleftrightarrow> n \<le> 2 ^ l"
    by linarith
  finally show ?thesis .
qed

lemma ceillog2_ge_iff:
  assumes "n > 0"
  shows   "ceillog2 n \<ge> l \<longleftrightarrow> 2 ^ l < 2 * n"
proof -
  have "-1 < (0 :: real)"
    by auto
  also have "\<dots> \<le> log 2 (real n)"
    using assms by auto
  finally have "ceillog2 n \<ge> l \<longleftrightarrow> real l - 1 < log 2 (real n)"
    unfolding ceillog2_def using assms by (auto simp: le_nat_iff le_ceiling_iff)
  also have "\<dots> \<longleftrightarrow> real l < log 2 (real (2 * n))"
    using assms by (auto simp: log_mult)
  also have "\<dots> \<longleftrightarrow> 2 ^ l < real (2 * n)"
    using assms by (subst less_log_iff) (auto simp: powr_realpow)
  also have "2 ^ l = real (2 ^ l)"
    by simp
  also have "real (2 ^ l) < real (2 * n) \<longleftrightarrow> 2 ^ l < 2 * n"
    by linarith
  finally show ?thesis .
qed

lemma le_two_power_ceillog2: "n \<le> 2 ^ ceillog2 n"
  using neq0_conv ceillog2_le_iff by blast

lemma two_power_ceillog2_gt:
  assumes "n > 0"
  shows   "2 * n > 2 ^ ceillog2 n"
  using ceillog2_ge_iff[of n "ceillog2 n"] assms by simp

lemma ceillog2_eqI:
  assumes "n \<le> 2 ^ l" "2 ^ l < 2 * n"
  shows   "ceillog2 n = l"
  by (metis Suc_leI assms bot_nat_0.not_eq_extremum ceillog2_ge_iff ceillog2_le_iff le_antisym mult_is_0
      not_less_eq_eq)

lemma ceillog2_rec_even:
  assumes "k > 0"
  shows   "ceillog2 (2 * k) = Suc (ceillog2 k)"
  by (rule ceillog2_eqI) (auto simp: le_two_power_ceillog2 two_power_ceillog2_gt assms)

lemma ceillog2_mono:
  assumes "m \<le> n"
  shows   "ceillog2 m \<le> ceillog2 n"
proof (cases "m = 0")
  case False
  have "\<lceil>log 2 (real m)\<rceil> \<le> \<lceil>log 2 (real n)\<rceil>"
    by (intro ceiling_mono) (use False assms in auto)
  hence "nat \<lceil>log 2 (real m)\<rceil> \<le> nat \<lceil>log 2 (real n)\<rceil>"
    by linarith
  thus ?thesis using False assms
    unfolding ceillog2_def by simp
qed auto
  
lemma ceillog2_rec_odd:
  assumes "k > 0"
  shows   "ceillog2 (Suc (2 * k)) = Suc (ceillog2 (Suc k))"
proof -
  have "2 ^ ceillog2 (Suc (2 * k)) > Suc (2 * k)"
    by (metis assms diff_Suc_1 dvd_triv_left le_two_power_ceillog2 mult_pos_pos nat_power_eq_Suc_0_iff 
        order_less_le pos2 semiring_parity_class.even_mask_iff)
  then have "ceillog2 (2 * k + 2) \<le> ceillog2 (2 * k + 1)"
    by (simp add: ceillog2_le_iff)
  moreover have "ceillog2 (2 * k + 2) \<ge> ceillog2 (2 * k + 1)"
    by (rule ceillog2_mono) auto
  ultimately have "ceillog2 (2 * k + 2) = ceillog2 (2 * k + 1)"
    by (rule antisym)
  also have "2 * k + 2 = 2 * Suc k"
    by simp
  also have "ceillog2 (2 * Suc k) = Suc (ceillog2 (Suc k))"
    by (rule ceillog2_rec_even) auto
  finally show ?thesis 
    by simp
qed  

(* TODO: better code is possible using bitlen and "count trailing 0 bits" *)
lemma ceillog2_rec:
  "ceillog2 n = (if n \<le> 1 then 0 else 1 + ceillog2 ((n + 1) div 2))"
proof (cases "n \<le> 1")
  case True
  thus ?thesis
    by (cases n) auto
next
  case False
  thus ?thesis
    by (cases "even n") (auto elim!: evenE oddE simp: ceillog2_rec_even ceillog2_rec_odd)
qed

lemma funpow_div2_ceillog2_le_1:
  "((\<lambda>n. (n + 1) div 2) ^^ ceillog2 n) n \<le> 1"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n \<le> 1")
    case True
    thus ?thesis by (cases n) auto
  next
    case False
    have "((\<lambda>n. (n + 1) div 2) ^^ Suc (ceillog2 ((n + 1) div 2))) n \<le> 1"
      using less.IH[of "(n+1) div 2"] False by (subst funpow_Suc_right) auto
    also have "Suc (ceillog2 ((n + 1) div 2)) = ceillog2 n"
      using False by (subst ceillog2_rec[of n]) auto
    finally show ?thesis .
  qed
qed


fun ceillog2_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "ceillog2_aux acc n = (if n \<le> 1 then acc else ceillog2_aux (acc + 1) ((n + 1) div 2))"

lemmas [simp del] = ceillog2_aux.simps

lemma ceillog2_aux_correct: "ceillog2_aux acc n = ceillog2 n + acc"
proof (induction acc n rule: ceillog2_aux.induct)
  case (1 acc n)
  show ?case
  proof (cases "n \<le> 1")
    case False
    thus ?thesis using ceillog2_rec[of n] "1.IH"
      by (auto simp: ceillog2_aux.simps[of acc n])
  qed (auto simp: ceillog2_aux.simps[of acc n])
qed

(* TODO: better code equation using bit operations *)
lemma ceillog2_code [code]: "ceillog2 n = ceillog2_aux 0 n"
  by (simp add: ceillog2_aux_correct)


subsection \<open>Bitlen\<close>

definition bitlen :: "int \<Rightarrow> int"
  where "bitlen a = floorlog 2 (nat a)"

lemma bitlen_alt_def:
  "bitlen a = (if a > 0 then \<lfloor>log 2 a\<rfloor> + 1 else 0)"
  by (simp add: bitlen_def floorlog_def)

lemma bitlen_zero [simp]:
  "bitlen 0 = 0"
  by (auto simp: bitlen_def floorlog_def)

lemma bitlen_nonneg:
  "0 \<le> bitlen x"
  by (simp add: bitlen_def)

lemma bitlen_bounds:
  "2 ^ nat (bitlen x - 1) \<le> x \<and> x < 2 ^ nat (bitlen x)" if "x > 0"
proof -
  from that have "bitlen x \<ge> 1" by (auto simp: bitlen_alt_def)
  with that floorlog_bounds[of "nat x" 2] show ?thesis
    by (auto simp add: bitlen_def le_nat_iff nat_less_iff nat_diff_distrib)
qed

lemma bitlen_pow2 [simp]:
  "bitlen (b * 2 ^ c) = bitlen b + c" if "b > 0"
  using that by (simp add: bitlen_def nat_mult_distrib nat_power_eq)

lemma compute_bitlen [code]:
  "bitlen x = (if x > 0 then bitlen (x div 2) + 1 else 0)"
  by (simp add: bitlen_def nat_div_distrib compute_floorlog)

lemma bitlen_eq_zero_iff:
  "bitlen x = 0 \<longleftrightarrow> x \<le> 0"
  by (auto simp add: bitlen_alt_def)
   (metis compute_bitlen add.commute bitlen_alt_def bitlen_nonneg less_add_same_cancel2
      not_less zero_less_one)

lemma bitlen_div:
  "1 \<le> real_of_int m / 2^nat (bitlen m - 1)"
    and "real_of_int m / 2^nat (bitlen m - 1) < 2" if "0 < m"
proof -
  let ?B = "2^nat (bitlen m - 1)"

  have "?B \<le> m" using bitlen_bounds[OF \<open>0 <m\<close>] ..
  then have "1 * ?B \<le> real_of_int m"
    unfolding of_int_le_iff[symmetric] by auto
  then show "1 \<le> real_of_int m / ?B" by auto

  from that have "0 \<le> bitlen m - 1" by (auto simp: bitlen_alt_def)

  have "m < 2^nat(bitlen m)" using bitlen_bounds[OF that] ..
  also from that have "\<dots> = 2^nat(bitlen m - 1 + 1)"
    by (auto simp: bitlen_def)
  also have "\<dots> = ?B * 2"
    unfolding nat_add_distrib[OF \<open>0 \<le> bitlen m - 1\<close> zero_le_one] by auto
  finally have "real_of_int m < 2 * ?B"
    by (metis (full_types) mult.commute power.simps(2) of_int_less_numeral_power_cancel_iff)
  then have "real_of_int m / ?B < 2 * ?B / ?B"
    by (rule divide_strict_right_mono) auto
  then show "real_of_int m / ?B < 2" by auto
qed

lemma bitlen_le_iff_floorlog:
  "bitlen x \<le> w \<longleftrightarrow> w \<ge> 0 \<and> floorlog 2 (nat x) \<le> nat w"
  by (auto simp: bitlen_def)

lemma bitlen_le_iff_power:
  "bitlen x \<le> w \<longleftrightarrow> w \<ge> 0 \<and> x < 2 ^ nat w"
  by (auto simp: bitlen_le_iff_floorlog floorlog_le_iff)

lemma less_power_nat_iff_bitlen:
  "x < 2 ^ w \<longleftrightarrow> bitlen (int x) \<le> w"
  using bitlen_le_iff_power[of x w]
  by auto

lemma bitlen_ge_iff_power:
  "w \<le> bitlen x \<longleftrightarrow> w \<le> 0 \<or> 2 ^ (nat w - 1) \<le> x"
  unfolding bitlen_def
  by (auto simp flip: nat_le_iff intro: floorlog_geI dest: floorlog_geD)

lemma bitlen_twopow_add_eq:
  "bitlen (2 ^ w + b) = w + 1" if "0 \<le> b" "b < 2 ^ w"
  by (auto simp: that nat_add_distrib bitlen_le_iff_power bitlen_ge_iff_power intro!: antisym)

end
