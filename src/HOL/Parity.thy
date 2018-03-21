(*  Title:      HOL/Parity.thy
    Author:     Jeremy Avigad
    Author:     Jacques D. Fleuriot
*)

section \<open>Parity in rings and semirings\<close>

theory Parity
  imports Euclidean_Division
begin

subsection \<open>Ring structures with parity and \<open>even\<close>/\<open>odd\<close> predicates\<close>

class semiring_parity = semidom + semiring_char_0 + unique_euclidean_semiring +
  assumes of_nat_div: "of_nat (m div n) = of_nat m div of_nat n"
    and division_segment_of_nat [simp]: "division_segment (of_nat n) = 1"
    and division_segment_euclidean_size [simp]: "division_segment a * of_nat (euclidean_size a) = a"
begin

lemma division_segment_eq_iff:
  "a = b" if "division_segment a = division_segment b"
    and "euclidean_size a = euclidean_size b"
  using that division_segment_euclidean_size [of a] by simp

lemma euclidean_size_of_nat [simp]:
  "euclidean_size (of_nat n) = n"
proof -
  have "division_segment (of_nat n) * of_nat (euclidean_size (of_nat n)) = of_nat n"
    by (fact division_segment_euclidean_size)
  then show ?thesis by simp
qed

lemma of_nat_euclidean_size:
  "of_nat (euclidean_size a) = a div division_segment a"
proof -
  have "of_nat (euclidean_size a) = division_segment a * of_nat (euclidean_size a) div division_segment a"
    by (subst nonzero_mult_div_cancel_left) simp_all
  also have "\<dots> = a div division_segment a"
    by simp
  finally show ?thesis .
qed

lemma division_segment_1 [simp]:
  "division_segment 1 = 1"
  using division_segment_of_nat [of 1] by simp

lemma division_segment_numeral [simp]:
  "division_segment (numeral k) = 1"
  using division_segment_of_nat [of "numeral k"] by simp

lemma euclidean_size_1 [simp]:
  "euclidean_size 1 = 1"
  using euclidean_size_of_nat [of 1] by simp

lemma euclidean_size_numeral [simp]:
  "euclidean_size (numeral k) = numeral k"
  using euclidean_size_of_nat [of "numeral k"] by simp

lemma of_nat_dvd_iff:
  "of_nat m dvd of_nat n \<longleftrightarrow> m dvd n" (is "?P \<longleftrightarrow> ?Q")
proof (cases "m = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof
    assume ?Q
    then show ?P
      by (auto elim: dvd_class.dvdE)
  next
    assume ?P
    with False have "of_nat n = of_nat n div of_nat m * of_nat m"
      by simp
    then have "of_nat n = of_nat (n div m * m)"
      by (simp add: of_nat_div)
    then have "n = n div m * m"
      by (simp only: of_nat_eq_iff)
    then have "n = m * (n div m)"
      by (simp add: ac_simps)
    then show ?Q ..
  qed
qed

lemma of_nat_mod:
  "of_nat (m mod n) = of_nat m mod of_nat n"
proof -
  have "of_nat m div of_nat n * of_nat n + of_nat m mod of_nat n = of_nat m"
    by (simp add: div_mult_mod_eq)
  also have "of_nat m = of_nat (m div n * n + m mod n)"
    by simp
  finally show ?thesis
    by (simp only: of_nat_div of_nat_mult of_nat_add) simp
qed

lemma one_div_two_eq_zero [simp]:
  "1 div 2 = 0"
proof -
  from of_nat_div [symmetric] have "of_nat 1 div of_nat 2 = of_nat 0"
    by (simp only:) simp
  then show ?thesis
    by simp
qed

lemma one_mod_two_eq_one [simp]:
  "1 mod 2 = 1"
proof -
  from of_nat_mod [symmetric] have "of_nat 1 mod of_nat 2 = of_nat 1"
    by (simp only:) simp
  then show ?thesis
    by simp
qed

abbreviation even :: "'a \<Rightarrow> bool"
  where "even a \<equiv> 2 dvd a"

abbreviation odd :: "'a \<Rightarrow> bool"
  where "odd a \<equiv> \<not> 2 dvd a"

lemma even_iff_mod_2_eq_zero:
  "even a \<longleftrightarrow> a mod 2 = 0"
  by (fact dvd_eq_mod_eq_0)

lemma odd_iff_mod_2_eq_one:
  "odd a \<longleftrightarrow> a mod 2 = 1"
proof
  assume "a mod 2 = 1"
  then show "odd a"
    by auto
next
  assume "odd a"
  have eucl: "euclidean_size (a mod 2) = 1"
  proof (rule order_antisym)
    show "euclidean_size (a mod 2) \<le> 1"
      using mod_size_less [of 2 a] by simp
    show "1 \<le> euclidean_size (a mod 2)"
      using \<open>odd a\<close> by (simp add: Suc_le_eq dvd_eq_mod_eq_0)
  qed 
  from \<open>odd a\<close> have "\<not> of_nat 2 dvd division_segment a * of_nat (euclidean_size a)"
    by simp
  then have "\<not> of_nat 2 dvd of_nat (euclidean_size a)"
    by (auto simp only: dvd_mult_unit_iff' is_unit_division_segment)
  then have "\<not> 2 dvd euclidean_size a"
    using of_nat_dvd_iff [of 2] by simp
  then have "euclidean_size a mod 2 = 1"
    by (simp add: semidom_modulo_class.dvd_eq_mod_eq_0)
  then have "of_nat (euclidean_size a mod 2) = of_nat 1"
    by simp
  then have "of_nat (euclidean_size a) mod 2 = 1"
    by (simp add: of_nat_mod)
  from \<open>odd a\<close> eucl
  show "a mod 2 = 1"
    by (auto intro: division_segment_eq_iff simp add: division_segment_mod)
qed

lemma parity_cases [case_names even odd]:
  assumes "even a \<Longrightarrow> a mod 2 = 0 \<Longrightarrow> P"
  assumes "odd a \<Longrightarrow> a mod 2 = 1 \<Longrightarrow> P"
  shows P
  using assms by (cases "even a") (simp_all add: odd_iff_mod_2_eq_one)

lemma not_mod_2_eq_1_eq_0 [simp]:
  "a mod 2 \<noteq> 1 \<longleftrightarrow> a mod 2 = 0"
  by (cases a rule: parity_cases) simp_all

lemma not_mod_2_eq_0_eq_1 [simp]:
  "a mod 2 \<noteq> 0 \<longleftrightarrow> a mod 2 = 1"
  by (cases a rule: parity_cases) simp_all

lemma evenE [elim?]:
  assumes "even a"
  obtains b where "a = 2 * b"
  using assms by (rule dvdE)

lemma oddE [elim?]:
  assumes "odd a"
  obtains b where "a = 2 * b + 1"
proof -
  have "a = 2 * (a div 2) + a mod 2"
    by (simp add: mult_div_mod_eq)
  with assms have "a = 2 * (a div 2) + 1"
    by (simp add: odd_iff_mod_2_eq_one)
  then show ?thesis ..
qed

lemma mod_2_eq_odd:
  "a mod 2 = of_bool (odd a)"
  by (auto elim: oddE)

lemma of_bool_odd_eq_mod_2:
  "of_bool (odd a) = a mod 2"
  by (simp add: mod_2_eq_odd)

lemma one_mod_2_pow_eq [simp]:
  "1 mod (2 ^ n) = of_bool (n > 0)"
proof -
  have "1 mod (2 ^ n) = of_nat (1 mod (2 ^ n))"
    using of_nat_mod [of 1 "2 ^ n"] by simp
  also have "\<dots> = of_bool (n > 0)"
    by simp
  finally show ?thesis .
qed

lemma one_div_2_pow_eq [simp]:
  "1 div (2 ^ n) = of_bool (n = 0)"
  using div_mult_mod_eq [of 1 "2 ^ n"] by auto

lemma even_of_nat [simp]:
  "even (of_nat a) \<longleftrightarrow> even a"
proof -
  have "even (of_nat a) \<longleftrightarrow> of_nat 2 dvd of_nat a"
    by simp
  also have "\<dots> \<longleftrightarrow> even a"
    by (simp only: of_nat_dvd_iff)
  finally show ?thesis .
qed

lemma even_zero [simp]:
  "even 0"
  by (fact dvd_0_right)

lemma odd_one [simp]:
  "odd 1"
proof -
  have "\<not> (2 :: nat) dvd 1"
    by simp
  then have "\<not> of_nat 2 dvd of_nat 1"
    unfolding of_nat_dvd_iff by simp
  then show ?thesis
    by simp
qed

lemma odd_even_add:
  "even (a + b)" if "odd a" and "odd b"
proof -
  from that obtain c d where "a = 2 * c + 1" and "b = 2 * d + 1"
    by (blast elim: oddE)
  then have "a + b = 2 * c + 2 * d + (1 + 1)"
    by (simp only: ac_simps)
  also have "\<dots> = 2 * (c + d + 1)"
    by (simp add: algebra_simps)
  finally show ?thesis ..
qed

lemma even_add [simp]:
  "even (a + b) \<longleftrightarrow> (even a \<longleftrightarrow> even b)"
  by (auto simp add: dvd_add_right_iff dvd_add_left_iff odd_even_add)

lemma odd_add [simp]:
  "odd (a + b) \<longleftrightarrow> \<not> (odd a \<longleftrightarrow> odd b)"
  by simp

lemma even_plus_one_iff [simp]:
  "even (a + 1) \<longleftrightarrow> odd a"
  by (auto simp add: dvd_add_right_iff intro: odd_even_add)

lemma even_mult_iff [simp]:
  "even (a * b) \<longleftrightarrow> even a \<or> even b" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q
  then show ?P
    by auto
next
  assume ?P
  show ?Q
  proof (rule ccontr)
    assume "\<not> (even a \<or> even b)"
    then have "odd a" and "odd b"
      by auto
    then obtain r s where "a = 2 * r + 1" and "b = 2 * s + 1"
      by (blast elim: oddE)
    then have "a * b = (2 * r + 1) * (2 * s + 1)"
      by simp
    also have "\<dots> = 2 * (2 * r * s + r + s) + 1"
      by (simp add: algebra_simps)
    finally have "odd (a * b)"
      by simp
    with \<open>?P\<close> show False
      by auto
  qed
qed

lemma even_numeral [simp]: "even (numeral (Num.Bit0 n))"
proof -
  have "even (2 * numeral n)"
    unfolding even_mult_iff by simp
  then have "even (numeral n + numeral n)"
    unfolding mult_2 .
  then show ?thesis
    unfolding numeral.simps .
qed

lemma odd_numeral [simp]: "odd (numeral (Num.Bit1 n))"
proof
  assume "even (numeral (num.Bit1 n))"
  then have "even (numeral n + numeral n + 1)"
    unfolding numeral.simps .
  then have "even (2 * numeral n + 1)"
    unfolding mult_2 .
  then have "2 dvd numeral n * 2 + 1"
    by (simp add: ac_simps)
  then have "2 dvd 1"
    using dvd_add_times_triv_left_iff [of 2 "numeral n" 1] by simp
  then show False by simp
qed

lemma even_power [simp]: "even (a ^ n) \<longleftrightarrow> even a \<and> n > 0"
  by (induct n) auto

lemma even_succ_div_two [simp]:
  "even a \<Longrightarrow> (a + 1) div 2 = a div 2"
  by (cases "a = 0") (auto elim!: evenE dest: mult_not_zero)

lemma odd_succ_div_two [simp]:
  "odd a \<Longrightarrow> (a + 1) div 2 = a div 2 + 1"
  by (auto elim!: oddE simp add: add.assoc)

lemma even_two_times_div_two:
  "even a \<Longrightarrow> 2 * (a div 2) = a"
  by (fact dvd_mult_div_cancel)

lemma odd_two_times_div_two_succ [simp]:
  "odd a \<Longrightarrow> 2 * (a div 2) + 1 = a"
  using mult_div_mod_eq [of 2 a]
  by (simp add: even_iff_mod_2_eq_zero)

lemma coprime_left_2_iff_odd [simp]:
  "coprime 2 a \<longleftrightarrow> odd a"
proof
  assume "odd a"
  show "coprime 2 a"
  proof (rule coprimeI)
    fix b
    assume "b dvd 2" "b dvd a"
    then have "b dvd a mod 2"
      by (auto intro: dvd_mod)
    with \<open>odd a\<close> show "is_unit b"
      by (simp add: mod_2_eq_odd)
  qed
next
  assume "coprime 2 a"
  show "odd a"
  proof (rule notI)
    assume "even a"
    then obtain b where "a = 2 * b" ..
    with \<open>coprime 2 a\<close> have "coprime 2 (2 * b)"
      by simp
    moreover have "\<not> coprime 2 (2 * b)"
      by (rule not_coprimeI [of 2]) simp_all
    ultimately show False
      by blast
  qed
qed

lemma coprime_right_2_iff_odd [simp]:
  "coprime a 2 \<longleftrightarrow> odd a"
  using coprime_left_2_iff_odd [of a] by (simp add: ac_simps)

lemma div_mult2_eq':
  "a div (of_nat m * of_nat n) = a div of_nat m div of_nat n"
proof (cases a "of_nat m * of_nat n" rule: divmod_cases)
  case (divides q)
  then show ?thesis
    using nonzero_mult_div_cancel_right [of "of_nat m" "q * of_nat n"]
    by (simp add: ac_simps)
next
  case (remainder q r)
  then have "division_segment r = 1"
    using division_segment_of_nat [of "m * n"] by simp
  with division_segment_euclidean_size [of r]
  have "of_nat (euclidean_size r) = r"
    by simp
  then have "r div of_nat m = of_nat (euclidean_size r) div of_nat m"
    by simp
  also have "\<dots> = of_nat (euclidean_size r div m)"
    by (simp add: of_nat_div)
  finally have "r div of_nat m = of_nat (euclidean_size r div m)"
    .
  with remainder(1-3) have "r div of_nat m div of_nat n = 0"
    by (auto intro!: div_eqI [of _ "of_nat (euclidean_size r div m)"])
      (simp add: division_segment_mult euclidean_size_mult ac_simps less_mult_imp_div_less )
  with remainder(1)
  have "q = (r div of_nat m + q * of_nat n * of_nat m div of_nat m) div of_nat n"
    by simp
  with remainder(5-7) show ?thesis
    using div_plus_div_distrib_dvd_right [of "of_nat m" "q * (of_nat m * of_nat n)" r]
    by (simp add: ac_simps)
next
  case by0
  then show ?thesis
    by auto
qed

lemma mod_mult2_eq':
  "a mod (of_nat m * of_nat n) = of_nat m * (a div of_nat m mod of_nat n) + a mod of_nat m"
proof -
  have "a div (of_nat m * of_nat n) * (of_nat m * of_nat n) + a mod (of_nat m * of_nat n) = a div of_nat m div of_nat n * of_nat n * of_nat m + (a div of_nat m mod of_nat n * of_nat m + a mod of_nat m)"
    by (simp add: combine_common_factor div_mult_mod_eq)
  moreover have "a div of_nat m div of_nat n * of_nat n * of_nat m = of_nat n * of_nat m * (a div of_nat m div of_nat n)"
    by (simp add: ac_simps)
  ultimately show ?thesis
    by (simp add: div_mult2_eq' mult_commute)
qed

end

class ring_parity = ring + semiring_parity
begin

subclass comm_ring_1 ..

lemma even_minus:
  "even (- a) \<longleftrightarrow> even a"
  by (fact dvd_minus_iff)

lemma even_diff [simp]:
  "even (a - b) \<longleftrightarrow> even (a + b)"
  using even_add [of a "- b"] by simp

lemma minus_1_mod_2_eq [simp]:
  "- 1 mod 2 = 1"
  by (simp add: mod_2_eq_odd)

lemma minus_1_div_2_eq [simp]:
  "- 1 div 2 = - 1"
proof -
  from div_mult_mod_eq [of "- 1" 2]
  have "- 1 div 2 * 2 = - 1 * 2"
    using local.add_implies_diff by fastforce
  then show ?thesis
    using mult_right_cancel [of 2 "- 1 div 2" "- 1"] by simp
qed

end


subsection \<open>Instance for @{typ nat}\<close>

instance nat :: semiring_parity
  by standard (simp_all add: dvd_eq_mod_eq_0)

lemma even_Suc_Suc_iff [simp]:
  "even (Suc (Suc n)) \<longleftrightarrow> even n"
  using dvd_add_triv_right_iff [of 2 n] by simp

lemma even_Suc [simp]: "even (Suc n) \<longleftrightarrow> odd n"
  using even_plus_one_iff [of n] by simp

lemma even_diff_nat [simp]:
  "even (m - n) \<longleftrightarrow> m < n \<or> even (m + n)" for m n :: nat
proof (cases "n \<le> m")
  case True
  then have "m - n + n * 2 = m + n" by (simp add: mult_2_right)
  moreover have "even (m - n) \<longleftrightarrow> even (m - n + n * 2)" by simp
  ultimately have "even (m - n) \<longleftrightarrow> even (m + n)" by (simp only:)
  then show ?thesis by auto
next
  case False
  then show ?thesis by simp
qed

lemma odd_pos:
  "odd n \<Longrightarrow> 0 < n" for n :: nat
  by (auto elim: oddE)

lemma Suc_double_not_eq_double:
  "Suc (2 * m) \<noteq> 2 * n"
proof
  assume "Suc (2 * m) = 2 * n"
  moreover have "odd (Suc (2 * m))" and "even (2 * n)"
    by simp_all
  ultimately show False by simp
qed

lemma double_not_eq_Suc_double:
  "2 * m \<noteq> Suc (2 * n)"
  using Suc_double_not_eq_double [of n m] by simp

lemma odd_Suc_minus_one [simp]: "odd n \<Longrightarrow> Suc (n - Suc 0) = n"
  by (auto elim: oddE)

lemma even_Suc_div_two [simp]:
  "even n \<Longrightarrow> Suc n div 2 = n div 2"
  using even_succ_div_two [of n] by simp

lemma odd_Suc_div_two [simp]:
  "odd n \<Longrightarrow> Suc n div 2 = Suc (n div 2)"
  using odd_succ_div_two [of n] by simp

lemma odd_two_times_div_two_nat [simp]:
  assumes "odd n"
  shows "2 * (n div 2) = n - (1 :: nat)"
proof -
  from assms have "2 * (n div 2) + 1 = n"
    by (rule odd_two_times_div_two_succ)
  then have "Suc (2 * (n div 2)) - 1 = n - 1"
    by simp
  then show ?thesis
    by simp
qed

lemma parity_induct [case_names zero even odd]:
  assumes zero: "P 0"
  assumes even: "\<And>n. P n \<Longrightarrow> P (2 * n)"
  assumes odd: "\<And>n. P n \<Longrightarrow> P (Suc (2 * n))"
  shows "P n"
proof (induct n rule: less_induct)
  case (less n)
  show "P n"
  proof (cases "n = 0")
    case True with zero show ?thesis by simp
  next
    case False
    with less have hyp: "P (n div 2)" by simp
    show ?thesis
    proof (cases "even n")
      case True
      with hyp even [of "n div 2"] show ?thesis
        by simp
    next
      case False
      with hyp odd [of "n div 2"] show ?thesis
        by simp
    qed
  qed
qed


subsection \<open>Parity and powers\<close>

context ring_1
begin

lemma power_minus_even [simp]: "even n \<Longrightarrow> (- a) ^ n = a ^ n"
  by (auto elim: evenE)

lemma power_minus_odd [simp]: "odd n \<Longrightarrow> (- a) ^ n = - (a ^ n)"
  by (auto elim: oddE)

lemma uminus_power_if:
  "(- a) ^ n = (if even n then a ^ n else - (a ^ n))"
  by auto

lemma neg_one_even_power [simp]: "even n \<Longrightarrow> (- 1) ^ n = 1"
  by simp

lemma neg_one_odd_power [simp]: "odd n \<Longrightarrow> (- 1) ^ n = - 1"
  by simp

lemma neg_one_power_add_eq_neg_one_power_diff: "k \<le> n \<Longrightarrow> (- 1) ^ (n + k) = (- 1) ^ (n - k)"
  by (cases "even (n + k)") auto

lemma minus_one_power_iff: "(- 1) ^ n = (if even n then 1 else - 1)"
  by (induct n) auto

end

context linordered_idom
begin

lemma zero_le_even_power: "even n \<Longrightarrow> 0 \<le> a ^ n"
  by (auto elim: evenE)

lemma zero_le_odd_power: "odd n \<Longrightarrow> 0 \<le> a ^ n \<longleftrightarrow> 0 \<le> a"
  by (auto simp add: power_even_eq zero_le_mult_iff elim: oddE)

lemma zero_le_power_eq: "0 \<le> a ^ n \<longleftrightarrow> even n \<or> odd n \<and> 0 \<le> a"
  by (auto simp add: zero_le_even_power zero_le_odd_power)

lemma zero_less_power_eq: "0 < a ^ n \<longleftrightarrow> n = 0 \<or> even n \<and> a \<noteq> 0 \<or> odd n \<and> 0 < a"
proof -
  have [simp]: "0 = a ^ n \<longleftrightarrow> a = 0 \<and> n > 0"
    unfolding power_eq_0_iff [of a n, symmetric] by blast
  show ?thesis
    unfolding less_le zero_le_power_eq by auto
qed

lemma power_less_zero_eq [simp]: "a ^ n < 0 \<longleftrightarrow> odd n \<and> a < 0"
  unfolding not_le [symmetric] zero_le_power_eq by auto

lemma power_le_zero_eq: "a ^ n \<le> 0 \<longleftrightarrow> n > 0 \<and> (odd n \<and> a \<le> 0 \<or> even n \<and> a = 0)"
  unfolding not_less [symmetric] zero_less_power_eq by auto

lemma power_even_abs: "even n \<Longrightarrow> \<bar>a\<bar> ^ n = a ^ n"
  using power_abs [of a n] by (simp add: zero_le_even_power)

lemma power_mono_even:
  assumes "even n" and "\<bar>a\<bar> \<le> \<bar>b\<bar>"
  shows "a ^ n \<le> b ^ n"
proof -
  have "0 \<le> \<bar>a\<bar>" by auto
  with \<open>\<bar>a\<bar> \<le> \<bar>b\<bar>\<close> have "\<bar>a\<bar> ^ n \<le> \<bar>b\<bar> ^ n"
    by (rule power_mono)
  with \<open>even n\<close> show ?thesis
    by (simp add: power_even_abs)
qed

lemma power_mono_odd:
  assumes "odd n" and "a \<le> b"
  shows "a ^ n \<le> b ^ n"
proof (cases "b < 0")
  case True
  with \<open>a \<le> b\<close> have "- b \<le> - a" and "0 \<le> - b" by auto
  then have "(- b) ^ n \<le> (- a) ^ n" by (rule power_mono)
  with \<open>odd n\<close> show ?thesis by simp
next
  case False
  then have "0 \<le> b" by auto
  show ?thesis
  proof (cases "a < 0")
    case True
    then have "n \<noteq> 0" and "a \<le> 0" using \<open>odd n\<close> [THEN odd_pos] by auto
    then have "a ^ n \<le> 0" unfolding power_le_zero_eq using \<open>odd n\<close> by auto
    moreover from \<open>0 \<le> b\<close> have "0 \<le> b ^ n" by auto
    ultimately show ?thesis by auto
  next
    case False
    then have "0 \<le> a" by auto
    with \<open>a \<le> b\<close> show ?thesis
      using power_mono by auto
  qed
qed

text \<open>Simplify, when the exponent is a numeral\<close>

lemma zero_le_power_eq_numeral [simp]:
  "0 \<le> a ^ numeral w \<longleftrightarrow> even (numeral w :: nat) \<or> odd (numeral w :: nat) \<and> 0 \<le> a"
  by (fact zero_le_power_eq)

lemma zero_less_power_eq_numeral [simp]:
  "0 < a ^ numeral w \<longleftrightarrow>
    numeral w = (0 :: nat) \<or>
    even (numeral w :: nat) \<and> a \<noteq> 0 \<or>
    odd (numeral w :: nat) \<and> 0 < a"
  by (fact zero_less_power_eq)

lemma power_le_zero_eq_numeral [simp]:
  "a ^ numeral w \<le> 0 \<longleftrightarrow>
    (0 :: nat) < numeral w \<and>
    (odd (numeral w :: nat) \<and> a \<le> 0 \<or> even (numeral w :: nat) \<and> a = 0)"
  by (fact power_le_zero_eq)

lemma power_less_zero_eq_numeral [simp]:
  "a ^ numeral w < 0 \<longleftrightarrow> odd (numeral w :: nat) \<and> a < 0"
  by (fact power_less_zero_eq)

lemma power_even_abs_numeral [simp]:
  "even (numeral w :: nat) \<Longrightarrow> \<bar>a\<bar> ^ numeral w = a ^ numeral w"
  by (fact power_even_abs)

end


subsection \<open>Instance for @{typ int}\<close>

instance int :: ring_parity
  by standard (simp_all add: dvd_eq_mod_eq_0 divide_int_def division_segment_int_def)

lemma even_diff_iff:
  "even (k - l) \<longleftrightarrow> even (k + l)" for k l :: int
  by (fact even_diff)

lemma even_abs_add_iff:
  "even (\<bar>k\<bar> + l) \<longleftrightarrow> even (k + l)" for k l :: int
  by simp

lemma even_add_abs_iff:
  "even (k + \<bar>l\<bar>) \<longleftrightarrow> even (k + l)" for k l :: int
  by simp

lemma even_nat_iff: "0 \<le> k \<Longrightarrow> even (nat k) \<longleftrightarrow> even k"
  by (simp add: even_of_nat [of "nat k", where ?'a = int, symmetric])


subsection \<open>Abstract bit operations\<close>

context semiring_parity
begin

text \<open>The primary purpose of the following operations is
  to avoid ad-hoc simplification of concrete expressions @{term "2 ^ n"}\<close>

definition push_bit :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  where push_bit_eq_mult: "push_bit n a = a * 2 ^ n"
 
definition take_bit :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  where take_bit_eq_mod: "take_bit n a = a mod of_nat (2 ^ n)"

definition drop_bit :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  where drop_bit_eq_div: "drop_bit n a = a div of_nat (2 ^ n)"

lemma bit_ident:
  "push_bit n (drop_bit n a) + take_bit n a = a"
  using div_mult_mod_eq by (simp add: push_bit_eq_mult take_bit_eq_mod drop_bit_eq_div)

lemma take_bit_take_bit [simp]:
  "take_bit n (take_bit n a) = take_bit n a"
  by (simp add: take_bit_eq_mod)
  
lemma take_bit_0 [simp]:
  "take_bit 0 a = 0"
  by (simp add: take_bit_eq_mod)

lemma take_bit_Suc [simp]:
  "take_bit (Suc n) a = take_bit n (a div 2) * 2 + of_bool (odd a)"
proof -
  have "1 + 2 * (a div 2) mod (2 * 2 ^ n) = (a div 2 * 2 + a mod 2) mod (2 * 2 ^ n)"
    if "odd a"
    using that mod_mult2_eq' [of "1 + 2 * (a div 2)" 2 "2 ^ n"]
    by (simp add: ac_simps odd_iff_mod_2_eq_one mult_mod_right)
  also have "\<dots> = a mod (2 * 2 ^ n)"
    by (simp only: div_mult_mod_eq)
  finally show ?thesis
    by (simp add: take_bit_eq_mod algebra_simps mult_mod_right)
qed

lemma take_bit_of_0 [simp]:
  "take_bit n 0 = 0"
  by (simp add: take_bit_eq_mod)

lemma take_bit_plus:
  "take_bit n (take_bit n a + take_bit n b) = take_bit n (a + b)"
  by (simp add: take_bit_eq_mod mod_simps)

lemma take_bit_of_1_eq_0_iff [simp]:
  "take_bit n 1 = 0 \<longleftrightarrow> n = 0"
  by (simp add: take_bit_eq_mod)

lemma push_bit_eq_0_iff [simp]:
  "push_bit n a = 0 \<longleftrightarrow> a = 0"
  by (simp add: push_bit_eq_mult)

lemma drop_bit_0 [simp]:
  "drop_bit 0 = id"
  by (simp add: fun_eq_iff drop_bit_eq_div)

lemma drop_bit_of_0 [simp]:
  "drop_bit n 0 = 0"
  by (simp add: drop_bit_eq_div)

lemma drop_bit_Suc [simp]:
  "drop_bit (Suc n) a = drop_bit n (a div 2)"
proof (cases "even a")
  case True
  then obtain b where "a = 2 * b" ..
  moreover have "drop_bit (Suc n) (2 * b) = drop_bit n b"
    by (simp add: drop_bit_eq_div)
  ultimately show ?thesis
    by simp
next
  case False
  then obtain b where "a = 2 * b + 1" ..
  moreover have "drop_bit (Suc n) (2 * b + 1) = drop_bit n b"
    using div_mult2_eq' [of "1 + b * 2" 2 "2 ^ n"]
    by (auto simp add: drop_bit_eq_div ac_simps)
  ultimately show ?thesis
    by simp
qed

lemma drop_bit_half:
  "drop_bit n (a div 2) = drop_bit n a div 2"
  by (induction n arbitrary: a) simp_all

lemma drop_bit_of_bool [simp]:
  "drop_bit n (of_bool d) = of_bool (n = 0 \<and> d)"
  by (cases n) simp_all

lemma even_take_bit_eq [simp]:
  "even (take_bit n a) \<longleftrightarrow> n = 0 \<or> even a"
  by (cases n) (simp_all add: take_bit_eq_mod dvd_mod_iff)

lemma push_bit_0_id [simp]:
  "push_bit 0 = id"
  by (simp add: fun_eq_iff push_bit_eq_mult)

lemma push_bit_of_0 [simp]:
  "push_bit n 0 = 0"
  by (simp add: push_bit_eq_mult)

lemma push_bit_of_1:
  "push_bit n 1 = 2 ^ n"
  by (simp add: push_bit_eq_mult)

lemma push_bit_Suc [simp]:
  "push_bit (Suc n) a = push_bit n (a * 2)"
  by (simp add: push_bit_eq_mult ac_simps)

lemma push_bit_double:
  "push_bit n (a * 2) = push_bit n a * 2"
  by (simp add: push_bit_eq_mult ac_simps)

lemma drop_bit_take_bit [simp]:
  "drop_bit n (take_bit n a) = 0"
  by (simp add: drop_bit_eq_div take_bit_eq_mod)

lemma take_bit_drop_bit_commute:
  "drop_bit m (take_bit n a) = take_bit (n - m) (drop_bit m a)"
  for m n :: nat
proof (cases "n \<ge> m")
  case True
  moreover define q where "q = n - m"
  ultimately have "n - m = q" and "n = m + q"
    by simp_all
  moreover have "drop_bit m (take_bit (m + q) a) = take_bit q (drop_bit m a)"
    using mod_mult2_eq' [of a "2 ^ m" "2 ^ q"]
    by (simp add: drop_bit_eq_div take_bit_eq_mod power_add)
  ultimately show ?thesis
    by simp
next
  case False
  moreover define q where "q = m - n"
  ultimately have "m - n = q" and "m = n + q"
    by simp_all
  moreover have "drop_bit (n + q) (take_bit n a) = 0"
    using div_mult2_eq' [of "a mod 2 ^ n" "2 ^ n" "2 ^ q"]
    by (simp add: drop_bit_eq_div take_bit_eq_mod power_add div_mult2_eq)
  ultimately show ?thesis
    by simp
qed

end

end
