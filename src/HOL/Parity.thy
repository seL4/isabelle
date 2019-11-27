(*  Title:      HOL/Parity.thy
    Author:     Jeremy Avigad
    Author:     Jacques D. Fleuriot
*)

section \<open>Parity in rings and semirings\<close>

theory Parity
  imports Euclidean_Division
begin

subsection \<open>Ring structures with parity and \<open>even\<close>/\<open>odd\<close> predicates\<close>

class semiring_parity = comm_semiring_1 + semiring_modulo +
  assumes even_iff_mod_2_eq_zero: "2 dvd a \<longleftrightarrow> a mod 2 = 0"
    and odd_iff_mod_2_eq_one: "\<not> 2 dvd a \<longleftrightarrow> a mod 2 = 1"
    and odd_one [simp]: "\<not> 2 dvd 1"
begin

abbreviation even :: "'a \<Rightarrow> bool"
  where "even a \<equiv> 2 dvd a"

abbreviation odd :: "'a \<Rightarrow> bool"
  where "odd a \<equiv> \<not> 2 dvd a"

lemma parity_cases [case_names even odd]:
  assumes "even a \<Longrightarrow> a mod 2 = 0 \<Longrightarrow> P"
  assumes "odd a \<Longrightarrow> a mod 2 = 1 \<Longrightarrow> P"
  shows P
  using assms by (cases "even a")
    (simp_all add: even_iff_mod_2_eq_zero [symmetric] odd_iff_mod_2_eq_one [symmetric])

lemma odd_of_bool_self [simp]:
  \<open>odd (of_bool p) \<longleftrightarrow> p\<close>
  by (cases p) simp_all

lemma not_mod_2_eq_0_eq_1 [simp]:
  "a mod 2 \<noteq> 0 \<longleftrightarrow> a mod 2 = 1"
  by (cases a rule: parity_cases) simp_all

lemma not_mod_2_eq_1_eq_0 [simp]:
  "a mod 2 \<noteq> 1 \<longleftrightarrow> a mod 2 = 0"
  by (cases a rule: parity_cases) simp_all

lemma mod2_eq_if: "a mod 2 = (if 2 dvd a then 0 else 1)"
  by (simp add: even_iff_mod_2_eq_zero odd_iff_mod_2_eq_one)

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
  by (auto elim: oddE simp add: even_iff_mod_2_eq_zero)

lemma of_bool_odd_eq_mod_2:
  "of_bool (odd a) = a mod 2"
  by (simp add: mod_2_eq_odd)

lemma even_zero [simp]:
  "even 0"
  by (fact dvd_0_right)

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

end


subsection \<open>Special case: euclidean rings containing the natural numbers\<close>

context unique_euclidean_semiring_with_nat
begin

subclass semiring_parity
proof
  show "2 dvd a \<longleftrightarrow> a mod 2 = 0" for a
    by (fact dvd_eq_mod_eq_0)
  show "\<not> 2 dvd a \<longleftrightarrow> a mod 2 = 1" for a
  proof
    assume "a mod 2 = 1"
    then show "\<not> 2 dvd a"
      by auto
  next
    assume "\<not> 2 dvd a"
    have eucl: "euclidean_size (a mod 2) = 1"
    proof (rule order_antisym)
      show "euclidean_size (a mod 2) \<le> 1"
        using mod_size_less [of 2 a] by simp
      show "1 \<le> euclidean_size (a mod 2)"
        using \<open>\<not> 2 dvd a\<close> by (simp add: Suc_le_eq dvd_eq_mod_eq_0)
    qed 
    from \<open>\<not> 2 dvd a\<close> have "\<not> of_nat 2 dvd division_segment a * of_nat (euclidean_size a)"
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
    from \<open>\<not> 2 dvd a\<close> eucl
    show "a mod 2 = 1"
      by (auto intro: division_segment_eq_iff simp add: division_segment_mod)
  qed
  show "\<not> is_unit 2"
  proof (rule notI)
    assume "is_unit 2"
    then have "of_nat 2 dvd of_nat 1"
      by simp
    then have "is_unit (2::nat)"
      by (simp only: of_nat_dvd_iff)
    then show False
      by simp
  qed
qed

lemma even_of_nat [simp]:
  "even (of_nat a) \<longleftrightarrow> even a"
proof -
  have "even (of_nat a) \<longleftrightarrow> of_nat 2 dvd of_nat a"
    by simp
  also have "\<dots> \<longleftrightarrow> even a"
    by (simp only: of_nat_dvd_iff)
  finally show ?thesis .
qed

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

end

context unique_euclidean_ring_with_nat
begin

subclass ring_parity ..

lemma minus_1_mod_2_eq [simp]:
  "- 1 mod 2 = 1"
  by (simp add: mod_2_eq_odd)

lemma minus_1_div_2_eq [simp]:
  "- 1 div 2 = - 1"
proof -
  from div_mult_mod_eq [of "- 1" 2]
  have "- 1 div 2 * 2 = - 1 * 2"
    using add_implies_diff by fastforce
  then show ?thesis
    using mult_right_cancel [of 2 "- 1 div 2" "- 1"] by simp
qed

end


subsection \<open>Instance for \<^typ>\<open>nat\<close>\<close>

instance nat :: unique_euclidean_semiring_with_nat
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

lemma not_mod2_eq_Suc_0_eq_0 [simp]:
  "n mod 2 \<noteq> Suc 0 \<longleftrightarrow> n mod 2 = 0"
  using not_mod_2_eq_1_eq_0 [of n] by simp

lemma odd_card_imp_not_empty:
  \<open>A \<noteq> {}\<close> if \<open>odd (card A)\<close>
  using that by auto

lemma nat_induct2 [case_names 0 1 step]:
  assumes "P 0" "P 1" and step: "\<And>n::nat. P n \<Longrightarrow> P (n + 2)"
  shows "P n"
proof (induct n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < Suc (Suc 0)")
    case True
    then show ?thesis
      using assms by (auto simp: less_Suc_eq)
  next
    case False
    then obtain k where k: "n = Suc (Suc k)"
      by (force simp: not_less nat_le_iff_add)
    then have "k<n"
      by simp
    with less assms have "P (k+2)"
      by blast
    then show ?thesis
      by (simp add: k)
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


subsection \<open>Instance for \<^typ>\<open>int\<close>\<close>

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

lemma zdiv_zmult2_eq:
  \<open>a div (b * c) = (a div b) div c\<close> if \<open>c \<ge> 0\<close> for a b c :: int
proof (cases \<open>b \<ge> 0\<close>)
  case True
  with that show ?thesis
    using div_mult2_eq' [of a \<open>nat b\<close> \<open>nat c\<close>] by simp
next
  case False
  with that show ?thesis
    using div_mult2_eq' [of \<open>- a\<close> \<open>nat (- b)\<close> \<open>nat c\<close>] by simp
qed

lemma zmod_zmult2_eq:
  \<open>a mod (b * c) = b * (a div b mod c) + a mod b\<close> if \<open>c \<ge> 0\<close> for a b c :: int
proof (cases \<open>b \<ge> 0\<close>)
  case True
  with that show ?thesis
    using mod_mult2_eq' [of a \<open>nat b\<close> \<open>nat c\<close>] by simp
next
  case False
  with that show ?thesis
    using mod_mult2_eq' [of \<open>- a\<close> \<open>nat (- b)\<close> \<open>nat c\<close>] by simp
qed


subsection \<open>Abstract bit structures\<close>

class semiring_bits = semiring_parity +
  assumes bit_induct [case_names stable rec]:
    \<open>(\<And>a. a div 2 = a \<Longrightarrow> P a)
     \<Longrightarrow> (\<And>a b. P a \<Longrightarrow> (of_bool b + 2 * a) div 2 = a \<Longrightarrow> P (of_bool b + 2 * a))
        \<Longrightarrow> P a\<close>
  assumes bits_div_0 [simp]: \<open>0 div a = 0\<close>
    and bits_div_by_1 [simp]: \<open>a div 1 = a\<close>
    and bit_mod_div_trivial [simp]: \<open>a mod b div b = 0\<close>
    and even_succ_div_2 [simp]: \<open>even a \<Longrightarrow> (1 + a) div 2 = a div 2\<close>
    and div_exp_eq: \<open>a div 2 ^ m div 2 ^ n = a div 2 ^ (m + n)\<close>
    and mod_exp_eq: \<open>a mod 2 ^ m mod 2 ^ n = a mod 2 ^ min m n\<close>
    and mult_exp_mod_exp_eq: \<open>m \<le> n \<Longrightarrow> (a * 2 ^ m) mod (2 ^ n) = (a mod 2 ^ (n - m)) * 2 ^ m\<close>
    and div_exp_mod_exp_eq: \<open>a div 2 ^ n mod 2 ^ m = a mod (2 ^ (n + m)) div 2 ^ n\<close>
begin

lemma bits_1_div_2 [simp]:
  \<open>1 div 2 = 0\<close>
  using even_succ_div_2 [of 0] by simp

lemma bits_1_div_exp [simp]:
  \<open>1 div 2 ^ n = of_bool (n = 0)\<close>
  using div_exp_eq [of 1 1] by (cases n) simp_all

lemma even_succ_div_exp [simp]:
  \<open>(1 + a) div 2 ^ n = a div 2 ^ n\<close> if \<open>even a\<close> and \<open>n > 0\<close>
proof (cases n)
  case 0
  with that show ?thesis
    by simp
next
  case (Suc n)
  with \<open>even a\<close> have \<open>(1 + a) div 2 ^ Suc n = a div 2 ^ Suc n\<close>
  proof (induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    then show ?case
      using div_exp_eq [of _ 1 \<open>Suc n\<close>, symmetric]
      by simp
  qed
  with Suc show ?thesis
    by simp
qed

lemma even_succ_mod_exp [simp]:
  \<open>(1 + a) mod 2 ^ n = 1 + (a mod 2 ^ n)\<close> if \<open>even a\<close> and \<open>n > 0\<close>
  using div_mult_mod_eq [of \<open>1 + a\<close> \<open>2 ^ n\<close>] that
  apply simp
  by (metis local.add.left_commute local.add_left_cancel local.div_mult_mod_eq)

lemma bits_mod_by_1 [simp]:
  \<open>a mod 1 = 0\<close>
  using div_mult_mod_eq [of a 1] by simp

lemma bits_mod_0 [simp]:
  \<open>0 mod a = 0\<close>
  using div_mult_mod_eq [of 0 a] by simp

lemma one_mod_two_eq_one [simp]:
  \<open>1 mod 2 = 1\<close>
  by (simp add: mod2_eq_if)

definition bit :: \<open>'a \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>bit a n \<longleftrightarrow> odd (a div 2 ^ n)\<close>

lemma bit_0 [simp]:
  \<open>bit a 0 \<longleftrightarrow> odd a\<close>
  by (simp add: bit_def)

lemma bit_Suc [simp]:
  \<open>bit a (Suc n) \<longleftrightarrow> bit (a div 2) n\<close>
  using div_exp_eq [of a 1 n] by (simp add: bit_def)

context
  fixes a
  assumes stable: \<open>a div 2 = a\<close>
begin

lemma stable_imp_add_self:
  \<open>a + a mod 2 = 0\<close>
proof -
  have \<open>a div 2 * 2 + a mod 2 = a\<close>
    by (fact div_mult_mod_eq)
  then have \<open>a * 2 + a mod 2 = a\<close>
    by (simp add: stable)
  then show ?thesis
    by (simp add: mult_2_right ac_simps)
qed

lemma stable_imp_bit_iff_odd:
  \<open>bit a n \<longleftrightarrow> odd a\<close>
  by (induction n) (simp_all add: stable)

end

lemma bit_iff_idd_imp_stable:
  \<open>a div 2 = a\<close> if \<open>\<And>n. bit a n \<longleftrightarrow> odd a\<close>
using that proof (induction a rule: bit_induct)
  case (stable a)
  then show ?case
    by simp
next
  case (rec a b)
  from rec.prems [of 1] have [simp]: \<open>b = odd a\<close>
    by (simp add: rec.hyps)
  from rec.hyps have hyp: \<open>(of_bool (odd a) + 2 * a) div 2 = a\<close>
    by simp
  have \<open>bit a n \<longleftrightarrow> odd a\<close> for n
    using rec.prems [of \<open>Suc n\<close>] by (simp add: hyp)
  then have \<open>a div 2 = a\<close>
    by (rule rec.IH)
  then have \<open>of_bool (odd a) + 2 * a = 2 * (a div 2) + of_bool (odd a)\<close>
    by (simp add: ac_simps)
  also have \<open>\<dots> = a\<close>
    using mult_div_mod_eq [of 2 a]
    by (simp add: of_bool_odd_eq_mod_2)
  finally show ?case
    using \<open>a div 2 = a\<close> by (simp add: hyp)
qed

lemma bit_eqI:
  \<open>a = b\<close> if \<open>\<And>n. bit a n \<longleftrightarrow> bit b n\<close>
using that proof (induction a arbitrary: b rule: bit_induct)
  case (stable a)
  from stable(2) [of 0] have **: \<open>even b \<longleftrightarrow> even a\<close>
    by simp
  have \<open>b div 2 = b\<close>
  proof (rule bit_iff_idd_imp_stable)
    fix n
    from stable have *: \<open>bit b n \<longleftrightarrow> bit a n\<close>
      by simp
    also have \<open>bit a n \<longleftrightarrow> odd a\<close>
      using stable by (simp add: stable_imp_bit_iff_odd)
    finally show \<open>bit b n \<longleftrightarrow> odd b\<close>
      by (simp add: **)
  qed
  from ** have \<open>a mod 2 = b mod 2\<close>
    by (simp add: mod2_eq_if)
  then have \<open>a mod 2 + (a + b) = b mod 2 + (a + b)\<close>
    by simp
  then have \<open>a + a mod 2 + b = b + b mod 2 + a\<close>
    by (simp add: ac_simps)
  with \<open>a div 2 = a\<close> \<open>b div 2 = b\<close> show ?case
    by (simp add: stable_imp_add_self)
next
  case (rec a p)
  from rec.prems [of 0] have [simp]: \<open>p = odd b\<close>
    by simp
  from rec.hyps have \<open>bit a n \<longleftrightarrow> bit (b div 2) n\<close> for n
    using rec.prems [of \<open>Suc n\<close>] by simp
  then have \<open>a = b div 2\<close>
    by (rule rec.IH)
  then have \<open>2 * a = 2 * (b div 2)\<close>
    by simp
  then have \<open>b mod 2 + 2 * a = b mod 2 + 2 * (b div 2)\<close>
    by simp
  also have \<open>\<dots> = b\<close>
    by (fact mod_mult_div_eq)
  finally show ?case
    by (auto simp add: mod2_eq_if)
qed

lemma bit_eq_iff:
  \<open>a = b \<longleftrightarrow> (\<forall>n. bit a n \<longleftrightarrow> bit b n)\<close>
  by (auto intro: bit_eqI)

lemma bit_eq_rec:
  \<open>a = b \<longleftrightarrow> (even a \<longleftrightarrow> even b) \<and> a div 2 = b div 2\<close>
  apply (simp add: bit_eq_iff)
  apply auto
  using bit_0 apply blast
  using bit_0 apply blast
  using bit_Suc apply blast
  using bit_Suc apply blast
     apply (metis bit_eq_iff local.even_iff_mod_2_eq_zero local.mod_div_mult_eq)
    apply (metis bit_eq_iff local.even_iff_mod_2_eq_zero local.mod_div_mult_eq)
   apply (metis bit_eq_iff local.mod2_eq_if local.mod_div_mult_eq)
  apply (metis bit_eq_iff local.mod2_eq_if local.mod_div_mult_eq)
  done

end

lemma nat_bit_induct [case_names zero even odd]:
  "P n" if zero: "P 0"
    and even: "\<And>n. P n \<Longrightarrow> n > 0 \<Longrightarrow> P (2 * n)"
    and odd: "\<And>n. P n \<Longrightarrow> P (Suc (2 * n))"
proof (induction n rule: less_induct)
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
      then have "n \<noteq> 1"
        by auto
      with \<open>n \<noteq> 0\<close> have "n div 2 > 0"
        by simp
      with \<open>even n\<close> hyp even [of "n div 2"] show ?thesis
        by simp
    next
      case False
      with hyp odd [of "n div 2"] show ?thesis
        by simp
    qed
  qed
qed

instance nat :: semiring_bits
proof
  show \<open>P n\<close> if stable: \<open>\<And>n. n div 2 = n \<Longrightarrow> P n\<close>
    and rec: \<open>\<And>n b. P n \<Longrightarrow> (of_bool b + 2 * n) div 2 = n \<Longrightarrow> P (of_bool b + 2 * n)\<close>
    for P and n :: nat
  proof (induction n rule: nat_bit_induct)
    case zero
    from stable [of 0] show ?case
      by simp
  next
    case (even n)
    with rec [of n False] show ?case
      by simp
  next
    case (odd n)
    with rec [of n True] show ?case
      by simp
  qed
  show \<open>q mod 2 ^ m mod 2 ^ n = q mod 2 ^ min m n\<close>
    for q m n :: nat
    apply (auto simp add: less_iff_Suc_add power_add mod_mod_cancel split: split_min_lin)
    apply (metis div_mult2_eq mod_div_trivial mod_eq_self_iff_div_eq_0 mod_mult_self2_is_0 power_commutes)
    done
  show \<open>(q * 2 ^ m) mod (2 ^ n) = (q mod 2 ^ (n - m)) * 2 ^ m\<close> if \<open>m \<le> n\<close>
    for q m n :: nat
    using that
    apply (auto simp add: mod_mod_cancel div_mult2_eq power_add mod_mult2_eq le_iff_add split: split_min_lin)
    apply (simp add: mult.commute)
    done
qed (auto simp add: div_mult2_eq mod_mult2_eq power_add)

lemma int_bit_induct [case_names zero minus even odd]:
  "P k" if zero_int: "P 0"
    and minus_int: "P (- 1)"
    and even_int: "\<And>k. P k \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> P (k * 2)"
    and odd_int: "\<And>k. P k \<Longrightarrow> k \<noteq> - 1 \<Longrightarrow> P (1 + (k * 2))" for k :: int
proof (cases "k \<ge> 0")
  case True
  define n where "n = nat k"
  with True have "k = int n"
    by simp
  then show "P k"
  proof (induction n arbitrary: k rule: nat_bit_induct)
    case zero
    then show ?case
      by (simp add: zero_int)
  next
    case (even n)
    have "P (int n * 2)"
      by (rule even_int) (use even in simp_all)
    with even show ?case
      by (simp add: ac_simps)
  next
    case (odd n)
    have "P (1 + (int n * 2))"
      by (rule odd_int) (use odd in simp_all)
    with odd show ?case
      by (simp add: ac_simps)
  qed
next
  case False
  define n where "n = nat (- k - 1)"
  with False have "k = - int n - 1"
    by simp
  then show "P k"
  proof (induction n arbitrary: k rule: nat_bit_induct)
    case zero
    then show ?case
      by (simp add: minus_int)
  next
    case (even n)
    have "P (1 + (- int (Suc n) * 2))"
      by (rule odd_int) (use even in \<open>simp_all add: algebra_simps\<close>)
    also have "\<dots> = - int (2 * n) - 1"
      by (simp add: algebra_simps)
    finally show ?case
      using even by simp
  next
    case (odd n)
    have "P (- int (Suc n) * 2)"
      by (rule even_int) (use odd in \<open>simp_all add: algebra_simps\<close>)
    also have "\<dots> = - int (Suc (2 * n)) - 1"
      by (simp add: algebra_simps)
    finally show ?case
      using odd by simp
  qed
qed

instance int :: semiring_bits
proof
  show \<open>P k\<close> if stable: \<open>\<And>k. k div 2 = k \<Longrightarrow> P k\<close>
    and rec: \<open>\<And>k b. P k \<Longrightarrow> (of_bool b + 2 * k) div 2 = k \<Longrightarrow> P (of_bool b + 2 * k)\<close>
    for P and k :: int
  proof (induction k rule: int_bit_induct)
    case zero
    from stable [of 0] show ?case
      by simp
  next
    case minus
    from stable [of \<open>- 1\<close>] show ?case
      by simp
  next
    case (even k)
    with rec [of k False] show ?case
      by (simp add: ac_simps)
  next
    case (odd k)
    with rec [of k True] show ?case
      by (simp add: ac_simps)
  qed
  show \<open>k mod 2 ^ m mod 2 ^ n = k mod 2 ^ min m n\<close>
    for m n :: nat and k :: int
    using mod_exp_eq [of \<open>nat k\<close> m n]
    apply (auto simp add: mod_mod_cancel zdiv_zmult2_eq power_add zmod_zmult2_eq le_iff_add split: split_min_lin)
     apply (auto simp add: less_iff_Suc_add mod_mod_cancel power_add)
    apply (simp only: flip: mult.left_commute [of \<open>2 ^ m\<close>])
    apply (subst zmod_zmult2_eq) apply simp_all
    done
  show \<open>(k * 2 ^ m) mod (2 ^ n) = (k mod 2 ^ (n - m)) * 2 ^ m\<close>
    if \<open>m \<le> n\<close> for m n :: nat and k :: int
    using that
    apply (auto simp add: power_add zmod_zmult2_eq le_iff_add split: split_min_lin)
    apply (simp add: ac_simps)
    done
qed (auto simp add: zdiv_zmult2_eq zmod_zmult2_eq power_add)

class semiring_bit_shifts = semiring_bits +
  fixes push_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes push_bit_eq_mult: \<open>push_bit n a = a * 2 ^ n\<close>
  fixes drop_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes drop_bit_eq_div: \<open>drop_bit n a = a div 2 ^ n\<close>
begin

definition take_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where take_bit_eq_mod: \<open>take_bit n a = a mod 2 ^ n\<close>

text \<open>
  Logically, \<^const>\<open>push_bit\<close>,
  \<^const>\<open>drop_bit\<close> and \<^const>\<open>take_bit\<close> are just aliases; having them
  as separate operations makes proofs easier, otherwise proof automation
  would fiddle with concrete expressions \<^term>\<open>2 ^ n\<close> in a way obfuscating the basic
  algebraic relationships between those operations.
  Having
  \<^const>\<open>push_bit\<close> and \<^const>\<open>drop_bit\<close> as definitional class operations
  takes into account that specific instances of these can be implemented
  differently wrt. code generation.
\<close>

lemma bit_ident:
  "push_bit n (drop_bit n a) + take_bit n a = a"
  using div_mult_mod_eq by (simp add: push_bit_eq_mult take_bit_eq_mod drop_bit_eq_div)

lemma push_bit_push_bit [simp]:
  "push_bit m (push_bit n a) = push_bit (m + n) a"
  by (simp add: push_bit_eq_mult power_add ac_simps)

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

lemma push_bit_add:
  "push_bit n (a + b) = push_bit n a + push_bit n b"
  by (simp add: push_bit_eq_mult algebra_simps)

lemma take_bit_0 [simp]:
  "take_bit 0 a = 0"
  by (simp add: take_bit_eq_mod)

lemma take_bit_Suc [simp]:
  \<open>take_bit (Suc n) a = take_bit n (a div 2) * 2 + of_bool (odd a)\<close>
proof -
  have \<open>take_bit (Suc n) (a div 2 * 2 + of_bool (odd a)) = take_bit n (a div 2) * 2 + of_bool (odd a)\<close>
    using even_succ_mod_exp [of \<open>2 * (a div 2)\<close> \<open>Suc n\<close>]
      mult_exp_mod_exp_eq [of 1 \<open>Suc n\<close> \<open>a div 2\<close>]
    by (auto simp add: take_bit_eq_mod ac_simps)
  then show ?thesis
    using div_mult_mod_eq [of a 2] by (simp add: mod_2_eq_odd)
qed

lemma take_bit_of_0 [simp]:
  "take_bit n 0 = 0"
  by (simp add: take_bit_eq_mod)

lemma take_bit_of_1 [simp]:
  "take_bit n 1 = of_bool (n > 0)"
  by (cases n) simp_all

lemma drop_bit_of_0 [simp]:
  "drop_bit n 0 = 0"
  by (simp add: drop_bit_eq_div)

lemma drop_bit_of_1 [simp]:
  "drop_bit n 1 = of_bool (n = 0)"
  by (simp add: drop_bit_eq_div)

lemma drop_bit_0 [simp]:
  "drop_bit 0 = id"
  by (simp add: fun_eq_iff drop_bit_eq_div)

lemma drop_bit_Suc [simp]:
  "drop_bit (Suc n) a = drop_bit n (a div 2)"
  using div_exp_eq [of a 1] by (simp add: drop_bit_eq_div)

lemma drop_bit_half:
  "drop_bit n (a div 2) = drop_bit n a div 2"
  by (induction n arbitrary: a) simp_all

lemma drop_bit_of_bool [simp]:
  "drop_bit n (of_bool d) = of_bool (n = 0 \<and> d)"
  by (cases n) simp_all

lemma take_bit_eq_0_imp_dvd:
  "take_bit n a = 0 \<Longrightarrow> 2 ^ n dvd a"
  by (simp add: take_bit_eq_mod mod_0_imp_dvd)

lemma even_take_bit_eq [simp]:
  \<open>even (take_bit n a) \<longleftrightarrow> n = 0 \<or> even a\<close>
  by (cases n) simp_all

lemma take_bit_take_bit [simp]:
  "take_bit m (take_bit n a) = take_bit (min m n) a"
  by (simp add: take_bit_eq_mod mod_exp_eq ac_simps)

lemma drop_bit_drop_bit [simp]:
  "drop_bit m (drop_bit n a) = drop_bit (m + n) a"
  by (simp add: drop_bit_eq_div power_add div_exp_eq ac_simps)

lemma push_bit_take_bit:
  "push_bit m (take_bit n a) = take_bit (m + n) (push_bit m a)"
  apply (simp add: push_bit_eq_mult take_bit_eq_mod power_add ac_simps)
  using mult_exp_mod_exp_eq [of m \<open>m + n\<close> a] apply (simp add: ac_simps power_add)
  done

lemma take_bit_push_bit:
  "take_bit m (push_bit n a) = push_bit n (take_bit (m - n) a)"
proof (cases "m \<le> n")
  case True
  then show ?thesis
    apply (simp add:)
    apply (simp_all add: push_bit_eq_mult take_bit_eq_mod)
    apply (auto dest!: le_Suc_ex simp add: power_add ac_simps)
    using mult_exp_mod_exp_eq [of m m \<open>a * 2 ^ n\<close> for n]
    apply (simp add: ac_simps)
    done
next
  case False
  then show ?thesis
    using push_bit_take_bit [of n "m - n" a]
    by simp
qed

lemma take_bit_drop_bit:
  "take_bit m (drop_bit n a) = drop_bit n (take_bit (m + n) a)"
  by (simp add: drop_bit_eq_div take_bit_eq_mod ac_simps div_exp_mod_exp_eq)

lemma drop_bit_take_bit:
  "drop_bit m (take_bit n a) = take_bit (n - m) (drop_bit m a)"
proof (cases "m \<le> n")
  case True
  then show ?thesis
    using take_bit_drop_bit [of "n - m" m a] by simp
next
  case False
  then obtain q where \<open>m = n + q\<close>
    by (auto simp add: not_le dest: less_imp_Suc_add)
  then have \<open>drop_bit m (take_bit n a) = 0\<close>
    using div_exp_eq [of \<open>a mod 2 ^ n\<close> n q]
    by (simp add: take_bit_eq_mod drop_bit_eq_div)
  with False show ?thesis
    by simp
qed

lemma bit_drop_bit_eq:
  \<open>bit (drop_bit n a) = bit a \<circ> (+) n\<close>
  by (simp add: bit_def fun_eq_iff ac_simps flip: drop_bit_eq_div)

lemma bit_take_bit_iff:
  \<open>bit (take_bit m a) n \<longleftrightarrow> n < m \<and> bit a n\<close>
  by (simp add: bit_def drop_bit_take_bit not_le flip: drop_bit_eq_div)

end

instantiation nat :: semiring_bit_shifts
begin

definition push_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>push_bit_nat n m = m * 2 ^ n\<close>

definition drop_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>drop_bit_nat n m = m div 2 ^ n\<close>

instance proof
  show \<open>push_bit n m = m * 2 ^ n\<close> for n m :: nat
    by (simp add: push_bit_nat_def)
  show \<open>drop_bit n m = m div 2 ^ n\<close> for n m :: nat
    by (simp add: drop_bit_nat_def)
qed

end

instantiation int :: semiring_bit_shifts
begin

definition push_bit_int :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>push_bit_int n k = k * 2 ^ n\<close>

definition drop_bit_int :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>drop_bit_int n k = k div 2 ^ n\<close>

instance proof
  show \<open>push_bit n k = k * 2 ^ n\<close> for n :: nat and k :: int
    by (simp add: push_bit_int_def)
  show \<open>drop_bit n k = k div 2 ^ n\<close> for n :: nat and k :: int
    by (simp add: drop_bit_int_def)
qed

end

class unique_euclidean_semiring_with_bit_shifts =
  unique_euclidean_semiring_with_nat + semiring_bit_shifts
begin

lemma take_bit_of_exp [simp]:
  \<open>take_bit m (2 ^ n) = of_bool (n < m) * 2 ^ n\<close>
  by (simp add: take_bit_eq_mod exp_mod_exp)

lemma take_bit_of_2 [simp]:
  \<open>take_bit n 2 = of_bool (2 \<le> n) * 2\<close>
  using take_bit_of_exp [of n 1] by simp

lemma push_bit_eq_0_iff [simp]:
  "push_bit n a = 0 \<longleftrightarrow> a = 0"
  by (simp add: push_bit_eq_mult)

lemma push_bit_numeral [simp]:
  "push_bit (numeral l) (numeral k) = push_bit (pred_numeral l) (numeral (Num.Bit0 k))"
  by (simp only: numeral_eq_Suc power_Suc numeral_Bit0 [of k] mult_2 [symmetric]) (simp add: ac_simps)

lemma push_bit_of_nat:
  "push_bit n (of_nat m) = of_nat (push_bit n m)"
  by (simp add: push_bit_eq_mult Parity.push_bit_eq_mult)

lemma take_bit_add:
  "take_bit n (take_bit n a + take_bit n b) = take_bit n (a + b)"
  by (simp add: take_bit_eq_mod mod_simps)

lemma take_bit_eq_0_iff:
  "take_bit n a = 0 \<longleftrightarrow> 2 ^ n dvd a"
  by (simp add: take_bit_eq_mod mod_eq_0_iff_dvd)

lemma take_bit_of_1_eq_0_iff [simp]:
  "take_bit n 1 = 0 \<longleftrightarrow> n = 0"
  by (simp add: take_bit_eq_mod)

lemma take_bit_numeral_bit0 [simp]:
  "take_bit (numeral l) (numeral (Num.Bit0 k)) = take_bit (pred_numeral l) (numeral k) * 2"
  by (simp only: numeral_eq_Suc power_Suc numeral_Bit0 [of k] mult_2 [symmetric] take_bit_Suc
    ac_simps even_mult_iff nonzero_mult_div_cancel_right [OF numeral_neq_zero]) simp

lemma take_bit_numeral_bit1 [simp]:
  "take_bit (numeral l) (numeral (Num.Bit1 k)) = take_bit (pred_numeral l) (numeral k) * 2 + 1"
  by (simp only: numeral_eq_Suc power_Suc numeral_Bit1 [of k] mult_2 [symmetric] take_bit_Suc
    ac_simps even_add even_mult_iff div_mult_self1 [OF numeral_neq_zero]) (simp add: ac_simps)

lemma take_bit_of_nat:
  "take_bit n (of_nat m) = of_nat (take_bit n m)"
  by (simp add: take_bit_eq_mod Parity.take_bit_eq_mod of_nat_mod [of m "2 ^ n"])

lemma drop_bit_numeral_bit0 [simp]:
  "drop_bit (numeral l) (numeral (Num.Bit0 k)) = drop_bit (pred_numeral l) (numeral k)"
  by (simp only: numeral_eq_Suc power_Suc numeral_Bit0 [of k] mult_2 [symmetric] drop_bit_Suc
    nonzero_mult_div_cancel_left [OF numeral_neq_zero])

lemma drop_bit_numeral_bit1 [simp]:
  "drop_bit (numeral l) (numeral (Num.Bit1 k)) = drop_bit (pred_numeral l) (numeral k)"
  by (simp only: numeral_eq_Suc power_Suc numeral_Bit1 [of k] mult_2 [symmetric] drop_bit_Suc
    div_mult_self4 [OF numeral_neq_zero]) simp

lemma drop_bit_of_nat:
  "drop_bit n (of_nat m) = of_nat (drop_bit n m)"
  by (simp add: drop_bit_eq_div Parity.drop_bit_eq_div of_nat_div [of m "2 ^ n"])

end

instance nat :: unique_euclidean_semiring_with_bit_shifts ..

instance int :: unique_euclidean_semiring_with_bit_shifts ..

lemma push_bit_of_Suc_0 [simp]:
  "push_bit n (Suc 0) = 2 ^ n"
  using push_bit_of_1 [where ?'a = nat] by simp

lemma take_bit_of_Suc_0 [simp]:
  "take_bit n (Suc 0) = of_bool (0 < n)"
  using take_bit_of_1 [where ?'a = nat] by simp

lemma drop_bit_of_Suc_0 [simp]:
  "drop_bit n (Suc 0) = of_bool (n = 0)"
  using drop_bit_of_1 [where ?'a = nat] by simp

lemma take_bit_eq_self:
  \<open>take_bit n m = m\<close> if \<open>m < 2 ^ n\<close> for n m :: nat
  using that by (simp add: take_bit_eq_mod)

lemma push_bit_minus_one:
  "push_bit n (- 1 :: int) = - (2 ^ n)"
  by (simp add: push_bit_eq_mult)

end
