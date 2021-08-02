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

lemma even_mod_2_iff [simp]:
  \<open>even (a mod 2) \<longleftrightarrow> even a\<close>
  by (simp add: mod_2_eq_odd)

lemma mod2_eq_if:
  "a mod 2 = (if even a then 0 else 1)"
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

lemma odd_numeral_BitM [simp]:
  \<open>odd (numeral (Num.BitM w))\<close>
  by (cases w) simp_all

lemma even_power [simp]: "even (a ^ n) \<longleftrightarrow> even a \<and> n > 0"
  by (induct n) auto

lemma mask_eq_sum_exp:
  \<open>2 ^ n - 1 = (\<Sum>m\<in>{q. q < n}. 2 ^ m)\<close>
proof -
  have *: \<open>{q. q < Suc m} = insert m {q. q < m}\<close> for m
    by auto
  have \<open>2 ^ n = (\<Sum>m\<in>{q. q < n}. 2 ^ m) + 1\<close>
    by (induction n) (simp_all add: ac_simps mult_2 *)
  then have \<open>2 ^ n - 1 = (\<Sum>m\<in>{q. q < n}. 2 ^ m) + 1 - 1\<close>
    by simp
  then show ?thesis
    by simp
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

lemma mask_eq_sum_exp_nat:
  \<open>2 ^ n - Suc 0 = (\<Sum>m\<in>{q. q < n}. 2 ^ m)\<close>
  using mask_eq_sum_exp [where ?'a = nat] by simp

context semiring_parity
begin

lemma even_sum_iff:
  \<open>even (sum f A) \<longleftrightarrow> even (card {a\<in>A. odd (f a)})\<close> if \<open>finite A\<close>
using that proof (induction A)
  case empty
  then show ?case
    by simp
next
  case (insert a A)
  moreover have \<open>{b \<in> insert a A. odd (f b)} = (if odd (f a) then {a} else {}) \<union> {b \<in> A. odd (f b)}\<close>
    by auto
  ultimately show ?case
    by simp
qed

lemma even_prod_iff:
  \<open>even (prod f A) \<longleftrightarrow> (\<exists>a\<in>A. even (f a))\<close> if \<open>finite A\<close>
  using that by (induction A) simp_all

lemma even_mask_iff [simp]:
  \<open>even (2 ^ n - 1) \<longleftrightarrow> n = 0\<close>
proof (cases \<open>n = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  then have \<open>{a. a = 0 \<and> a < n} = {0}\<close>
    by auto
  then show ?thesis
    by (auto simp add: mask_eq_sum_exp even_sum_iff)
qed

end


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

context unique_euclidean_semiring_with_nat
begin

lemma even_mask_div_iff':
  \<open>even ((2 ^ m - 1) div 2 ^ n) \<longleftrightarrow> m \<le> n\<close>
proof -
  have \<open>even ((2 ^ m - 1) div 2 ^ n) \<longleftrightarrow> even (of_nat ((2 ^ m - Suc 0) div 2 ^ n))\<close>
    by (simp only: of_nat_div) (simp add: of_nat_diff)
  also have \<open>\<dots> \<longleftrightarrow> even ((2 ^ m - Suc 0) div 2 ^ n)\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> m \<le> n\<close>
  proof (cases \<open>m \<le> n\<close>)
    case True
    then show ?thesis
      by (simp add: Suc_le_lessD)
  next
    case False
    then obtain r where r: \<open>m = n + Suc r\<close>
      using less_imp_Suc_add by fastforce
    from r have \<open>{q. q < m} \<inter> {q. 2 ^ n dvd (2::nat) ^ q} = {q. n \<le> q \<and> q < m}\<close>
      by (auto simp add: dvd_power_iff_le)
    moreover from r have \<open>{q. q < m} \<inter> {q. \<not> 2 ^ n dvd (2::nat) ^ q} = {q. q < n}\<close>
      by (auto simp add: dvd_power_iff_le)
    moreover from False have \<open>{q. n \<le> q \<and> q < m \<and> q \<le> n} = {n}\<close>
      by auto
    then have \<open>odd ((\<Sum>a\<in>{q. n \<le> q \<and> q < m}. 2 ^ a div (2::nat) ^ n) + sum ((^) 2) {q. q < n} div 2 ^ n)\<close>
      by (simp_all add: euclidean_semiring_cancel_class.power_diff_power_eq semiring_parity_class.even_sum_iff not_less mask_eq_sum_exp_nat [symmetric])
    ultimately have \<open>odd (sum ((^) (2::nat)) {q. q < m} div 2 ^ n)\<close>
      by (subst euclidean_semiring_cancel_class.sum_div_partition) simp_all
    with False show ?thesis
      by (simp add: mask_eq_sum_exp_nat)
  qed
  finally show ?thesis .
qed

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

context
  assumes "SORT_CONSTRAINT('a::division_ring)"
begin

lemma power_int_minus_left:
  "power_int (-a :: 'a) n = (if even n then power_int a n else -power_int a n)"
  by (auto simp: power_int_def minus_one_power_iff even_nat_iff)

lemma power_int_minus_left_even [simp]: "even n \<Longrightarrow> power_int (-a :: 'a) n = power_int a n"
  by (simp add: power_int_minus_left)

lemma power_int_minus_left_odd [simp]: "odd n \<Longrightarrow> power_int (-a :: 'a) n = -power_int a n"
  by (simp add: power_int_minus_left)

lemma power_int_minus_left_distrib:
  "NO_MATCH (-1) x \<Longrightarrow> power_int (-a :: 'a) n = power_int (-1) n * power_int a n"
  by (simp add: power_int_minus_left)

lemma power_int_minus_one_minus: "power_int (-1 :: 'a) (-n) = power_int (-1) n"
  by (simp add: power_int_minus_left)

lemma power_int_minus_one_diff_commute: "power_int (-1 :: 'a) (a - b) = power_int (-1) (b - a)"
  by (subst power_int_minus_one_minus [symmetric]) auto

lemma power_int_minus_one_mult_self [simp]:
  "power_int (-1 :: 'a) m * power_int (-1) m = 1"
  by (simp add: power_int_minus_left)

lemma power_int_minus_one_mult_self' [simp]:
  "power_int (-1 :: 'a) m * (power_int (-1) m * b) = b"
  by (simp add: power_int_minus_left)

end

code_identifier
  code_module Parity \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
