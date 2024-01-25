(*  Title:      HOL/Parity.thy
    Author:     Jeremy Avigad
    Author:     Jacques D. Fleuriot
*)

section \<open>Parity in rings and semirings\<close>

theory Parity
  imports Euclidean_Rings
begin

subsection \<open>Ring structures with parity and \<open>even\<close>/\<open>odd\<close> predicates\<close>

class semiring_parity = comm_semiring_1 + semiring_modulo +
  assumes mod_2_eq_odd: \<open>a mod 2 = of_bool (\<not> 2 dvd a)\<close>
    and odd_one [simp]: \<open>\<not> 2 dvd 1\<close>
begin

abbreviation even :: "'a \<Rightarrow> bool"
  where \<open>even a \<equiv> 2 dvd a\<close>

abbreviation odd :: "'a \<Rightarrow> bool"
  where \<open>odd a \<equiv> \<not> 2 dvd a\<close>

end

class ring_parity = ring + semiring_parity
begin

subclass comm_ring_1 ..

end

instance nat :: semiring_parity
  by standard (simp_all add: dvd_eq_mod_eq_0)

instance int :: ring_parity
  by standard (auto simp add: dvd_eq_mod_eq_0)

context semiring_parity
begin

lemma evenE [elim?]:
  assumes \<open>even a\<close>
  obtains b where \<open>a = 2 * b\<close>
  using assms by (rule dvdE)

lemma oddE [elim?]:
  assumes \<open>odd a\<close>
  obtains b where \<open>a = 2 * b + 1\<close>
proof -
  have \<open>a = 2 * (a div 2) + a mod 2\<close>
    by (simp add: mult_div_mod_eq)
  with assms have \<open>a = 2 * (a div 2) + 1\<close>
    by (simp add: mod_2_eq_odd)
  then show thesis ..
qed

lemma of_bool_odd_eq_mod_2:
  \<open>of_bool (odd a) = a mod 2\<close>
  by (simp add: mod_2_eq_odd)

lemma odd_of_bool_self [simp]:
  \<open>odd (of_bool p) \<longleftrightarrow> p\<close>
  by (cases p) simp_all

lemma not_mod_2_eq_0_eq_1 [simp]:
  \<open>a mod 2 \<noteq> 0 \<longleftrightarrow> a mod 2 = 1\<close>
  by (simp add: mod_2_eq_odd)

lemma not_mod_2_eq_1_eq_0 [simp]:
  \<open>a mod 2 \<noteq> 1 \<longleftrightarrow> a mod 2 = 0\<close>
  by (simp add: mod_2_eq_odd)

lemma even_iff_mod_2_eq_zero:
  \<open>2 dvd a \<longleftrightarrow> a mod 2 = 0\<close>
  by (simp add: mod_2_eq_odd)

lemma odd_iff_mod_2_eq_one:
  \<open>\<not> 2 dvd a \<longleftrightarrow> a mod 2 = 1\<close>
  by (simp add: mod_2_eq_odd)

lemma even_mod_2_iff [simp]:
  \<open>even (a mod 2) \<longleftrightarrow> even a\<close>
  by (simp add: mod_2_eq_odd)

lemma mod2_eq_if:
  "a mod 2 = (if even a then 0 else 1)"
  by (simp add: mod_2_eq_odd)

lemma zero_mod_two_eq_zero [simp]:
  \<open>0 mod 2 = 0\<close>
  by (simp add: mod_2_eq_odd)

lemma one_mod_two_eq_one [simp]:
  \<open>1 mod 2 = 1\<close>
  by (simp add: mod_2_eq_odd)

lemma parity_cases [case_names even odd]:
  assumes \<open>even a \<Longrightarrow> a mod 2 = 0 \<Longrightarrow> P\<close>
  assumes \<open>odd a \<Longrightarrow> a mod 2 = 1 \<Longrightarrow> P\<close>
  shows P
  using assms by (auto simp add: mod_2_eq_odd)

lemma even_zero [simp]:
  \<open>even 0\<close>
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

lemma even_prod_iff:
  \<open>even (prod f A) \<longleftrightarrow> (\<exists>a\<in>A. even (f a))\<close> if \<open>finite A\<close>
  using that by (induction A) simp_all

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

lemma (in -) mask_eq_sum_exp_nat:
  \<open>2 ^ n - Suc 0 = (\<Sum>m\<in>{q. q < n}. 2 ^ m)\<close>
  using mask_eq_sum_exp [where ?'a = nat] by simp

end

context ring_parity
begin

lemma even_minus:
  "even (- a) \<longleftrightarrow> even a"
  by (fact dvd_minus_iff)

lemma even_diff [simp]:
  "even (a - b) \<longleftrightarrow> even (a + b)"
  using even_add [of a "- b"] by simp

end


subsection \<open>Instance for \<^typ>\<open>nat\<close>\<close>

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
  by auto

lemma odd_Suc_div_two [simp]:
  "odd n \<Longrightarrow> Suc n div 2 = Suc (n div 2)"
  by (auto elim: oddE)

lemma odd_two_times_div_two_nat [simp]:
  assumes "odd n"
  shows "2 * (n div 2) = n - (1 :: nat)"
proof -
  from assms have "2 * (n div 2) + 1 = n"
    by (auto elim: oddE)
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

lemma mod_double_nat:
  \<open>n mod (2 * m) = n mod m \<or> n mod (2 * m) = n mod m + m\<close>
  for m n :: nat
  by (cases \<open>even (n div m)\<close>)
    (simp_all add: mod_mult2_eq ac_simps even_iff_mod_2_eq_zero)

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

lemma even_of_nat_iff [simp]:
  "even (of_nat n) \<longleftrightarrow> even n"
  by (induction n) simp_all

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
  by (simp add: even_of_nat_iff [of "nat k", where ?'a = int, symmetric])

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


subsection \<open>Special case: euclidean rings structurally containing the natural numbers\<close>

class linordered_euclidean_semiring = discrete_linordered_semidom + unique_euclidean_semiring +
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
      by auto
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

lemma div_mult2_eq':
  \<open>a div (of_nat m * of_nat n) = a div of_nat m div of_nat n\<close>
proof (cases \<open>m = 0 \<or> n = 0\<close>)
  case True
  then show ?thesis
    by auto
next
  case False
  then have \<open>m > 0\<close> \<open>n > 0\<close>
    by simp_all
  show ?thesis
  proof (cases \<open>of_nat m * of_nat n dvd a\<close>)
    case True
    then obtain b where \<open>a = (of_nat m * of_nat n) * b\<close> ..
    then have \<open>a = of_nat m * (of_nat n * b)\<close>
      by (simp add: ac_simps)
    then show ?thesis
      by simp
  next
    case False
    define q where \<open>q = a div (of_nat m * of_nat n)\<close>
    define r where \<open>r = a mod (of_nat m * of_nat n)\<close>
    from \<open>m > 0\<close> \<open>n > 0\<close> \<open>\<not> of_nat m * of_nat n dvd a\<close> r_def have "division_segment r = 1"
      using division_segment_of_nat [of "m * n"] by (simp add: division_segment_mod)
    with division_segment_euclidean_size [of r]
    have "of_nat (euclidean_size r) = r"
      by simp
    have "a mod (of_nat m * of_nat n) div (of_nat m * of_nat n) = 0"
      by simp
    with \<open>m > 0\<close> \<open>n > 0\<close> r_def have "r div (of_nat m * of_nat n) = 0"
      by simp
    with \<open>of_nat (euclidean_size r) = r\<close>
    have "of_nat (euclidean_size r) div (of_nat m * of_nat n) = 0"
      by simp
    then have "of_nat (euclidean_size r div (m * n)) = 0"
      by (simp add: of_nat_div)
    then have "of_nat (euclidean_size r div m div n) = 0"
      by (simp add: div_mult2_eq)
    with \<open>of_nat (euclidean_size r) = r\<close> have "r div of_nat m div of_nat n = 0"
      by (simp add: of_nat_div)
    with \<open>m > 0\<close> \<open>n > 0\<close> q_def
    have "q = (r div of_nat m + q * of_nat n * of_nat m div of_nat m) div of_nat n"
      by simp
    moreover have \<open>a = q * (of_nat m * of_nat n) + r\<close>
      by (simp add: q_def r_def div_mult_mod_eq)
    ultimately show \<open>a div (of_nat m * of_nat n) = a div of_nat m div of_nat n\<close>
      using q_def [symmetric] div_plus_div_distrib_dvd_right [of \<open>of_nat m\<close> \<open>q * (of_nat m * of_nat n)\<close> r]
      by (simp add: ac_simps)
  qed
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

lemma div_mult2_numeral_eq:
  "a div numeral k div numeral l = a div numeral (k * l)" (is "?A = ?B")
proof -
  have "?A = a div of_nat (numeral k) div of_nat (numeral l)"
    by simp
  also have "\<dots> = a div (of_nat (numeral k) * of_nat (numeral l))"
    by (fact div_mult2_eq' [symmetric])
  also have "\<dots> = ?B"
    by simp
  finally show ?thesis .
qed

lemma numeral_Bit0_div_2:
  "numeral (num.Bit0 n) div 2 = numeral n"
proof -
  have "numeral (num.Bit0 n) = numeral n + numeral n"
    by (simp only: numeral.simps)
  also have "\<dots> = numeral n * 2"
    by (simp add: mult_2_right)
  finally have "numeral (num.Bit0 n) div 2 = numeral n * 2 div 2"
    by simp
  also have "\<dots> = numeral n"
    by (rule nonzero_mult_div_cancel_right) simp
  finally show ?thesis .
qed

lemma numeral_Bit1_div_2:
  "numeral (num.Bit1 n) div 2 = numeral n"
proof -
  have "numeral (num.Bit1 n) = numeral n + numeral n + 1"
    by (simp only: numeral.simps)
  also have "\<dots> = numeral n * 2 + 1"
    by (simp add: mult_2_right)
  finally have "numeral (num.Bit1 n) div 2 = (numeral n * 2 + 1) div 2"
    by simp
  also have "\<dots> = numeral n * 2 div 2 + 1 div 2"
    using dvd_triv_right by (rule div_plus_div_distrib_dvd_left)
  also have "\<dots> = numeral n * 2 div 2"
    by simp
  also have "\<dots> = numeral n"
    by (rule nonzero_mult_div_cancel_right) simp
  finally show ?thesis .
qed

lemma exp_mod_exp:
  \<open>2 ^ m mod 2 ^ n = of_bool (m < n) * 2 ^ m\<close>
proof -
  have \<open>(2::nat) ^ m mod 2 ^ n = of_bool (m < n) * 2 ^ m\<close> (is \<open>?lhs = ?rhs\<close>)
    by (auto simp add: linorder_class.not_less monoid_mult_class.power_add dest!: le_Suc_ex)
  then have \<open>of_nat ?lhs = of_nat ?rhs\<close>
    by simp
  then show ?thesis
    by (simp add: of_nat_mod)
qed

lemma mask_mod_exp:
  \<open>(2 ^ n - 1) mod 2 ^ m = 2 ^ min m n - 1\<close>
proof -
  have \<open>(2 ^ n - 1) mod 2 ^ m = 2 ^ min m n - (1::nat)\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (cases \<open>n \<le> m\<close>)
    case True
    then show ?thesis
      by (simp add: Suc_le_lessD)
  next
    case False
    then have \<open>m < n\<close>
      by simp
    then obtain q where n: \<open>n = Suc q + m\<close>
      by (auto dest: less_imp_Suc_add)
    then have \<open>min m n = m\<close>
      by simp
    moreover have \<open>(2::nat) ^ m \<le> 2 * 2 ^ q * 2 ^ m\<close>
      using mult_le_mono1 [of 1 \<open>2 * 2 ^ q\<close> \<open>2 ^ m\<close>] by simp
    with n have \<open>2 ^ n - 1 = (2 ^ Suc q - 1) * 2 ^ m + (2 ^ m - (1::nat))\<close>
      by (simp add: monoid_mult_class.power_add algebra_simps)
    ultimately show ?thesis
      by (simp only: euclidean_semiring_cancel_class.mod_mult_self3) simp
  qed
  then have \<open>of_nat ?lhs = of_nat ?rhs\<close>
    by simp
  then show ?thesis
    by (simp add: of_nat_mod of_nat_diff)
qed

lemma of_bool_half_eq_0 [simp]:
  \<open>of_bool b div 2 = 0\<close>
  by simp

lemma of_nat_mod_double:
  \<open>of_nat n mod (2 * of_nat m) = of_nat n mod of_nat m \<or> of_nat n mod (2 * of_nat m) = of_nat n mod of_nat m + of_nat m\<close>
  by (simp add: mod_double_nat flip: of_nat_mod of_nat_add of_nat_mult of_nat_numeral)

end

instance nat :: linordered_euclidean_semiring
  by standard simp_all

instance int :: linordered_euclidean_semiring
  by standard (auto simp add: divide_int_def division_segment_int_def elim: contrapos_np)

context linordered_euclidean_semiring
begin

subclass semiring_parity
proof
  show \<open>a mod 2 = of_bool (\<not> 2 dvd a)\<close> for a
  proof (cases \<open>2 dvd a\<close>)
    case True
    then show ?thesis
      by (simp add: dvd_eq_mod_eq_0)
  next
    case False
    have eucl: "euclidean_size (a mod 2) = 1"
    proof (rule Orderings.order_antisym)
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
    have "a mod 2 = 1"
      by (auto intro: division_segment_eq_iff simp add: division_segment_mod)
    with \<open>\<not> 2 dvd a\<close> show ?thesis
      by simp
  qed
  show \<open>\<not> is_unit 2\<close>
  proof
    assume \<open>is_unit 2\<close>
    then have \<open>of_nat 2 dvd of_nat 1\<close>
      by simp
    then have \<open>is_unit (2::nat)\<close>
      by (simp only: of_nat_dvd_iff)
    then show False
      by simp
  qed
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

lemma minus_1_mod_2_eq [simp]:
  \<open>- 1 mod 2 = (1::int)\<close>
  by (simp add: mod_2_eq_odd)

lemma minus_1_div_2_eq [simp]:
  "- 1 div 2 = - (1::int)"
proof -
  from div_mult_mod_eq [of "- 1 :: int" 2]
  have "- 1 div 2 * 2 = - 1 * (2 :: int)"
    using add_implies_diff by fastforce
  then show ?thesis
    using mult_right_cancel [of 2 "- 1 div 2" "- (1 :: int)"] by simp
qed

context linordered_euclidean_semiring
begin

lemma even_decr_exp_div_exp_iff':
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
      by (simp_all add: euclidean_semiring_cancel_class.power_diff_power_eq semiring_parity_class.even_sum_iff
        linorder_class.not_less mask_eq_sum_exp_nat [symmetric])
    ultimately have \<open>odd (sum ((^) (2::nat)) {q. q < m} div 2 ^ n)\<close>
      by (subst euclidean_semiring_cancel_class.sum_div_partition) simp_all
    with False show ?thesis
      by (simp add: mask_eq_sum_exp_nat)
  qed
  finally show ?thesis .
qed

end


subsection \<open>Generic symbolic computations\<close>

text \<open>
  The following type class contains everything necessary to formulate
  a division algorithm in ring structures with numerals, restricted
  to its positive segments.
\<close>

class linordered_euclidean_semiring_division = linordered_euclidean_semiring +
  fixes divmod :: \<open>num \<Rightarrow> num \<Rightarrow> 'a \<times> 'a\<close>
    and divmod_step :: \<open>'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a\<close> \<comment> \<open>
      These are conceptually definitions but force generated code
      to be monomorphic wrt. particular instances of this class which
      yields a significant speedup.\<close>
  assumes divmod_def: \<open>divmod m n = (numeral m div numeral n, numeral m mod numeral n)\<close>
    and divmod_step_def [simp]: \<open>divmod_step l (q, r) =
      (if euclidean_size l \<le> euclidean_size r then (2 * q + 1, r - l)
       else (2 * q, r))\<close> \<comment> \<open>
         This is a formulation of one step (referring to one digit position)
         in school-method division: compare the dividend at the current
         digit position with the remainder from previous division steps
         and evaluate accordingly.\<close>
begin

lemma fst_divmod:
  \<open>fst (divmod m n) = numeral m div numeral n\<close>
  by (simp add: divmod_def)

lemma snd_divmod:
  \<open>snd (divmod m n) = numeral m mod numeral n\<close>
  by (simp add: divmod_def)

text \<open>
  Following a formulation of school-method division.
  If the divisor is smaller than the dividend, terminate.
  If not, shift the dividend to the right until termination
  occurs and then reiterate single division steps in the
  opposite direction.
\<close>

lemma divmod_divmod_step:
  \<open>divmod m n = (if m < n then (0, numeral m)
    else divmod_step (numeral n) (divmod m (Num.Bit0 n)))\<close>
proof (cases \<open>m < n\<close>)
  case True
  then show ?thesis
    by (simp add: prod_eq_iff fst_divmod snd_divmod flip: of_nat_numeral of_nat_div of_nat_mod)
next
  case False
  define r s t where \<open>r = (numeral m :: nat)\<close> \<open>s = (numeral n :: nat)\<close> \<open>t = 2 * s\<close>
  then have *: \<open>numeral m = of_nat r\<close> \<open>numeral n = of_nat s\<close> \<open>numeral (num.Bit0 n) = of_nat t\<close>
    and \<open>\<not> s \<le> r mod s\<close>
    by (simp_all add: linorder_class.not_le)
  have t: \<open>2 * (r div t) = r div s - r div s mod 2\<close>
    \<open>r mod t = s * (r div s mod 2) + r mod s\<close>
    by (simp add: Rings.minus_mod_eq_mult_div Groups.mult.commute [of 2] Euclidean_Rings.div_mult2_eq \<open>t = 2 * s\<close>)
      (use mod_mult2_eq [of r s 2] in \<open>simp add: ac_simps \<open>t = 2 * s\<close>\<close>)
  have rs: \<open>r div s mod 2 = 0 \<or> r div s mod 2 = Suc 0\<close>
    by auto
  from \<open>\<not> s \<le> r mod s\<close> have \<open>s \<le> r mod t \<Longrightarrow>
     r div s = Suc (2 * (r div t)) \<and>
     r mod s = r mod t - s\<close>
    using rs
    by (auto simp add: t)
  moreover have \<open>r mod t < s \<Longrightarrow>
     r div s = 2 * (r div t) \<and>
     r mod s = r mod t\<close>
    using rs
    by (auto simp add: t)
  ultimately show ?thesis
    by (simp add: divmod_def prod_eq_iff split_def Let_def
        not_less mod_eq_0_iff_dvd Rings.mod_eq_0_iff_dvd False not_le *)
    (simp add: flip: of_nat_numeral of_nat_mult add.commute [of 1] of_nat_div of_nat_mod of_nat_Suc of_nat_diff)
qed

text \<open>The division rewrite proper -- first, trivial results involving \<open>1\<close>\<close>

lemma divmod_trivial [simp]:
  "divmod m Num.One = (numeral m, 0)"
  "divmod num.One (num.Bit0 n) = (0, Numeral1)"
  "divmod num.One (num.Bit1 n) = (0, Numeral1)"
  using divmod_divmod_step [of "Num.One"] by (simp_all add: divmod_def)

text \<open>Division by an even number is a right-shift\<close>

lemma divmod_cancel [simp]:
  \<open>divmod (Num.Bit0 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r))\<close> (is ?P)
  \<open>divmod (Num.Bit1 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r + 1))\<close> (is ?Q)
proof -
  define r s where \<open>r = (numeral m :: nat)\<close> \<open>s = (numeral n :: nat)\<close>
  then have *: \<open>numeral m = of_nat r\<close> \<open>numeral n = of_nat s\<close>
    \<open>numeral (num.Bit0 m) = of_nat (2 * r)\<close> \<open>numeral (num.Bit0 n) = of_nat (2 * s)\<close>
    \<open>numeral (num.Bit1 m) = of_nat (Suc (2 * r))\<close>
    by simp_all
  have **: \<open>Suc (2 * r) div 2 = r\<close>
    by simp
  show ?P and ?Q
    by (simp_all add: divmod_def *)
      (simp_all flip: of_nat_numeral of_nat_div of_nat_mod of_nat_mult add.commute [of 1] of_nat_Suc
       add: Euclidean_Rings.mod_mult_mult1 div_mult2_eq [of _ 2] mod_mult2_eq [of _ 2] **)
qed

text \<open>The really hard work\<close>

lemma divmod_steps [simp]:
  "divmod (num.Bit0 m) (num.Bit1 n) =
      (if m \<le> n then (0, numeral (num.Bit0 m))
       else divmod_step (numeral (num.Bit1 n))
             (divmod (num.Bit0 m)
               (num.Bit0 (num.Bit1 n))))"
  "divmod (num.Bit1 m) (num.Bit1 n) =
      (if m < n then (0, numeral (num.Bit1 m))
       else divmod_step (numeral (num.Bit1 n))
             (divmod (num.Bit1 m)
               (num.Bit0 (num.Bit1 n))))"
  by (simp_all add: divmod_divmod_step)

lemmas divmod_algorithm_code = divmod_trivial divmod_cancel divmod_steps

text \<open>Special case: divisibility\<close>

definition divides_aux :: "'a \<times> 'a \<Rightarrow> bool"
where
  "divides_aux qr \<longleftrightarrow> snd qr = 0"

lemma divides_aux_eq [simp]:
  "divides_aux (q, r) \<longleftrightarrow> r = 0"
  by (simp add: divides_aux_def)

lemma dvd_numeral_simp [simp]:
  "numeral m dvd numeral n \<longleftrightarrow> divides_aux (divmod n m)"
  by (simp add: divmod_def mod_eq_0_iff_dvd)

text \<open>Generic computation of quotient and remainder\<close>

lemma numeral_div_numeral [simp]:
  "numeral k div numeral l = fst (divmod k l)"
  by (simp add: fst_divmod)

lemma numeral_mod_numeral [simp]:
  "numeral k mod numeral l = snd (divmod k l)"
  by (simp add: snd_divmod)

lemma one_div_numeral [simp]:
  "1 div numeral n = fst (divmod num.One n)"
  by (simp add: fst_divmod)

lemma one_mod_numeral [simp]:
  "1 mod numeral n = snd (divmod num.One n)"
  by (simp add: snd_divmod)

end

instantiation nat :: linordered_euclidean_semiring_division
begin

definition divmod_nat :: "num \<Rightarrow> num \<Rightarrow> nat \<times> nat"
where
  divmod'_nat_def: "divmod_nat m n = (numeral m div numeral n, numeral m mod numeral n)"

definition divmod_step_nat :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat"
where
  "divmod_step_nat l qr = (let (q, r) = qr
    in if r \<ge> l then (2 * q + 1, r - l)
    else (2 * q, r))"

instance
  by standard (simp_all add: divmod'_nat_def divmod_step_nat_def)

end

declare divmod_algorithm_code [where ?'a = nat, code]

lemma Suc_0_div_numeral [simp]:
  \<open>Suc 0 div numeral Num.One = 1\<close>
  \<open>Suc 0 div numeral (Num.Bit0 n) = 0\<close>
  \<open>Suc 0 div numeral (Num.Bit1 n) = 0\<close>
  by simp_all

lemma Suc_0_mod_numeral [simp]:
  \<open>Suc 0 mod numeral Num.One = 0\<close>
  \<open>Suc 0 mod numeral (Num.Bit0 n) = 1\<close>
  \<open>Suc 0 mod numeral (Num.Bit1 n) = 1\<close>
  by simp_all

instantiation int :: linordered_euclidean_semiring_division
begin

definition divmod_int :: "num \<Rightarrow> num \<Rightarrow> int \<times> int"
where
  "divmod_int m n = (numeral m div numeral n, numeral m mod numeral n)"

definition divmod_step_int :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int"
where
  "divmod_step_int l qr = (let (q, r) = qr
    in if \<bar>l\<bar> \<le> \<bar>r\<bar> then (2 * q + 1, r - l)
    else (2 * q, r))"

instance
  by standard (auto simp add: divmod_int_def divmod_step_int_def)

end

declare divmod_algorithm_code [where ?'a = int, code]

context
begin

qualified definition adjust_div :: "int \<times> int \<Rightarrow> int"
where
  "adjust_div qr = (let (q, r) = qr in q + of_bool (r \<noteq> 0))"

qualified lemma adjust_div_eq [simp, code]:
  "adjust_div (q, r) = q + of_bool (r \<noteq> 0)"
  by (simp add: adjust_div_def)

qualified definition adjust_mod :: "num \<Rightarrow> int \<Rightarrow> int"
where
  [simp]: "adjust_mod l r = (if r = 0 then 0 else numeral l - r)"

lemma minus_numeral_div_numeral [simp]:
  "- numeral m div numeral n = - (adjust_div (divmod m n) :: int)"
proof -
  have "int (fst (divmod m n)) = fst (divmod m n)"
    by (simp only: fst_divmod divide_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def divide_int_def)
qed

lemma minus_numeral_mod_numeral [simp]:
  "- numeral m mod numeral n = adjust_mod n (snd (divmod m n) :: int)"
proof (cases "snd (divmod m n) = (0::int)")
  case True
  then show ?thesis
    by (simp add: mod_eq_0_iff_dvd divides_aux_def)
next
  case False
  then have "int (snd (divmod m n)) = snd (divmod m n)" if "snd (divmod m n) \<noteq> (0::int)"
    by (simp only: snd_divmod modulo_int_def) auto
  then show ?thesis
    by (simp add: divides_aux_def adjust_div_def)
      (simp add: divides_aux_def modulo_int_def)
qed

lemma numeral_div_minus_numeral [simp]:
  "numeral m div - numeral n = - (adjust_div (divmod m n) :: int)"
proof -
  have "int (fst (divmod m n)) = fst (divmod m n)"
    by (simp only: fst_divmod divide_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def divide_int_def)
qed

lemma numeral_mod_minus_numeral [simp]:
  "numeral m mod - numeral n = - adjust_mod n (snd (divmod m n) :: int)"
proof (cases "snd (divmod m n) = (0::int)")
  case True
  then show ?thesis
    by (simp add: mod_eq_0_iff_dvd divides_aux_def)
next
  case False
  then have "int (snd (divmod m n)) = snd (divmod m n)" if "snd (divmod m n) \<noteq> (0::int)"
    by (simp only: snd_divmod modulo_int_def) auto
  then show ?thesis
    by (simp add: divides_aux_def adjust_div_def)
      (simp add: divides_aux_def modulo_int_def)
qed

lemma minus_one_div_numeral [simp]:
  "- 1 div numeral n = - (adjust_div (divmod Num.One n) :: int)"
  using minus_numeral_div_numeral [of Num.One n] by simp

lemma minus_one_mod_numeral [simp]:
  "- 1 mod numeral n = adjust_mod n (snd (divmod Num.One n) :: int)"
  using minus_numeral_mod_numeral [of Num.One n] by simp

lemma one_div_minus_numeral [simp]:
  "1 div - numeral n = - (adjust_div (divmod Num.One n) :: int)"
  using numeral_div_minus_numeral [of Num.One n] by simp

lemma one_mod_minus_numeral [simp]:
  "1 mod - numeral n = - adjust_mod n (snd (divmod Num.One n) :: int)"
  using numeral_mod_minus_numeral [of Num.One n] by simp

lemma [code]:
  fixes k :: int
  shows
    "k div 0 = 0"
    "k mod 0 = k"
    "0 div k = 0"
    "0 mod k = 0"
    "k div Int.Pos Num.One = k"
    "k mod Int.Pos Num.One = 0"
    "k div Int.Neg Num.One = - k"
    "k mod Int.Neg Num.One = 0"
    "Int.Pos m div Int.Pos n = (fst (divmod m n) :: int)"
    "Int.Pos m mod Int.Pos n = (snd (divmod m n) :: int)"
    "Int.Neg m div Int.Pos n = - (adjust_div (divmod m n) :: int)"
    "Int.Neg m mod Int.Pos n = adjust_mod n (snd (divmod m n) :: int)"
    "Int.Pos m div Int.Neg n = - (adjust_div (divmod m n) :: int)"
    "Int.Pos m mod Int.Neg n = - adjust_mod n (snd (divmod m n) :: int)"
    "Int.Neg m div Int.Neg n = (fst (divmod m n) :: int)"
    "Int.Neg m mod Int.Neg n = - (snd (divmod m n) :: int)"
  by simp_all

end

lemma divmod_BitM_2_eq [simp]:
  \<open>divmod (Num.BitM m) (Num.Bit0 Num.One) = (numeral m - 1, (1 :: int))\<close>
  by (cases m) simp_all


subsubsection \<open>Computation by simplification\<close>

lemma euclidean_size_nat_less_eq_iff:
  \<open>euclidean_size m \<le> euclidean_size n \<longleftrightarrow> m \<le> n\<close> for m n :: nat
  by simp

lemma euclidean_size_int_less_eq_iff:
  \<open>euclidean_size k \<le> euclidean_size l \<longleftrightarrow> \<bar>k\<bar> \<le> \<bar>l\<bar>\<close> for k l :: int
  by auto

simproc_setup numeral_divmod
  ("0 div 0 :: 'a :: linordered_euclidean_semiring_division" | "0 mod 0 :: 'a :: linordered_euclidean_semiring_division" |
   "0 div 1 :: 'a :: linordered_euclidean_semiring_division" | "0 mod 1 :: 'a :: linordered_euclidean_semiring_division" |
   "0 div - 1 :: int" | "0 mod - 1 :: int" |
   "0 div numeral b :: 'a :: linordered_euclidean_semiring_division" | "0 mod numeral b :: 'a :: linordered_euclidean_semiring_division" |
   "0 div - numeral b :: int" | "0 mod - numeral b :: int" |
   "1 div 0 :: 'a :: linordered_euclidean_semiring_division" | "1 mod 0 :: 'a :: linordered_euclidean_semiring_division" |
   "1 div 1 :: 'a :: linordered_euclidean_semiring_division" | "1 mod 1 :: 'a :: linordered_euclidean_semiring_division" |
   "1 div - 1 :: int" | "1 mod - 1 :: int" |
   "1 div numeral b :: 'a :: linordered_euclidean_semiring_division" | "1 mod numeral b :: 'a :: linordered_euclidean_semiring_division" |
   "1 div - numeral b :: int" |"1 mod - numeral b :: int" |
   "- 1 div 0 :: int" | "- 1 mod 0 :: int" | "- 1 div 1 :: int" | "- 1 mod 1 :: int" |
   "- 1 div - 1 :: int" | "- 1 mod - 1 :: int" | "- 1 div numeral b :: int" | "- 1 mod numeral b :: int" |
   "- 1 div - numeral b :: int" | "- 1 mod - numeral b :: int" |
   "numeral a div 0 :: 'a :: linordered_euclidean_semiring_division" | "numeral a mod 0 :: 'a :: linordered_euclidean_semiring_division" |
   "numeral a div 1 :: 'a :: linordered_euclidean_semiring_division" | "numeral a mod 1 :: 'a :: linordered_euclidean_semiring_division" |
   "numeral a div - 1 :: int" | "numeral a mod - 1 :: int" |
   "numeral a div numeral b :: 'a :: linordered_euclidean_semiring_division" | "numeral a mod numeral b :: 'a :: linordered_euclidean_semiring_division" |
   "numeral a div - numeral b :: int" | "numeral a mod - numeral b :: int" |
   "- numeral a div 0 :: int" | "- numeral a mod 0 :: int" |
   "- numeral a div 1 :: int" | "- numeral a mod 1 :: int" |
   "- numeral a div - 1 :: int" | "- numeral a mod - 1 :: int" |
   "- numeral a div numeral b :: int" | "- numeral a mod numeral b :: int" |
   "- numeral a div - numeral b :: int" | "- numeral a mod - numeral b :: int") = \<open>
  let
    val if_cong = the (Code.get_case_cong \<^theory> \<^const_name>\<open>If\<close>);
    fun successful_rewrite ctxt ct =
      let
        val thm = Simplifier.rewrite ctxt ct
      in if Thm.is_reflexive thm then NONE else SOME thm end;
    val simps = @{thms div_0 mod_0 div_by_0 mod_by_0 div_by_1 mod_by_1
      one_div_numeral one_mod_numeral minus_one_div_numeral minus_one_mod_numeral
      one_div_minus_numeral one_mod_minus_numeral
      numeral_div_numeral numeral_mod_numeral minus_numeral_div_numeral minus_numeral_mod_numeral
      numeral_div_minus_numeral numeral_mod_minus_numeral
      div_minus_minus mod_minus_minus Parity.adjust_div_eq of_bool_eq one_neq_zero
      numeral_neq_zero neg_equal_0_iff_equal arith_simps arith_special divmod_trivial
      divmod_cancel divmod_steps divmod_step_def fst_conv snd_conv numeral_One
      case_prod_beta rel_simps Parity.adjust_mod_def div_minus1_right mod_minus1_right
      minus_minus numeral_times_numeral mult_zero_right mult_1_right
      euclidean_size_nat_less_eq_iff euclidean_size_int_less_eq_iff diff_nat_numeral nat_numeral}
      @ [@{lemma "0 = 0 \<longleftrightarrow> True" by simp}];
    val simpset =
      HOL_ss |> Simplifier.simpset_map \<^context>
        (Simplifier.add_cong if_cong #> fold Simplifier.add_simp simps);
  in K (fn ctxt => successful_rewrite (Simplifier.put_simpset simpset ctxt)) end
\<close> \<comment> \<open>
  There is space for improvement here: the calculation itself
  could be carried out outside the logic, and a generic simproc
  (simplifier setup) for generic calculation would be helpful.
\<close>


subsection \<open>Computing congruences modulo \<open>2 ^ q\<close>\<close>

context linordered_euclidean_semiring_division
begin

lemma cong_exp_iff_simps:
  "numeral n mod numeral Num.One = 0
    \<longleftrightarrow> True"
  "numeral (Num.Bit0 n) mod numeral (Num.Bit0 q) = 0
    \<longleftrightarrow> numeral n mod numeral q = 0"
  "numeral (Num.Bit1 n) mod numeral (Num.Bit0 q) = 0
    \<longleftrightarrow> False"
  "numeral m mod numeral Num.One = (numeral n mod numeral Num.One)
    \<longleftrightarrow> True"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> True"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> (numeral n mod numeral q) = 0"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> numeral m mod numeral q = (numeral n mod numeral q)"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> (numeral m mod numeral q) = 0"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> numeral m mod numeral q = (numeral n mod numeral q)"
  by (auto simp add: case_prod_beta dest: arg_cong [of _ _ even])

end


code_identifier
  code_module Parity \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

lemmas even_of_nat = even_of_nat_iff

end
