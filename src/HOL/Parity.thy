(*  Title:      HOL/Parity.thy
    Author:     Jeremy Avigad
    Author:     Jacques D. Fleuriot
*)

section {* Parity in rings and semirings *}

theory Parity
imports Nat_Transfer
begin

subsection {* Ring structures with parity and @{text even}/@{text odd} predicates *}

class semiring_parity = comm_semiring_1_diff_distrib + numeral +
  assumes odd_one [simp]: "\<not> 2 dvd 1"
  assumes odd_even_add: "\<not> 2 dvd a \<Longrightarrow> \<not> 2 dvd b \<Longrightarrow> 2 dvd a + b"
  assumes even_multD: "2 dvd a * b \<Longrightarrow> 2 dvd a \<or> 2 dvd b"
  assumes odd_ex_decrement: "\<not> 2 dvd a \<Longrightarrow> \<exists>b. a = b + 1"
begin

subclass semiring_numeral ..

abbreviation even :: "'a \<Rightarrow> bool"
where
  "even a \<equiv> 2 dvd a"

abbreviation odd :: "'a \<Rightarrow> bool"
where
  "odd a \<equiv> \<not> 2 dvd a"

lemma even_zero [simp]:
  "even 0"
  by (fact dvd_0_right)

lemma even_plus_one_iff [simp]:
  "even (a + 1) \<longleftrightarrow> odd a"
  by (auto simp add: dvd_add_right_iff intro: odd_even_add)

lemma evenE [elim?]:
  assumes "even a"
  obtains b where "a = 2 * b"
  using assms by (rule dvdE)

lemma oddE [elim?]:
  assumes "odd a"
  obtains b where "a = 2 * b + 1"
proof -
  from assms obtain b where *: "a = b + 1"
    by (blast dest: odd_ex_decrement)
  with assms have "even (b + 2)" by simp
  then have "even b" by simp
  then obtain c where "b = 2 * c" ..
  with * have "a = 2 * c + 1" by simp
  with that show thesis .
qed
 
lemma even_times_iff [simp]:
  "even (a * b) \<longleftrightarrow> even a \<or> even b"
  by (auto dest: even_multD)

lemma even_numeral [simp]:
  "even (numeral (Num.Bit0 n))"
proof -
  have "even (2 * numeral n)"
    unfolding even_times_iff by simp
  then have "even (numeral n + numeral n)"
    unfolding mult_2 .
  then show ?thesis
    unfolding numeral.simps .
qed

lemma odd_numeral [simp]:
  "odd (numeral (Num.Bit1 n))"
proof
  assume "even (numeral (num.Bit1 n))"
  then have "even (numeral n + numeral n + 1)"
    unfolding numeral.simps .
  then have "even (2 * numeral n + 1)"
    unfolding mult_2 .
  then have "2 dvd numeral n * 2 + 1"
    by (simp add: ac_simps)
  with dvd_add_times_triv_left_iff [of 2 "numeral n" 1]
    have "2 dvd 1"
    by simp
  then show False by simp
qed

lemma even_add [simp]:
  "even (a + b) \<longleftrightarrow> (even a \<longleftrightarrow> even b)"
  by (auto simp add: dvd_add_right_iff dvd_add_left_iff odd_even_add)

lemma odd_add [simp]:
  "odd (a + b) \<longleftrightarrow> (\<not> (odd a \<longleftrightarrow> odd b))"
  by simp

lemma even_power [simp]:
  "even (a ^ n) \<longleftrightarrow> even a \<and> n > 0"
  by (induct n) auto

end

class ring_parity = ring + semiring_parity
begin

subclass comm_ring_1 ..

lemma even_minus [simp]:
  "even (- a) \<longleftrightarrow> even a"
  by (fact dvd_minus_iff)

lemma even_diff [simp]:
  "even (a - b) \<longleftrightarrow> even (a + b)"
  using even_add [of a "- b"] by simp

end


subsection {* Instances for @{typ nat} and @{typ int} *}

lemma even_Suc_Suc_iff [simp]:
  "even (Suc (Suc n)) \<longleftrightarrow> even n"
  using dvd_add_triv_right_iff [of 2 n] by simp

lemma even_Suc [simp]:
  "even (Suc n) \<longleftrightarrow> odd n"
  by (induct n) auto

lemma even_diff_nat [simp]:
  fixes m n :: nat
  shows "even (m - n) \<longleftrightarrow> m < n \<or> even (m + n)"
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
  
lemma even_diff_iff [simp]:
  fixes k l :: int
  shows "even (k - l) \<longleftrightarrow> even (k + l)"
  using dvd_add_times_triv_right_iff [of 2 "k - l" l] by (simp add: mult_2_right)

lemma even_abs_add_iff [simp]:
  fixes k l :: int
  shows "even (\<bar>k\<bar> + l) \<longleftrightarrow> even (k + l)"
  by (cases "k \<ge> 0") (simp_all add: ac_simps)

lemma even_add_abs_iff [simp]:
  fixes k l :: int
  shows "even (k + \<bar>l\<bar>) \<longleftrightarrow> even (k + l)"
  using even_abs_add_iff [of l k] by (simp add: ac_simps)

instance nat :: semiring_parity
proof
  show "odd (1 :: nat)"
    by (rule notI, erule dvdE) simp
next
  fix m n :: nat
  assume "odd m"
  moreover assume "odd n"
  ultimately have *: "even (Suc m) \<and> even (Suc n)"
    by simp
  then have "even (Suc m + Suc n)"
    by (blast intro: dvd_add)
  also have "Suc m + Suc n = m + n + 2"
    by simp
  finally show "even (m + n)"
    using dvd_add_triv_right_iff [of 2 "m + n"] by simp
next
  fix m n :: nat
  assume *: "even (m * n)"
  show "even m \<or> even n"
  proof (rule disjCI)
    assume "odd n"
    then have "even (Suc n)" by simp
    then obtain r where "Suc n = 2 * r" ..
    moreover from * obtain s where "m * n = 2 * s" ..
    then have "2 * s + m = m * Suc n" by simp
    ultimately have " 2 * s + m = 2 * (m * r)" by (simp add: algebra_simps)
    then have "m = 2 * (m * r - s)" by simp
    then show "even m" ..
  qed
next
  fix n :: nat
  assume "odd n"
  then show "\<exists>m. n = m + 1"
    by (cases n) simp_all
qed

lemma odd_pos: 
  "odd (n :: nat) \<Longrightarrow> 0 < n"
  by (auto elim: oddE)
  
instance int :: ring_parity
proof
  show "odd (1 :: int)" by (simp add: dvd_int_unfold_dvd_nat)
  fix k l :: int
  assume "odd k"
  moreover assume "odd l"
  ultimately have "even (nat \<bar>k\<bar> + nat \<bar>l\<bar>)" 
    by (auto simp add: dvd_int_unfold_dvd_nat intro: odd_even_add)
  then have "even (\<bar>k\<bar> + \<bar>l\<bar>)"
    by (simp add: dvd_int_unfold_dvd_nat nat_add_distrib)
  then show "even (k + l)"
    by simp
next
  fix k l :: int
  assume "even (k * l)"
  then show "even k \<or> even l"
    by (simp add: dvd_int_unfold_dvd_nat even_multD nat_abs_mult_distrib)
next
  fix k :: int
  have "k = (k - 1) + 1" by simp
  then show "\<exists>l. k = l + 1" ..
qed

lemma even_int_iff [simp]:
  "even (int n) \<longleftrightarrow> even n"
  by (simp add: dvd_int_iff)

lemma even_nat_iff:
  "0 \<le> k \<Longrightarrow> even (nat k) \<longleftrightarrow> even k"
  by (simp add: even_int_iff [symmetric])


subsection {* Parity and powers *}

context comm_ring_1
begin

lemma power_minus_even [simp]:
  "even n \<Longrightarrow> (- a) ^ n = a ^ n"
  by (auto elim: evenE)

lemma power_minus_odd [simp]:
  "odd n \<Longrightarrow> (- a) ^ n = - (a ^ n)"
  by (auto elim: oddE)

lemma neg_one_even_power [simp]:
  "even n \<Longrightarrow> (- 1) ^ n = 1"
  by simp

lemma neg_one_odd_power [simp]:
  "odd n \<Longrightarrow> (- 1) ^ n = - 1"
  by simp

end  

context linordered_idom
begin

lemma zero_le_even_power:
  "even n \<Longrightarrow> 0 \<le> a ^ n"
  by (auto elim: evenE)

lemma zero_le_odd_power:
  "odd n \<Longrightarrow> 0 \<le> a ^ n \<longleftrightarrow> 0 \<le> a"
  by (auto simp add: power_even_eq zero_le_mult_iff elim: oddE)

lemma zero_le_power_eq:
  "0 \<le> a ^ n \<longleftrightarrow> even n \<or> odd n \<and> 0 \<le> a"
  by (auto simp add: zero_le_even_power zero_le_odd_power)
  
lemma zero_less_power_eq:
  "0 < a ^ n \<longleftrightarrow> n = 0 \<or> even n \<and> a \<noteq> 0 \<or> odd n \<and> 0 < a"
proof -
  have [simp]: "0 = a ^ n \<longleftrightarrow> a = 0 \<and> n > 0"
    unfolding power_eq_0_iff [of a n, symmetric] by blast
  show ?thesis
  unfolding less_le zero_le_power_eq by auto
qed

lemma power_less_zero_eq [simp]:
  "a ^ n < 0 \<longleftrightarrow> odd n \<and> a < 0"
  unfolding not_le [symmetric] zero_le_power_eq by auto
  
lemma power_le_zero_eq:
  "a ^ n \<le> 0 \<longleftrightarrow> n > 0 \<and> (odd n \<and> a \<le> 0 \<or> even n \<and> a = 0)"
  unfolding not_less [symmetric] zero_less_power_eq by auto 

lemma power_even_abs:
  "even n \<Longrightarrow> \<bar>a\<bar> ^ n = a ^ n"
  using power_abs [of a n] by (simp add: zero_le_even_power)

lemma power_mono_even:
  assumes "even n" and "\<bar>a\<bar> \<le> \<bar>b\<bar>"
  shows "a ^ n \<le> b ^ n"
proof -
  have "0 \<le> \<bar>a\<bar>" by auto
  with `\<bar>a\<bar> \<le> \<bar>b\<bar>`
  have "\<bar>a\<bar> ^ n \<le> \<bar>b\<bar> ^ n" by (rule power_mono)
  with `even n` show ?thesis by (simp add: power_even_abs)  
qed

lemma power_mono_odd:
  assumes "odd n" and "a \<le> b"
  shows "a ^ n \<le> b ^ n"
proof (cases "b < 0")
  case True with `a \<le> b` have "- b \<le> - a" and "0 \<le> - b" by auto
  hence "(- b) ^ n \<le> (- a) ^ n" by (rule power_mono)
  with `odd n` show ?thesis by simp
next
  case False then have "0 \<le> b" by auto
  show ?thesis
  proof (cases "a < 0")
    case True then have "n \<noteq> 0" and "a \<le> 0" using `odd n` [THEN odd_pos] by auto
    then have "a ^ n \<le> 0" unfolding power_le_zero_eq using `odd n` by auto
    moreover
    from `0 \<le> b` have "0 \<le> b ^ n" by auto
    ultimately show ?thesis by auto
  next
    case False then have "0 \<le> a" by auto
    with `a \<le> b` show ?thesis using power_mono by auto
  qed
qed
 
text {* Simplify, when the exponent is a numeral *}

lemma zero_le_power_eq_numeral [simp]:
  "0 \<le> a ^ numeral w \<longleftrightarrow> even (numeral w :: nat) \<or> odd (numeral w :: nat) \<and> 0 \<le> a"
  by (fact zero_le_power_eq)

lemma zero_less_power_eq_numeral [simp]:
  "0 < a ^ numeral w \<longleftrightarrow> numeral w = (0 :: nat)
    \<or> even (numeral w :: nat) \<and> a \<noteq> 0 \<or> odd (numeral w :: nat) \<and> 0 < a"
  by (fact zero_less_power_eq)

lemma power_le_zero_eq_numeral [simp]:
  "a ^ numeral w \<le> 0 \<longleftrightarrow> (0 :: nat) < numeral w
    \<and> (odd (numeral w :: nat) \<and> a \<le> 0 \<or> even (numeral w :: nat) \<and> a = 0)"
  by (fact power_le_zero_eq)

lemma power_less_zero_eq_numeral [simp]:
  "a ^ numeral w < 0 \<longleftrightarrow> odd (numeral w :: nat) \<and> a < 0"
  by (fact power_less_zero_eq)

lemma power_even_abs_numeral [simp]:
  "even (numeral w :: nat) \<Longrightarrow> \<bar>a\<bar> ^ numeral w = a ^ numeral w"
  by (fact power_even_abs)

end


subsubsection {* Tools setup *}

declare transfer_morphism_int_nat [transfer add return:
  even_int_iff
]

end

