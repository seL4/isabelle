(*  Title:      HOL/Parity.thy
    Author:     Jeremy Avigad
    Author:     Jacques D. Fleuriot
*)

header {* Even and Odd for int and nat *}

theory Parity
imports Main
begin

subsection {* Preliminaries about divisibility on @{typ nat} and @{typ int} *}

lemma two_dvd_Suc_Suc_iff [simp]:
  "2 dvd Suc (Suc n) \<longleftrightarrow> 2 dvd n"
  using dvd_add_triv_right_iff [of 2 n] by simp

lemma two_dvd_Suc_iff:
  "2 dvd Suc n \<longleftrightarrow> \<not> 2 dvd n"
  by (induct n) auto

lemma two_dvd_diff_nat_iff:
  fixes m n :: nat
  shows "2 dvd m - n \<longleftrightarrow> m < n \<or> 2 dvd m + n"
proof (cases "n \<le> m")
  case True
  then have "m - n + n * 2 = m + n" by simp
  moreover have "2 dvd m - n \<longleftrightarrow> 2 dvd m - n + n * 2" by simp
  ultimately have "2 dvd m - n \<longleftrightarrow> 2 dvd m + n" by (simp only:)
  then show ?thesis by auto
next
  case False
  then show ?thesis by simp
qed 
  
lemma two_dvd_diff_iff:
  fixes k l :: int
  shows "2 dvd k - l \<longleftrightarrow> 2 dvd k + l"
  using dvd_add_times_triv_right_iff [of 2 "k - l" l] by (simp add: ac_simps)

lemma two_dvd_abs_add_iff:
  fixes k l :: int
  shows "2 dvd \<bar>k\<bar> + l \<longleftrightarrow> 2 dvd k + l"
  by (cases "k \<ge> 0") (simp_all add: two_dvd_diff_iff ac_simps)

lemma two_dvd_add_abs_iff:
  fixes k l :: int
  shows "2 dvd k + \<bar>l\<bar> \<longleftrightarrow> 2 dvd k + l"
  using two_dvd_abs_add_iff [of l k] by (simp add: ac_simps)


subsection {* Ring structures with parity *}

class semiring_parity = semiring_dvd + semiring_numeral +
  assumes two_not_dvd_one [simp]: "\<not> 2 dvd 1"
  assumes not_dvd_not_dvd_dvd_add: "\<not> 2 dvd a \<Longrightarrow> \<not> 2 dvd b \<Longrightarrow> 2 dvd a + b"
  assumes two_is_prime: "2 dvd a * b \<Longrightarrow> 2 dvd a \<or> 2 dvd b"
  assumes not_dvd_ex_decrement: "\<not> 2 dvd a \<Longrightarrow> \<exists>b. a = b + 1"
begin

lemma two_dvd_plus_one_iff [simp]:
  "2 dvd a + 1 \<longleftrightarrow> \<not> 2 dvd a"
  by (auto simp add: dvd_add_right_iff intro: not_dvd_not_dvd_dvd_add)

lemma not_two_dvdE [elim?]:
  assumes "\<not> 2 dvd a"
  obtains b where "a = 2 * b + 1"
proof -
  from assms obtain b where *: "a = b + 1"
    by (blast dest: not_dvd_ex_decrement)
  with assms have "2 dvd b + 2" by simp
  then have "2 dvd b" by simp
  then obtain c where "b = 2 * c" ..
  with * have "a = 2 * c + 1" by simp
  with that show thesis .
qed

end

instance nat :: semiring_parity
proof
  show "\<not> (2 :: nat) dvd 1"
    by (rule notI, erule dvdE) simp
next
  fix m n :: nat
  assume "\<not> 2 dvd m"
  moreover assume "\<not> 2 dvd n"
  ultimately have *: "2 dvd Suc m \<and> 2 dvd Suc n"
    by (simp add: two_dvd_Suc_iff)
  then have "2 dvd Suc m + Suc n"
    by (blast intro: dvd_add)
  also have "Suc m + Suc n = m + n + 2"
    by simp
  finally show "2 dvd m + n"
    using dvd_add_triv_right_iff [of 2 "m + n"] by simp
next
  fix m n :: nat
  assume *: "2 dvd m * n"
  show "2 dvd m \<or> 2 dvd n"
  proof (rule disjCI)
    assume "\<not> 2 dvd n"
    then have "2 dvd Suc n" by (simp add: two_dvd_Suc_iff)
    then obtain r where "Suc n = 2 * r" ..
    moreover from * obtain s where "m * n = 2 * s" ..
    then have "2 * s + m = m * Suc n" by simp
    ultimately have " 2 * s + m = 2 * (m * r)" by simp
    then have "m = 2 * (m * r - s)" by simp
    then show "2 dvd m" ..
  qed
next
  fix n :: nat
  assume "\<not> 2 dvd n"
  then show "\<exists>m. n = m + 1"
    by (cases n) simp_all
qed

class ring_parity = comm_ring_1 + semiring_parity

instance int :: ring_parity
proof
  show "\<not> (2 :: int) dvd 1" by (simp add: dvd_int_unfold_dvd_nat)
  fix k l :: int
  assume "\<not> 2 dvd k"
  moreover assume "\<not> 2 dvd l"
  ultimately have "2 dvd nat \<bar>k\<bar> + nat \<bar>l\<bar>" 
    by (auto simp add: dvd_int_unfold_dvd_nat intro: not_dvd_not_dvd_dvd_add)
  then have "2 dvd \<bar>k\<bar> + \<bar>l\<bar>"
    by (simp add: dvd_int_unfold_dvd_nat nat_add_distrib)
  then show "2 dvd k + l"
    by (simp add: two_dvd_abs_add_iff two_dvd_add_abs_iff)
next
  fix k l :: int
  assume "2 dvd k * l"
  then show "2 dvd k \<or> 2 dvd l"
    by (simp add: dvd_int_unfold_dvd_nat two_is_prime nat_abs_mult_distrib)
next
  fix k :: int
  have "k = (k - 1) + 1" by simp
  then show "\<exists>l. k = l + 1" ..
qed

context semiring_div_parity
begin

subclass semiring_parity
proof (unfold_locales, unfold dvd_eq_mod_eq_0 not_mod_2_eq_0_eq_1)
  fix a b c
  show "(c * a + b) mod a = 0 \<longleftrightarrow> b mod a = 0"
    by simp
next
  fix a b c
  assume "(b + c) mod a = 0"
  with mod_add_eq [of b c a]
  have "(b mod a + c mod a) mod a = 0"
    by simp
  moreover assume "b mod a = 0"
  ultimately show "c mod a = 0"
    by simp
next
  show "1 mod 2 = 1"
    by (fact one_mod_two_eq_one)
next
  fix a b
  assume "a mod 2 = 1"
  moreover assume "b mod 2 = 1"
  ultimately show "(a + b) mod 2 = 0"
    using mod_add_eq [of a b 2] by simp
next
  fix a b
  assume "(a * b) mod 2 = 0"
  then have "(a mod 2) * (b mod 2) = 0"
    by (cases "a mod 2 = 0") (simp_all add: mod_mult_eq [of a b 2])
  then show "a mod 2 = 0 \<or> b mod 2 = 0"
    by (rule divisors_zero)
next
  fix a
  assume "a mod 2 = 1"
  then have "a = a div 2 * 2 + 1" using mod_div_equality [of a 2] by simp
  then show "\<exists>b. a = b + 1" ..
qed

end


subsection {* Dedicated @{text even}/@{text odd} predicate *}

subsubsection {* Properties *}

context semiring_parity
begin

definition even :: "'a \<Rightarrow> bool"
where
  [algebra]: "even a \<longleftrightarrow> 2 dvd a"

abbreviation odd :: "'a \<Rightarrow> bool"
where
  "odd a \<equiv> \<not> even a"

lemma oddE [elim?]:
  assumes "odd a"
  obtains b where "a = 2 * b + 1"
proof -
  from assms have "\<not> 2 dvd a" by (simp add: even_def)
  then show thesis using that by (rule not_two_dvdE)
qed
  
lemma even_times_iff [simp, presburger, algebra]:
  "even (a * b) \<longleftrightarrow> even a \<or> even b"
  by (auto simp add: even_def dest: two_is_prime)

lemma even_zero [simp]:
  "even 0"
  by (simp add: even_def)

lemma odd_one [simp]:
  "odd 1"
  by (simp add: even_def)

lemma even_numeral [simp]:
  "even (numeral (Num.Bit0 n))"
proof -
  have "even (2 * numeral n)"
    unfolding even_times_iff by (simp add: even_def)
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
    unfolding even_def by (simp add: ac_simps)
  with dvd_add_times_triv_left_iff [of 2 "numeral n" 1]
    have "2 dvd 1"
    by simp
  then show False by simp
qed

lemma even_add [simp]:
  "even (a + b) \<longleftrightarrow> (even a \<longleftrightarrow> even b)"
  by (auto simp add: even_def dvd_add_right_iff dvd_add_left_iff not_dvd_not_dvd_dvd_add)

lemma odd_add [simp]:
  "odd (a + b) \<longleftrightarrow> (\<not> (odd a \<longleftrightarrow> odd b))"
  by simp

lemma even_power [simp, presburger]:
  "even (a ^ n) \<longleftrightarrow> even a \<and> n \<noteq> 0"
  by (induct n) auto

end

context ring_parity
begin

lemma even_minus [simp, presburger, algebra]:
  "even (- a) \<longleftrightarrow> even a"
  by (simp add: even_def)

lemma even_diff [simp]:
  "even (a - b) \<longleftrightarrow> even (a + b)"
  using even_add [of a "- b"] by simp

end

context semiring_div_parity
begin

lemma even_iff_mod_2_eq_zero [presburger]:
  "even a \<longleftrightarrow> a mod 2 = 0"
  by (simp add: even_def dvd_eq_mod_eq_0)

end


subsubsection {* Particularities for @{typ nat} and @{typ int} *}

lemma even_Suc [simp, presburger, algebra]:
  "even (Suc n) = odd n"
  by (simp add: even_def two_dvd_Suc_iff)

lemma even_diff_nat [simp]:
  fixes m n :: nat
  shows "even (m - n) \<longleftrightarrow> m < n \<or> even (m + n)"
  by (simp add: even_def two_dvd_diff_nat_iff)

lemma even_int_iff:
  "even (int n) \<longleftrightarrow> even n"
  by (simp add: even_def dvd_int_iff)

lemma even_nat_iff:
  "0 \<le> k \<Longrightarrow> even (nat k) \<longleftrightarrow> even k"
  by (simp add: even_int_iff [symmetric])


subsubsection {* Tools setup *}

declare transfer_morphism_int_nat [transfer add return:
  even_int_iff
]

lemma [presburger]:
  "even n \<longleftrightarrow> even (int n)"
  using even_int_iff [of n] by simp

lemma (in semiring_parity) [presburger]:
  "even (a + b) \<longleftrightarrow> even a \<and> even b \<or> odd a \<and> odd b"
  by auto

lemma [presburger, algebra]:
  fixes m n :: nat
  shows "even (m - n) \<longleftrightarrow> m < n \<or> even m \<and> even n \<or> odd m \<and> odd n"
  by auto

lemma [presburger, algebra]:
  fixes m n :: nat
  shows "even (m ^ n) \<longleftrightarrow> even m \<and> 0 < n"
  by simp

lemma [presburger]:
  fixes k :: int
  shows "(k + 1) div 2 = k div 2 \<longleftrightarrow> even k"
  by presburger

lemma [presburger]:
  fixes k :: int
  shows "(k + 1) div 2 = k div 2 + 1 \<longleftrightarrow> odd k"
  by presburger
  
lemma [presburger]:
  "Suc n div Suc (Suc 0) = n div Suc (Suc 0) \<longleftrightarrow> even n"
  by presburger


subsubsection {* Legacy cruft *}


subsubsection {* Equivalent definitions *}

lemma even_nat_mod_two_eq_zero:
  "even (x::nat) ==> x mod Suc (Suc 0) = 0"
  by presburger

lemma odd_nat_mod_two_eq_one:
  "odd (x::nat) ==> x mod Suc (Suc 0) = Suc 0"
  by presburger

lemma even_nat_equiv_def:
  "even (x::nat) = (x mod Suc (Suc 0) = 0)"
  by presburger

lemma odd_nat_equiv_def:
  "odd (x::nat) = (x mod Suc (Suc 0) = Suc 0)"
  by presburger

lemma even_nat_div_two_times_two:
  "even (x::nat) ==> Suc (Suc 0) * (x div Suc (Suc 0)) = x"
  by presburger

lemma odd_nat_div_two_times_two_plus_one:
  "odd (x::nat) ==> Suc (Suc (Suc 0) * (x div Suc (Suc 0))) = x"
  by presburger


subsubsection {* Parity and powers *}

lemma (in comm_ring_1) neg_power_if:
  "(- a) ^ n = (if even n then (a ^ n) else - (a ^ n))"
  by (induct n) simp_all

lemma (in comm_ring_1)
  shows neg_one_even_power [simp]: "even n \<Longrightarrow> (- 1) ^ n = 1"
  and neg_one_odd_power [simp]: "odd n \<Longrightarrow> (- 1) ^ n = - 1"
  by (simp_all add: neg_power_if)

lemma zero_le_even_power: "even n ==>
    0 <= (x::'a::{linordered_ring,monoid_mult}) ^ n"
  apply (simp add: even_def)
  apply (erule dvdE)
  apply (erule ssubst)
  unfolding mult.commute [of 2]
  unfolding power_mult power2_eq_square
  apply (rule zero_le_square)
  done

lemma zero_le_odd_power:
  "odd n \<Longrightarrow> 0 \<le> (x::'a::{linordered_idom}) ^ n \<longleftrightarrow> 0 \<le> x"
  by (erule oddE) (auto simp: power_add zero_le_mult_iff mult_2 order_antisym_conv)

lemma zero_le_power_eq [presburger]: "(0 <= (x::'a::{linordered_idom}) ^ n) =
    (even n | (odd n & 0 <= x))"
  apply auto
  apply (subst zero_le_odd_power [symmetric])
  apply assumption+
  apply (erule zero_le_even_power)
  done

lemma zero_less_power_eq[presburger]: "(0 < (x::'a::{linordered_idom}) ^ n) =
    (n = 0 | (even n & x ~= 0) | (odd n & 0 < x))"
  unfolding order_less_le zero_le_power_eq by auto

lemma power_less_zero_eq[presburger]: "((x::'a::{linordered_idom}) ^ n < 0) =
    (odd n & x < 0)"
  apply (subst linorder_not_le [symmetric])+
  apply (subst zero_le_power_eq)
  apply auto
  done

lemma power_le_zero_eq[presburger]: "((x::'a::{linordered_idom}) ^ n <= 0) =
    (n ~= 0 & ((odd n & x <= 0) | (even n & x = 0)))"
  apply (subst linorder_not_less [symmetric])+
  apply (subst zero_less_power_eq)
  apply auto
  done

lemma power_even_abs: "even n ==>
    (abs (x::'a::{linordered_idom}))^n = x^n"
  apply (subst power_abs [symmetric])
  apply (simp add: zero_le_even_power)
  done

lemma power_minus_even [simp]: "even n ==>
    (- x)^n = (x^n::'a::{comm_ring_1})"
  apply (subst power_minus)
  apply simp
  done

lemma power_minus_odd [simp]: "odd n ==>
    (- x)^n = - (x^n::'a::{comm_ring_1})"
  apply (subst power_minus)
  apply simp
  done

lemma power_mono_even: fixes x y :: "'a :: {linordered_idom}"
  assumes "even n" and "\<bar>x\<bar> \<le> \<bar>y\<bar>"
  shows "x^n \<le> y^n"
proof -
  have "0 \<le> \<bar>x\<bar>" by auto
  with `\<bar>x\<bar> \<le> \<bar>y\<bar>`
  have "\<bar>x\<bar>^n \<le> \<bar>y\<bar>^n" by (rule power_mono)
  thus ?thesis unfolding power_even_abs[OF `even n`] .
qed

lemma odd_pos: "odd (n::nat) \<Longrightarrow> 0 < n" by presburger

lemma power_mono_odd: fixes x y :: "'a :: {linordered_idom}"
  assumes "odd n" and "x \<le> y"
  shows "x^n \<le> y^n"
proof (cases "y < 0")
  case True with `x \<le> y` have "-y \<le> -x" and "0 \<le> -y" by auto
  hence "(-y)^n \<le> (-x)^n" by (rule power_mono)
  thus ?thesis unfolding power_minus_odd[OF `odd n`] by auto
next
  case False
  show ?thesis
  proof (cases "x < 0")
    case True hence "n \<noteq> 0" and "x \<le> 0" using `odd n`[THEN odd_pos] by auto
    hence "x^n \<le> 0" unfolding power_le_zero_eq using `odd n` by auto
    moreover
    from `\<not> y < 0` have "0 \<le> y" by auto
    hence "0 \<le> y^n" by auto
    ultimately show ?thesis by auto
  next
    case False hence "0 \<le> x" by auto
    with `x \<le> y` show ?thesis using power_mono by auto
  qed
qed


subsubsection {* More Even/Odd Results *}
 
lemma even_mult_two_ex: "even(n) = (\<exists>m::nat. n = 2*m)" by presburger
lemma odd_Suc_mult_two_ex: "odd(n) = (\<exists>m. n = Suc (2*m))" by presburger

lemma lemma_even_div2 [simp]: "even (n::nat) ==> (n + 1) div 2 = n div 2"
  by presburger

lemma lemma_odd_div2 [simp]: "odd n ==> (n + 1) div 2 = Suc (n div 2)"
  by presburger

lemma even_num_iff: "0 < n ==> even n = (odd (n - 1 :: nat))" by presburger
lemma even_even_mod_4_iff: "even (n::nat) = even (n mod 4)" by presburger

lemma lemma_odd_mod_4_div_2: "n mod 4 = (3::nat) ==> odd((n - 1) div 2)" by presburger

lemma lemma_even_mod_4_div_2: "n mod 4 = (1::nat) ==> even ((n - 1) div 2)"
  by presburger

text {* Simplify, when the exponent is a numeral *}

lemmas zero_le_power_eq_numeral [simp] =
  zero_le_power_eq [of _ "numeral w"] for w

lemmas zero_less_power_eq_numeral [simp] =
  zero_less_power_eq [of _ "numeral w"] for w

lemmas power_le_zero_eq_numeral [simp] =
  power_le_zero_eq [of _ "numeral w"] for w

lemmas power_less_zero_eq_numeral [simp] =
  power_less_zero_eq [of _ "numeral w"] for w

lemmas zero_less_power_nat_eq_numeral [simp] =
  nat_zero_less_power_iff [of _ "numeral w"] for w

lemmas power_eq_0_iff_numeral [simp] =
  power_eq_0_iff [of _ "numeral w"] for w

lemmas power_even_abs_numeral [simp] =
  power_even_abs [of "numeral w" _] for w


subsubsection {* An Equivalence for @{term [source] "0 \<le> a^n"} *}

lemma zero_le_power_iff[presburger]:
  "(0 \<le> a^n) = (0 \<le> (a::'a::{linordered_idom}) | even n)"
proof cases
  assume even: "even n"
  then have "2 dvd n" by (simp add: even_def)
  then obtain k where "n = 2 * k" ..
  thus ?thesis by (simp add: zero_le_even_power even)
next
  assume odd: "odd n"
  then obtain k where "n = 2 * k + 1" ..
  moreover have "a ^ (2 * k) \<le> 0 \<Longrightarrow> a = 0"
    by (induct k) (auto simp add: zero_le_mult_iff mult_le_0_iff)
  ultimately show ?thesis
    by (auto simp add: zero_le_mult_iff zero_le_even_power)
qed


subsubsection {* Miscellaneous *}

lemma even_nat_plus_one_div_two:
  "even (x::nat) ==> (Suc x) div Suc (Suc 0) = x div Suc (Suc 0)"
  by presburger

lemma odd_nat_plus_one_div_two:
  "odd (x::nat) ==> (Suc x) div Suc (Suc 0) = Suc (x div Suc (Suc 0))"
  by presburger

end

