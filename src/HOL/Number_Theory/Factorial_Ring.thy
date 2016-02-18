(*  Title:      HOL/Number_Theory/Factorial_Ring.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Factorial (semi)rings\<close>

theory Factorial_Ring
imports Main Primes "~~/src/HOL/Library/Multiset" (*"~~/src/HOL/Library/Polynomial"*)
begin

class factorial_semiring = normalization_semidom +
  assumes finite_divisors: "a \<noteq> 0 \<Longrightarrow> finite {b. b dvd a \<and> normalize b = b}"
  fixes is_prime :: "'a \<Rightarrow> bool"
  assumes not_is_prime_zero [simp]: "\<not> is_prime 0"
    and is_prime_not_unit: "is_prime p \<Longrightarrow> \<not> is_unit p"
    and no_prime_divisorsI: "(\<And>b. b dvd a \<Longrightarrow> \<not> is_prime b) \<Longrightarrow> is_unit a"
  assumes is_primeI: "p \<noteq> 0 \<Longrightarrow> \<not> is_unit p \<Longrightarrow> (\<And>a. a dvd p \<Longrightarrow> \<not> is_unit a \<Longrightarrow> p dvd a) \<Longrightarrow> is_prime p"
    and is_primeD: "is_prime p \<Longrightarrow> p dvd a * b \<Longrightarrow> p dvd a \<or> p dvd b"
begin

lemma not_is_prime_one [simp]:
  "\<not> is_prime 1"
  by (auto dest: is_prime_not_unit)

lemma is_prime_not_zeroI:
  assumes "is_prime p"
  shows "p \<noteq> 0"
  using assms by (auto intro: ccontr)

lemma is_prime_multD:
  assumes "is_prime (a * b)"
  shows "is_unit a \<or> is_unit b"
proof -
  from assms have "a \<noteq> 0" "b \<noteq> 0" by auto
  moreover from assms is_primeD [of "a * b"] have "a * b dvd a \<or> a * b dvd b"
    by auto
  ultimately show ?thesis
    using dvd_times_left_cancel_iff [of a b 1]
      dvd_times_right_cancel_iff [of b a 1]
    by auto
qed

lemma is_primeD2:
  assumes "is_prime p" and "a dvd p" and "\<not> is_unit a"
  shows "p dvd a"
proof -
  from \<open>a dvd p\<close> obtain b where "p = a * b" ..
  with \<open>is_prime p\<close> is_prime_multD \<open>\<not> is_unit a\<close> have "is_unit b" by auto
  with \<open>p = a * b\<close> show ?thesis
    by (auto simp add: mult_unit_dvd_iff)
qed

lemma is_prime_mult_unit_left:
  assumes "is_prime p"
    and "is_unit a"
  shows "is_prime (a * p)"
proof (rule is_primeI)
  from assms show "a * p \<noteq> 0" "\<not> is_unit (a * p)"
    by (auto simp add: is_unit_mult_iff is_prime_not_unit)
  show "a * p dvd b" if "b dvd a * p" "\<not> is_unit b" for b
  proof -
    from that \<open>is_unit a\<close> have "b dvd p"
      using dvd_mult_unit_iff [of a b p] by (simp add: ac_simps)
    with \<open>is_prime p\<close> \<open>\<not> is_unit b\<close> have "p dvd b" 
      using is_primeD2 [of p b] by auto
    with \<open>is_unit a\<close> show ?thesis
      using mult_unit_dvd_iff [of a p b] by (simp add: ac_simps)
  qed
qed

lemma is_primeI2:
  assumes "p \<noteq> 0"
  assumes "\<not> is_unit p"
  assumes P: "\<And>a b. p dvd a * b \<Longrightarrow> p dvd a \<or> p dvd b"
  shows "is_prime p"
using \<open>p \<noteq> 0\<close> \<open>\<not> is_unit p\<close> proof (rule is_primeI)
  fix a
  assume "a dvd p"
  then obtain b where "p = a * b" ..
  with \<open>p \<noteq> 0\<close> have "b \<noteq> 0" by simp
  moreover from \<open>p = a * b\<close> P have "p dvd a \<or> p dvd b" by auto
  moreover assume "\<not> is_unit a"
  ultimately show "p dvd a"
    using dvd_times_right_cancel_iff [of b a 1] \<open>p = a * b\<close> by auto
qed    

lemma not_is_prime_divisorE:
  assumes "a \<noteq> 0" and "\<not> is_unit a" and "\<not> is_prime a"
  obtains b where "b dvd a" and "\<not> is_unit b" and "\<not> a dvd b"
proof -
  from assms have "\<exists>b. b dvd a \<and> \<not> is_unit b \<and> \<not> a dvd b"
    by (auto intro: is_primeI)
  with that show thesis by blast
qed

lemma prime_divisorE:
  assumes "a \<noteq> 0" and "\<not> is_unit a" 
  obtains p where "is_prime p" and "p dvd a"
  using assms no_prime_divisorsI [of a] by blast

lemma prime_dvd_mult_iff:  
  assumes "is_prime p"
  shows "p dvd a * b \<longleftrightarrow> p dvd a \<or> p dvd b"
  using assms by (auto dest: is_primeD)

lemma prime_dvd_power_iff:
  assumes "is_prime p"
  shows "p dvd a ^ n \<longleftrightarrow> p dvd a \<and> n > 0"
  using assms by (induct n) (auto dest: is_prime_not_unit is_primeD)

lemma is_prime_normalize_iff [simp]:
  "is_prime (normalize p) \<longleftrightarrow> is_prime p" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q show ?P
    by (rule is_primeI) (insert \<open>?Q\<close>, simp_all add: is_prime_not_zeroI is_prime_not_unit is_primeD2)
next
  assume ?P show ?Q
    by (rule is_primeI)
      (insert is_prime_not_zeroI [of "normalize p"] is_prime_not_unit [of "normalize p"] is_primeD2 [of "normalize p"] \<open>?P\<close>, simp_all)
qed  

lemma is_prime_inj_power:
  assumes "is_prime p"
  shows "inj (op ^ p)"
proof (rule injI, rule ccontr)
  fix m n :: nat
  have [simp]: "p ^ q = 1 \<longleftrightarrow> q = 0" (is "?P \<longleftrightarrow> ?Q") for q
  proof
    assume ?Q then show ?P by simp
  next
    assume ?P then have "is_unit (p ^ q)" by simp
    with assms show ?Q by (auto simp add: is_unit_power_iff is_prime_not_unit)
  qed
  have *: False if "p ^ m = p ^ n" and "m > n" for m n
  proof -
    from assms have "p \<noteq> 0"
      by (rule is_prime_not_zeroI)
    then have "p ^ n \<noteq> 0"
      by (induct n) simp_all
    from that have "m = n + (m - n)" and "m - n > 0" by arith+
    then obtain q where "m = n + q" and "q > 0" ..
    with that have "p ^ n * p ^ q = p ^ n * 1" by (simp add: power_add)
    with \<open>p ^ n \<noteq> 0\<close> have "p ^ q = 1"
      using mult_left_cancel [of "p ^ n" "p ^ q" 1] by simp
    with \<open>q > 0\<close> show ?thesis by simp
  qed 
  assume "m \<noteq> n"
  then have "m > n \<or> m < n" by arith
  moreover assume "p ^ m = p ^ n"
  ultimately show False using * [of m n] * [of n m] by auto
qed

lemma prime_unique:
  assumes "is_prime q" and "is_prime p" and "q dvd p"
  shows "normalize q = normalize p"
proof -
  from assms have "p dvd q"
    by (auto dest: is_primeD2 [of p] is_prime_not_unit [of q])
  with assms show ?thesis
    by (auto intro: associatedI)
qed  

lemma exists_factorization:
  assumes "a \<noteq> 0"
  obtains P where "\<And>p. p \<in># P \<Longrightarrow> is_prime p" "msetprod P = normalize a"
proof -
  let ?prime_factors = "\<lambda>a. {p. p dvd a \<and> is_prime p \<and> normalize p = p}"
  have "?prime_factors a \<subseteq> {b. b dvd a \<and> normalize b = b}" by auto
  moreover from assms have "finite {b. b dvd a \<and> normalize b = b}"
    by (rule finite_divisors)
  ultimately have "finite (?prime_factors a)" by (rule finite_subset)
  then show thesis using \<open>a \<noteq> 0\<close> that proof (induct "?prime_factors a" arbitrary: thesis a)
    case empty then have
      P: "\<And>b. is_prime b \<Longrightarrow> b dvd a \<Longrightarrow> normalize b \<noteq> b" and "a \<noteq> 0"
      by auto
    have "is_unit a"
    proof (rule no_prime_divisorsI)
      fix b
      assume "b dvd a"
      then show "\<not> is_prime b"
        using P [of "normalize b"] by auto
    qed
    then have "\<And>p. p \<in># {#} \<Longrightarrow> is_prime p" and "msetprod {#} = normalize a"
      by (simp_all add: is_unit_normalize)
    with empty show thesis by blast
  next
    case (insert p P)
    from \<open>insert p P = ?prime_factors a\<close>
    have "p dvd a" and "is_prime p" and "normalize p = p"
      by auto
    obtain n where "n > 0" and "p ^ n dvd a" and "\<not> p ^ Suc n dvd a" 
    proof (rule that)
      def N \<equiv> "{n. p ^ n dvd a}"
      from is_prime_inj_power \<open>is_prime p\<close> have "inj (op ^ p)" .
      then have "inj_on (op ^ p) U" for U
        by (rule subset_inj_on) simp
      moreover have "op ^ p ` N \<subseteq> {b. b dvd a \<and> normalize b = b}"
        by (auto simp add: normalize_power \<open>normalize p = p\<close> N_def)
      ultimately have "finite N"
        by (rule inj_on_finite) (simp add: finite_divisors \<open>a \<noteq> 0\<close>)
      from N_def \<open>a \<noteq> 0\<close> have "0 \<in> N" by (simp add: N_def)
      then have "N \<noteq> {}" by blast
      note * = \<open>finite N\<close> \<open>N \<noteq> {}\<close>
      from N_def \<open>p dvd a\<close> have "1 \<in> N" by simp
      with * show "Max N > 0"
        by (auto simp add: Max_gr_iff)
      from * have "Max N \<in> N" by (rule Max_in)
      then show "p ^ Max N dvd a" by (simp add: N_def)
      from * have "\<forall>n\<in>N. n \<le> Max N"
        by (simp add: Max_le_iff [symmetric])
      then have "p ^ Suc (Max N) dvd a \<Longrightarrow> Suc (Max N) \<le> Max N"
        by (rule bspec) (simp add: N_def)
      then show "\<not> p ^ Suc (Max N) dvd a"
        by auto
    qed
    from \<open>p ^ n dvd a\<close> obtain c where "a = p ^ n * c" ..
    with \<open>\<not> p ^ Suc n dvd a\<close> have "\<not> p dvd c"
      by (auto elim: dvdE simp add: ac_simps)
    have "?prime_factors a - {p} = ?prime_factors c" (is "?A = ?B")
    proof (rule set_eqI)
      fix q
      show "q \<in> ?A \<longleftrightarrow> q \<in> ?B"
      using \<open>normalize p = p\<close> \<open>is_prime p\<close> \<open>a = p ^ n * c\<close> \<open>\<not> p dvd c\<close>
        prime_unique [of q p]
        by (auto simp add: prime_dvd_power_iff prime_dvd_mult_iff)
    qed
    moreover from insert have "P = ?prime_factors a - {p}"
      by auto
    ultimately have "P = ?prime_factors c"
      by simp
    moreover from \<open>a \<noteq> 0\<close> \<open>a = p ^ n * c\<close> have "c \<noteq> 0"
      by auto
    ultimately obtain P where "\<And>p. p \<in># P \<Longrightarrow> is_prime p" "msetprod P = normalize c"
      using insert(3) by blast 
    with \<open>is_prime p\<close> \<open>a = p ^ n * c\<close> \<open>normalize p = p\<close>
    have "\<And>q. q \<in># P + (replicate_mset n p) \<longrightarrow> is_prime q" "msetprod (P + replicate_mset n p) = normalize a"
      by (auto simp add: ac_simps normalize_mult normalize_power)
    with insert(6) show thesis by blast
  qed
qed
  
end

instantiation nat :: factorial_semiring
begin

definition is_prime_nat :: "nat \<Rightarrow> bool"
where
  "is_prime_nat p \<longleftrightarrow> (1 < p \<and> (\<forall>n. n dvd p \<longrightarrow> n = 1 \<or> n = p))"

lemma is_prime_eq_prime:
  "is_prime = prime"
  by (simp add: fun_eq_iff prime_def is_prime_nat_def)

instance proof
  show "\<not> is_prime (0::nat)" by (simp add: is_prime_nat_def)
  show "\<not> is_unit p" if "is_prime p" for p :: nat
    using that by (simp add: is_prime_nat_def)
next
  fix p :: nat
  assume "p \<noteq> 0" and "\<not> is_unit p"
  then have "p > 1" by simp
  assume P: "\<And>n. n dvd p \<Longrightarrow> \<not> is_unit n \<Longrightarrow> p dvd n"
  have "n = 1" if "n dvd p" "n \<noteq> p" for n
  proof (rule ccontr)
    assume "n \<noteq> 1"
    with that P have "p dvd n" by auto
    with \<open>n dvd p\<close> have "n = p" by (rule dvd_antisym)
    with that show False by simp
  qed
  with \<open>p > 1\<close> show "is_prime p" by (auto simp add: is_prime_nat_def)
next
  fix p m n :: nat
  assume "is_prime p"
  then have "prime p" by (simp add: is_prime_eq_prime)
  moreover assume "p dvd m * n"
  ultimately show "p dvd m \<or> p dvd n"
    by (rule prime_dvd_mult_nat)
next
  fix n :: nat
  show "is_unit n" if "\<And>m. m dvd n \<Longrightarrow> \<not> is_prime m"
    using that prime_factor_nat by (auto simp add: is_prime_eq_prime)
qed simp

end

instantiation int :: factorial_semiring
begin

definition is_prime_int :: "int \<Rightarrow> bool"
where
  "is_prime_int p \<longleftrightarrow> is_prime (nat \<bar>p\<bar>)"

lemma is_prime_int_iff [simp]:
  "is_prime (int n) \<longleftrightarrow> is_prime n"
  by (simp add: is_prime_int_def)

lemma is_prime_nat_abs_iff [simp]:
  "is_prime (nat \<bar>k\<bar>) \<longleftrightarrow> is_prime k"
  by (simp add: is_prime_int_def)

instance proof
  show "\<not> is_prime (0::int)" by (simp add: is_prime_int_def)
  show "\<not> is_unit p" if "is_prime p" for p :: int
    using that is_prime_not_unit [of "nat \<bar>p\<bar>"] by simp
next
  fix p :: int
  assume P: "\<And>k. k dvd p \<Longrightarrow> \<not> is_unit k \<Longrightarrow> p dvd k"
  have "nat \<bar>p\<bar> dvd n" if "n dvd nat \<bar>p\<bar>" and "n \<noteq> Suc 0" for n :: nat
  proof -
    from that have "int n dvd p" by (simp add: int_dvd_iff)
    moreover from that have "\<not> is_unit (int n)" by simp
    ultimately have "p dvd int n" by (rule P)
    with that have "p dvd int n" by auto
    then show ?thesis by (simp add: dvd_int_iff)
  qed
  moreover assume "p \<noteq> 0" and "\<not> is_unit p"
  ultimately have "is_prime (nat \<bar>p\<bar>)" by (intro is_primeI) auto
  then show "is_prime p" by simp
next
  fix p k l :: int
  assume "is_prime p"
  then have *: "is_prime (nat \<bar>p\<bar>)" by simp
  assume "p dvd k * l"
  then have "nat \<bar>p\<bar> dvd nat \<bar>k * l\<bar>"
    by (simp add: dvd_int_unfold_dvd_nat)
  then have "nat \<bar>p\<bar> dvd nat \<bar>k\<bar> * nat \<bar>l\<bar>"
    by (simp add: abs_mult nat_mult_distrib)
  with * have "nat \<bar>p\<bar> dvd nat \<bar>k\<bar> \<or> nat \<bar>p\<bar> dvd nat \<bar>l\<bar>"
    using is_primeD [of "nat \<bar>p\<bar>"] by auto
  then show "p dvd k \<or> p dvd l"
    by (simp add: dvd_int_unfold_dvd_nat)
next
  fix k :: int
  assume P: "\<And>l. l dvd k \<Longrightarrow> \<not> is_prime l"
  have "is_unit (nat \<bar>k\<bar>)"
  proof (rule no_prime_divisorsI)
    fix m
    assume "m dvd nat \<bar>k\<bar>"
    then have "int m dvd k" by (simp add: int_dvd_iff)
    then have "\<not> is_prime (int m)" by (rule P)
    then show "\<not> is_prime m" by simp
  qed
  then show "is_unit k" by simp
qed simp

end

end
