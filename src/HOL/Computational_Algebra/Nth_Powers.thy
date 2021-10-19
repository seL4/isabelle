(*
  File:      HOL/Computational_Algebra/Nth_Powers.thy
  Author:    Manuel Eberl <manuel@pruvisto.org>

  n-th powers in general and n-th roots of natural numbers
*)
section \<open>$n$-th powers and roots of naturals\<close>
theory Nth_Powers
  imports Primes
begin
  
subsection \<open>The set of $n$-th powers\<close>

definition is_nth_power :: "nat \<Rightarrow> 'a :: monoid_mult \<Rightarrow> bool" where
  "is_nth_power n x \<longleftrightarrow> (\<exists>y. x = y ^ n)"
  
lemma is_nth_power_nth_power [simp, intro]: "is_nth_power n (x ^ n)"
  by (auto simp add: is_nth_power_def)

lemma is_nth_powerI [intro?]: "x = y ^ n \<Longrightarrow> is_nth_power n x"
  by (auto simp: is_nth_power_def)

lemma is_nth_powerE: "is_nth_power n x \<Longrightarrow> (\<And>y. x = y ^ n \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: is_nth_power_def)

  
abbreviation is_square where "is_square \<equiv> is_nth_power 2"
  
lemma is_zeroth_power [simp]: "is_nth_power 0 x \<longleftrightarrow> x = 1"
  by (simp add: is_nth_power_def)

lemma is_first_power [simp]: "is_nth_power 1 x"
  by (simp add: is_nth_power_def)

lemma is_first_power' [simp]: "is_nth_power (Suc 0) x"
  by (simp add: is_nth_power_def)

lemma is_nth_power_0 [simp]: "n > 0 \<Longrightarrow> is_nth_power n (0 :: 'a :: semiring_1)" 
  by (auto simp: is_nth_power_def power_0_left intro!: exI[of _ 0])
    
lemma is_nth_power_0_iff [simp]: "is_nth_power n (0 :: 'a :: semiring_1) \<longleftrightarrow> n > 0"
  by (cases n) auto

lemma is_nth_power_1 [simp]: "is_nth_power n 1"
  by (auto simp: is_nth_power_def intro!: exI[of _ 1])

lemma is_nth_power_Suc_0 [simp]: "is_nth_power n (Suc 0)"
  by (simp add: One_nat_def [symmetric] del: One_nat_def)

lemma is_nth_power_conv_multiplicity: 
  fixes x :: "'a :: {factorial_semiring, normalization_semidom_multiplicative}"
  assumes "n > 0"
  shows   "is_nth_power n (normalize x) \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> n dvd multiplicity p x)"
proof (cases "x = 0")
  case False
  show ?thesis
  proof (safe intro!: is_nth_powerI elim!: is_nth_powerE)
    fix y p :: 'a assume *: "normalize x = y ^ n" "prime p"
    with assms and False have [simp]: "y \<noteq> 0" by (auto simp: power_0_left)
    have "multiplicity p x = multiplicity p (y ^ n)"
      by (subst *(1) [symmetric]) simp
    with False and * and assms show "n dvd multiplicity p x"
      by (auto simp: prime_elem_multiplicity_power_distrib)
  next
    assume *: "\<forall>p. prime p \<longrightarrow> n dvd multiplicity p x"
    have "multiplicity p ((\<Prod>p\<in>prime_factors x. p ^ (multiplicity p x div n)) ^ n) = 
            multiplicity p x" if "prime p" for p
    proof -
      from that and * have "n dvd multiplicity p x" by blast
      have "multiplicity p x = 0" if "p \<notin> prime_factors x"
        using that and \<open>prime p\<close> by (simp add: prime_factors_multiplicity)
      with that and * and assms show ?thesis unfolding prod_power_distrib power_mult [symmetric]
        by (subst multiplicity_prod_prime_powers) (auto simp: in_prime_factors_imp_prime elim: dvdE)
    qed
    with assms False 
      have "normalize x = normalize ((\<Prod>p\<in>prime_factors x. p ^ (multiplicity p x div n)) ^ n)"
      by (intro multiplicity_eq_imp_eq) (auto simp: multiplicity_prod_prime_powers)
    thus "normalize x = normalize (\<Prod>p\<in>prime_factors x. p ^ (multiplicity p x div n)) ^ n"
      by (simp add: normalize_power)
  qed
qed (insert assms, auto)

lemma is_nth_power_conv_multiplicity_nat:
  assumes "n > 0"
  shows   "is_nth_power n (x :: nat) \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> n dvd multiplicity p x)"
  using is_nth_power_conv_multiplicity[OF assms, of x] by simp

lemma is_nth_power_mult:
  assumes "is_nth_power n a" "is_nth_power n b"
  shows   "is_nth_power n (a * b :: 'a :: comm_monoid_mult)"
proof -
  from assms obtain a' b' where "a = a' ^ n" "b = b' ^ n" by (auto elim!: is_nth_powerE)
  hence "a * b = (a' * b') ^ n" by (simp add: power_mult_distrib)
  thus ?thesis by (rule is_nth_powerI)
qed
    
lemma is_nth_power_mult_coprime_natD:
  fixes a b :: nat
  assumes "coprime a b" "is_nth_power n (a * b)" "a > 0" "b > 0"
  shows   "is_nth_power n a" "is_nth_power n b"
proof -
  have A: "is_nth_power n a" if "coprime a b" "is_nth_power n (a * b)" "a \<noteq> 0" "b \<noteq> 0" "n > 0" 
    for a b :: nat unfolding is_nth_power_conv_multiplicity_nat[OF \<open>n > 0\<close>]
  proof safe
    fix p :: nat assume p: "prime p"
    from \<open>coprime a b\<close> have "\<not>(p dvd a \<and> p dvd b)"
      using coprime_common_divisor_nat[of a b p] p by auto
    moreover from that and p
      have "n dvd multiplicity p a + multiplicity p b"
      by (auto simp: is_nth_power_conv_multiplicity_nat prime_elem_multiplicity_mult_distrib)
    ultimately show "n dvd multiplicity p a"
      by (auto simp: not_dvd_imp_multiplicity_0)
  qed
  from A [of a b] assms show "is_nth_power n a"
    by (cases "n = 0") simp_all
  from A [of b a] assms show "is_nth_power n b"
    by (cases "n = 0") (simp_all add: ac_simps)
qed
    
lemma is_nth_power_mult_coprime_nat_iff:
  fixes a b :: nat
  assumes "coprime a b"
  shows   "is_nth_power n (a * b) \<longleftrightarrow> is_nth_power n a \<and>is_nth_power n b" 
  using assms
  by (cases "a = 0"; cases "b = 0")
     (auto intro: is_nth_power_mult dest: is_nth_power_mult_coprime_natD[of a b n]
           simp del: One_nat_def)

lemma is_nth_power_prime_power_nat_iff:
  fixes p :: nat assumes "prime p"
  shows "is_nth_power n (p ^ k) \<longleftrightarrow> n dvd k"
  using assms
  by (cases "n > 0")
     (auto simp: is_nth_power_conv_multiplicity_nat prime_elem_multiplicity_power_distrib)

lemma is_nth_power_nth_power': 
  assumes "n dvd n'"
  shows   "is_nth_power n (m ^ n')"
proof -
  from assms have "n' = n' div n * n" by simp
  also have "m ^ \<dots> = (m ^ (n' div n)) ^ n" by (simp add: power_mult)
  also have "is_nth_power n \<dots>" by simp
  finally show ?thesis .
qed

definition is_nth_power_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  where [code_abbrev]: "is_nth_power_nat = is_nth_power"

lemma is_nth_power_nat_code [code]:
  "is_nth_power_nat n m = 
     (if n = 0 then m = 1 
      else if m = 0 then n > 0
      else if n = 1 then True
      else (\<exists>k\<in>{1..m}. k ^ n = m))"
  by (auto simp: is_nth_power_nat_def is_nth_power_def power_eq_iff_eq_base self_le_power)


(* TODO: Harmonise with Discrete.sqrt *)

subsection \<open>The $n$-root of a natural number\<close>

definition nth_root_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_root_nat k n = (if k = 0 then 0 else Max {m. m ^ k \<le> n})"

lemma zeroth_root_nat [simp]: "nth_root_nat 0 n = 0"
  by (simp add: nth_root_nat_def)

lemma nth_root_nat_aux1: 
  assumes "k > 0"
  shows   "{m::nat. m ^ k \<le> n} \<subseteq> {..n}"
proof safe
  fix m assume "m ^ k \<le> n"
  show "m \<le> n"
  proof (cases "m = 0")
    case False
    with assms have "m ^ 1 \<le> m ^ k" by (intro power_increasing) simp_all
    also note \<open>m ^ k \<le> n\<close>
    finally show ?thesis by simp
  qed simp_all
qed

lemma nth_root_nat_aux2:
  assumes "k > 0"
  shows   "finite {m::nat. m ^ k \<le> n}" "{m::nat. m ^ k \<le> n} \<noteq> {}"
proof -
  from assms have "{m. m ^ k \<le> n} \<subseteq> {..n}" by (rule nth_root_nat_aux1)
  moreover have "finite {..n}" by simp
  ultimately show "finite {m::nat. m ^ k \<le> n}" by (rule finite_subset)
next
  from assms show "{m::nat. m ^ k \<le> n} \<noteq> {}" by (auto intro!: exI[of _ 0] simp: power_0_left)
qed

lemma 
  assumes "k > 0"
  shows   nth_root_nat_power_le: "nth_root_nat k n ^ k \<le> n"
    and   nth_root_nat_ge: "x ^ k \<le> n \<Longrightarrow> x \<le> nth_root_nat k n"
  using Max_in[OF nth_root_nat_aux2[OF assms], of n]
        Max_ge[OF nth_root_nat_aux2(1)[OF assms], of x n] assms
  by (auto simp: nth_root_nat_def)

lemma nth_root_nat_less: 
  assumes "k > 0" "x ^ k > n"
  shows   "nth_root_nat k n < x"
proof -
  from \<open>k > 0\<close> have "nth_root_nat k n ^ k \<le> n" by (rule nth_root_nat_power_le)
  also have "n < x ^ k" by fact
  finally show ?thesis by (rule power_less_imp_less_base) simp_all
qed

lemma nth_root_nat_unique:
  assumes "m ^ k \<le> n" "(m + 1) ^ k > n"
  shows   "nth_root_nat k n = m"
proof (cases "k > 0")
  case True
  from nth_root_nat_less[OF \<open>k > 0\<close> assms(2)] 
    have "nth_root_nat k n \<le> m" by simp
  moreover from \<open>k > 0\<close> and assms(1) have "nth_root_nat k n \<ge> m"
    by (intro nth_root_nat_ge)
  ultimately show ?thesis by (rule antisym)
qed (insert assms, auto)

lemma nth_root_nat_0 [simp]: "nth_root_nat k 0 = 0" by (simp add: nth_root_nat_def)
lemma nth_root_nat_1 [simp]: "k > 0 \<Longrightarrow> nth_root_nat k 1 = 1"
  by (rule nth_root_nat_unique) (auto simp del: One_nat_def)
lemma nth_root_nat_Suc_0 [simp]: "k > 0 \<Longrightarrow> nth_root_nat k (Suc 0) = Suc 0"
  using nth_root_nat_1 by (simp del: nth_root_nat_1)

lemma first_root_nat [simp]: "nth_root_nat 1 n = n"
  by (intro nth_root_nat_unique) auto
    
lemma first_root_nat' [simp]: "nth_root_nat (Suc 0) n = n"
  by (intro nth_root_nat_unique) auto


lemma nth_root_nat_code_naive':
  "nth_root_nat k n = (if k = 0 then 0 else Max (Set.filter (\<lambda>m. m ^ k \<le> n) {..n}))"
proof (cases "k > 0")
  case True
  hence "{m. m ^ k \<le> n} \<subseteq> {..n}" by (rule nth_root_nat_aux1)
  hence "Set.filter (\<lambda>m. m ^ k \<le> n) {..n} = {m. m ^ k \<le> n}"
    by (auto simp: Set.filter_def)
  with True show ?thesis by (simp add: nth_root_nat_def Set.filter_def)
qed simp

function nth_root_nat_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_root_nat_aux m k acc n =
     (let acc' = (k + 1) ^ m
      in  if k \<ge> n \<or> acc' > n then k else nth_root_nat_aux m (k+1) acc' n)"
  by auto
termination by (relation "measure (\<lambda>(_,k,_,n). n - k)", goal_cases) auto

lemma nth_root_nat_aux_le:
  assumes "k ^ m \<le> n" "m > 0"
  shows   "nth_root_nat_aux m k (k ^ m) n ^ m \<le> n"
  using assms
  by (induction m k "k ^ m" n rule:  nth_root_nat_aux.induct) (auto simp: Let_def)

lemma nth_root_nat_aux_gt:
  assumes "m > 0"
  shows   "(nth_root_nat_aux m k (k ^ m) n + 1) ^ m > n"
  using assms
proof (induction m k "k ^ m" n rule:  nth_root_nat_aux.induct)
  case (1 m k n)
  have "n < Suc k ^ m" if "n \<le> k"
  proof -
    note that
    also have "k < Suc k ^ 1" by simp
    also from \<open>m > 0\<close> have "\<dots> \<le> Suc k ^ m" by (intro power_increasing) simp_all
    finally show ?thesis .
  qed
  with 1 show ?case by (auto simp: Let_def)
qed

lemma nth_root_nat_aux_correct:
  assumes "k ^ m \<le> n" "m > 0"
  shows   "nth_root_nat_aux m k (k ^ m) n = nth_root_nat m n"
  by (rule sym, intro nth_root_nat_unique nth_root_nat_aux_le nth_root_nat_aux_gt assms)

lemma nth_root_nat_naive_code [code]:
  "nth_root_nat m n = (if m = 0 \<or> n = 0 then 0 else if m = 1 \<or> n = 1 then n else
                        nth_root_nat_aux m 1 1 n)"
  using nth_root_nat_aux_correct[of 1 m n] by (auto simp: )


lemma nth_root_nat_nth_power [simp]: "k > 0 \<Longrightarrow> nth_root_nat k (n ^ k) = n"
  by (intro nth_root_nat_unique order.refl power_strict_mono) simp_all

lemma nth_root_nat_nth_power':
  assumes "k > 0" "k dvd m" 
  shows   "nth_root_nat k (n ^ m) = n ^ (m div k)"
proof -
  from assms have "m = (m div k) * k" by simp
  also have "n ^ \<dots> = (n ^ (m div k)) ^ k" by (simp add: power_mult)
  also from assms have "nth_root_nat k \<dots> = n ^ (m div k)" by simp
  finally show ?thesis .
qed

lemma nth_root_nat_mono:
  assumes "m \<le> n"
  shows   "nth_root_nat k m \<le> nth_root_nat k n"
proof (cases "k = 0")
  case False
  with assms show ?thesis unfolding nth_root_nat_def
    using nth_root_nat_aux2[of k m] nth_root_nat_aux2[of k n]
    by (auto intro!: Max_mono)
qed auto

end
