(*  Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad, Tobias Nipkow, 
                Manuel Eberl


This file deals with properties of primes. Definitions and lemmas are
proved uniformly for the natural numbers and integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on @{cite davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD". IntPrimes also defined and developed
the congruence relations on the integers. The notion was extended to
the natural numbers by Chaieb.

Jeremy Avigad combined all of these, made everything uniform for the
natural numbers and the integers, and added a number of new theorems.

Tobias Nipkow cleaned up a lot.

Florian Haftmann and Manuel Eberl put primality and prime factorisation
onto an algebraic foundation and thus generalised these concepts to 
other rings, such as polynomials. (see also the Factorial_Ring theory).

There were also previous formalisations of unique factorisation by 
Thomas Marthedal Rasmussen, Jeremy Avigad, and David Gray.
*)


section \<open>Primes\<close>

theory Primes
imports "~~/src/HOL/Binomial" Euclidean_Algorithm
begin

(* As a simp or intro rule,

     prime p \<Longrightarrow> p > 0

   wreaks havoc here. When the premise includes \<forall>x \<in># M. prime x, it
   leads to the backchaining

     x > 0
     prime x
     x \<in># M   which is, unfortunately,
     count M x > 0
*)

declare [[coercion int]]
declare [[coercion_enabled]]

lemma prime_elem_nat_iff:
  "prime_elem (n :: nat) \<longleftrightarrow> (1 < n \<and> (\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n))"
proof safe
  assume *: "prime_elem n"
  from * have "n \<noteq> 0" "n \<noteq> 1" by (intro notI, simp del: One_nat_def)+
  thus "n > 1" by (cases n) simp_all
  fix m assume m: "m dvd n" "m \<noteq> n"
  from * \<open>m dvd n\<close> have "n dvd m \<or> is_unit m"
    by (intro irreducibleD' prime_elem_imp_irreducible)
  with m show "m = 1" by (auto dest: dvd_antisym)
next
  assume "n > 1" "\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n"
  thus "prime_elem n"
    by (auto simp: prime_elem_iff_irreducible irreducible_altdef)
qed

lemma prime_nat_iff_prime_elem: "prime (n :: nat) \<longleftrightarrow> prime_elem n"
  by (simp add: prime_def)

lemma prime_nat_iff:
  "prime (n :: nat) \<longleftrightarrow> (1 < n \<and> (\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n))"
  by (simp add: prime_nat_iff_prime_elem prime_elem_nat_iff)

lemma prime_elem_int_nat_transfer: "prime_elem (n::int) \<longleftrightarrow> prime_elem (nat (abs n))"
proof
  assume "prime_elem n"
  thus "prime_elem (nat (abs n))" by (auto simp: prime_elem_def nat_dvd_iff)
next
  assume "prime_elem (nat (abs n))"
  thus "prime_elem n"
    by (auto simp: dvd_int_unfold_dvd_nat prime_elem_def abs_mult nat_mult_distrib)
qed

lemma prime_elem_nat_int_transfer [simp]: "prime_elem (int n) \<longleftrightarrow> prime_elem n"
  by (auto simp: prime_elem_int_nat_transfer)

lemma prime_nat_int_transfer [simp]: "prime (int n) \<longleftrightarrow> prime n"
  by (auto simp: prime_elem_int_nat_transfer prime_def)

lemma prime_int_nat_transfer: "prime (n::int) \<longleftrightarrow> n \<ge> 0 \<and> prime (nat n)"
  by (auto simp: prime_elem_int_nat_transfer prime_def)

lemma prime_int_iff:
  "prime (n::int) \<longleftrightarrow> (1 < n \<and> (\<forall>m. m \<ge> 0 \<and> m dvd n \<longrightarrow> m = 1 \<or> m = n))"
proof (intro iffI conjI allI impI; (elim conjE)?)
  assume *: "prime n"
  hence irred: "irreducible n" by (simp add: prime_elem_imp_irreducible)
  from * have "n \<ge> 0" "n \<noteq> 0" "n \<noteq> 1" 
    by (auto simp: prime_def zabs_def not_less split: if_splits)
  thus "n > 1" by presburger
  fix m assume "m dvd n" \<open>m \<ge> 0\<close>
  with irred have "m dvd 1 \<or> n dvd m" by (auto simp: irreducible_altdef)
  with \<open>m dvd n\<close> \<open>m \<ge> 0\<close> \<open>n > 1\<close> show "m = 1 \<or> m = n"
    using associated_iff_dvd[of m n] by auto
next
  assume n: "1 < n" "\<forall>m. m \<ge> 0 \<and> m dvd n \<longrightarrow> m = 1 \<or> m = n"
  hence "nat n > 1" by simp
  moreover have "\<forall>m. m dvd nat n \<longrightarrow> m = 1 \<or> m = nat n"
  proof (intro allI impI)
    fix m assume "m dvd nat n"
    with \<open>n > 1\<close> have "int m dvd n" by (auto simp: int_dvd_iff)
    with n(2) have "int m = 1 \<or> int m = n" by auto
    thus "m = 1 \<or> m = nat n" by auto
  qed
  ultimately show "prime n" 
    unfolding prime_int_nat_transfer prime_nat_iff by auto
qed


lemma prime_nat_not_dvd:
  assumes "prime p" "p > n" "n \<noteq> (1::nat)"
  shows   "\<not>n dvd p"
proof
  assume "n dvd p"
  from assms(1) have "irreducible p" by (simp add: prime_elem_imp_irreducible)
  from irreducibleD'[OF this \<open>n dvd p\<close>] \<open>n dvd p\<close> \<open>p > n\<close> assms show False
    by (cases "n = 0") (auto dest!: dvd_imp_le)
qed

lemma prime_int_not_dvd:
  assumes "prime p" "p > n" "n > (1::int)"
  shows   "\<not>n dvd p"
proof
  assume "n dvd p"
  from assms(1) have "irreducible p" by (simp add: prime_elem_imp_irreducible)
  from irreducibleD'[OF this \<open>n dvd p\<close>] \<open>n dvd p\<close> \<open>p > n\<close> assms show False
    by (auto dest!: zdvd_imp_le)
qed

lemma prime_odd_nat: "prime p \<Longrightarrow> p > (2::nat) \<Longrightarrow> odd p"
  by (intro prime_nat_not_dvd) auto

lemma prime_odd_int: "prime p \<Longrightarrow> p > (2::int) \<Longrightarrow> odd p"
  by (intro prime_int_not_dvd) auto

lemma prime_ge_0_int: "prime p \<Longrightarrow> p \<ge> (0::int)"
  unfolding prime_int_iff by auto

lemma prime_gt_0_nat: "prime p \<Longrightarrow> p > (0::nat)"
  unfolding prime_nat_iff by auto

lemma prime_gt_0_int: "prime p \<Longrightarrow> p > (0::int)"
  unfolding prime_int_iff by auto

lemma prime_ge_1_nat: "prime p \<Longrightarrow> p \<ge> (1::nat)"
  unfolding prime_nat_iff by auto

lemma prime_ge_Suc_0_nat: "prime p \<Longrightarrow> p \<ge> Suc 0"
  unfolding prime_nat_iff by auto

lemma prime_ge_1_int: "prime p \<Longrightarrow> p \<ge> (1::int)"
  unfolding prime_int_iff by auto

lemma prime_gt_1_nat: "prime p \<Longrightarrow> p > (1::nat)"
  unfolding prime_nat_iff by auto

lemma prime_gt_Suc_0_nat: "prime p \<Longrightarrow> p > Suc 0"
  unfolding prime_nat_iff by auto

lemma prime_gt_1_int: "prime p \<Longrightarrow> p > (1::int)"
  unfolding prime_int_iff by auto

lemma prime_ge_2_nat: "prime p \<Longrightarrow> p \<ge> (2::nat)"
  unfolding prime_nat_iff by auto

lemma prime_ge_2_int: "prime p \<Longrightarrow> p \<ge> (2::int)"
  unfolding prime_int_iff by auto

lemma prime_int_altdef:
  "prime p = (1 < p \<and> (\<forall>m::int. m \<ge> 0 \<longrightarrow> m dvd p \<longrightarrow>
    m = 1 \<or> m = p))"
  unfolding prime_int_iff by blast

lemma not_prime_eq_prod_nat:
  assumes "m > 1" "\<not>prime (m::nat)"
  shows   "\<exists>n k. n = m * k \<and> 1 < m \<and> m < n \<and> 1 < k \<and> k < n"
  using assms irreducible_altdef[of m]
  by (auto simp: prime_elem_iff_irreducible prime_def irreducible_altdef)


subsubsection \<open>Make prime naively executable\<close>

lemma Suc_0_not_prime_nat [simp]: "~prime (Suc 0)"
  unfolding One_nat_def [symmetric] by (rule not_prime_1)

lemma prime_nat_iff':
  "prime (p :: nat) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p)"
proof safe
  assume "p > 1" and *: "\<forall>n\<in>{1<..<p}. \<not>n dvd p"
  show "prime p" unfolding prime_nat_iff
  proof (intro conjI allI impI)
    fix m assume "m dvd p"
    with \<open>p > 1\<close> have "m \<noteq> 0" by (intro notI) auto
    hence "m \<ge> 1" by simp
    moreover from \<open>m dvd p\<close> and * have "m \<notin> {1<..<p}" by blast
    with \<open>m dvd p\<close> and \<open>p > 1\<close> have "m \<le> 1 \<or> m = p" by (auto dest: dvd_imp_le)
    ultimately show "m = 1 \<or> m = p" by simp
  qed fact+
qed (auto simp: prime_nat_iff)

lemma prime_nat_code [code_unfold]:
  "(prime :: nat \<Rightarrow> bool) = (\<lambda>p. p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p))"
  by (rule ext, rule prime_nat_iff')

lemma prime_int_iff':
  "prime (p :: int) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p)" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  thus "?rhs" by (auto simp: prime_int_nat_transfer dvd_int_unfold_dvd_nat prime_nat_code)
next
  assume "?rhs"
  thus "?lhs" by (auto simp: prime_int_nat_transfer zdvd_int prime_nat_code)
qed

lemma prime_int_code [code_unfold]:
  "(prime :: int \<Rightarrow> bool) = (\<lambda>p. p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p))" 
  by (rule ext, rule prime_int_iff')

lemma prime_nat_simp:
    "prime p \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> set [2..<p]. \<not> n dvd p)"
  by (auto simp add: prime_nat_code)

lemma prime_int_simp:
    "prime (p::int) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {2..<p}. \<not> n dvd p)"
  by (auto simp add: prime_int_code)

lemmas prime_nat_simp_numeral [simp] = prime_nat_simp [of "numeral m"] for m

lemma two_is_prime_nat [simp]: "prime (2::nat)"
  by simp

declare prime_int_nat_transfer[of "numeral m" for m, simp]


text\<open>A bit of regression testing:\<close>

lemma "prime(97::nat)" by simp
lemma "prime(997::nat)" by eval
lemma "prime(97::int)" by simp
lemma "prime(997::int)" by eval

lemma prime_factor_nat: 
  "n \<noteq> (1::nat) \<Longrightarrow> \<exists>p. prime p \<and> p dvd n"
  using prime_divisor_exists[of n]
  by (cases "n = 0") (auto intro: exI[of _ "2::nat"])


subsection \<open>Infinitely many primes\<close>

lemma next_prime_bound: "\<exists>p::nat. prime p \<and> n < p \<and> p \<le> fact n + 1"
proof-
  have f1: "fact n + 1 \<noteq> (1::nat)" using fact_ge_1 [of n, where 'a=nat] by arith
  from prime_factor_nat [OF f1]
  obtain p :: nat where "prime p" and "p dvd fact n + 1" by auto
  then have "p \<le> fact n + 1" apply (intro dvd_imp_le) apply auto done
  { assume "p \<le> n"
    from \<open>prime p\<close> have "p \<ge> 1"
      by (cases p, simp_all)
    with \<open>p <= n\<close> have "p dvd fact n"
      by (intro dvd_fact)
    with \<open>p dvd fact n + 1\<close> have "p dvd fact n + 1 - fact n"
      by (rule dvd_diff_nat)
    then have "p dvd 1" by simp
    then have "p <= 1" by auto
    moreover from \<open>prime p\<close> have "p > 1"
      using prime_nat_iff by blast
    ultimately have False by auto}
  then have "n < p" by presburger
  with \<open>prime p\<close> and \<open>p <= fact n + 1\<close> show ?thesis by auto
qed

lemma bigger_prime: "\<exists>p. prime p \<and> p > (n::nat)"
  using next_prime_bound by auto

lemma primes_infinite: "\<not> (finite {(p::nat). prime p})"
proof
  assume "finite {(p::nat). prime p}"
  with Max_ge have "(EX b. (ALL x : {(p::nat). prime p}. x <= b))"
    by auto
  then obtain b where "ALL (x::nat). prime x \<longrightarrow> x <= b"
    by auto
  with bigger_prime [of b] show False
    by auto
qed

subsection\<open>Powers of Primes\<close>

text\<open>Versions for type nat only\<close>

lemma prime_product:
  fixes p::nat
  assumes "prime (p * q)"
  shows "p = 1 \<or> q = 1"
proof -
  from assms have
    "1 < p * q" and P: "\<And>m. m dvd p * q \<Longrightarrow> m = 1 \<or> m = p * q"
    unfolding prime_nat_iff by auto
  from \<open>1 < p * q\<close> have "p \<noteq> 0" by (cases p) auto
  then have Q: "p = p * q \<longleftrightarrow> q = 1" by auto
  have "p dvd p * q" by simp
  then have "p = 1 \<or> p = p * q" by (rule P)
  then show ?thesis by (simp add: Q)
qed

(* TODO: Generalise? *)
lemma prime_power_mult_nat:
  fixes p::nat
  assumes p: "prime p" and xy: "x * y = p ^ k"
  shows "\<exists>i j. x = p ^i \<and> y = p^ j"
using xy
proof(induct k arbitrary: x y)
  case 0 thus ?case apply simp by (rule exI[where x="0"], simp)
next
  case (Suc k x y)
  from Suc.prems have pxy: "p dvd x*y" by auto
  from prime_dvd_multD [OF p pxy] have pxyc: "p dvd x \<or> p dvd y" .
  from p have p0: "p \<noteq> 0" by - (rule ccontr, simp)
  {assume px: "p dvd x"
    then obtain d where d: "x = p*d" unfolding dvd_def by blast
    from Suc.prems d  have "p*d*y = p^Suc k" by simp
    hence th: "d*y = p^k" using p0 by simp
    from Suc.hyps[OF th] obtain i j where ij: "d = p^i" "y = p^j" by blast
    with d have "x = p^Suc i" by simp
    with ij(2) have ?case by blast}
  moreover
  {assume px: "p dvd y"
    then obtain d where d: "y = p*d" unfolding dvd_def by blast
    from Suc.prems d  have "p*d*x = p^Suc k" by (simp add: mult.commute)
    hence th: "d*x = p^k" using p0 by simp
    from Suc.hyps[OF th] obtain i j where ij: "d = p^i" "x = p^j" by blast
    with d have "y = p^Suc i" by simp
    with ij(2) have ?case by blast}
  ultimately show ?case  using pxyc by blast
qed

lemma prime_power_exp_nat:
  fixes p::nat
  assumes p: "prime p" and n: "n \<noteq> 0"
    and xn: "x^n = p^k" shows "\<exists>i. x = p^i"
  using n xn
proof(induct n arbitrary: k)
  case 0 thus ?case by simp
next
  case (Suc n k) hence th: "x*x^n = p^k" by simp
  {assume "n = 0" with Suc have ?case by simp (rule exI[where x="k"], simp)}
  moreover
  {assume n: "n \<noteq> 0"
    from prime_power_mult_nat[OF p th]
    obtain i j where ij: "x = p^i" "x^n = p^j"by blast
    from Suc.hyps[OF n ij(2)] have ?case .}
  ultimately show ?case by blast
qed

lemma divides_primepow_nat:
  fixes p::nat
  assumes p: "prime p"
  shows "d dvd p^k \<longleftrightarrow> (\<exists> i. i \<le> k \<and> d = p ^i)"
proof
  assume H: "d dvd p^k" then obtain e where e: "d*e = p^k"
    unfolding dvd_def  apply (auto simp add: mult.commute) by blast
  from prime_power_mult_nat[OF p e] obtain i j where ij: "d = p^i" "e=p^j" by blast
  from e ij have "p^(i + j) = p^k" by (simp add: power_add)
  hence "i + j = k" using p prime_gt_1_nat power_inject_exp[of p "i+j" k] by simp
  hence "i \<le> k" by arith
  with ij(1) show "\<exists>i\<le>k. d = p ^ i" by blast
next
  {fix i assume H: "i \<le> k" "d = p^i"
    then obtain j where j: "k = i + j"
      by (metis le_add_diff_inverse)
    hence "p^k = p^j*d" using H(2) by (simp add: power_add)
    hence "d dvd p^k" unfolding dvd_def by auto}
  thus "\<exists>i\<le>k. d = p ^ i \<Longrightarrow> d dvd p ^ k" by blast
qed


subsection \<open>Chinese Remainder Theorem Variants\<close>

lemma bezout_gcd_nat:
  fixes a::nat shows "\<exists>x y. a * x - b * y = gcd a b \<or> b * x - a * y = gcd a b"
  using bezout_nat[of a b]
by (metis bezout_nat diff_add_inverse gcd_add_mult gcd.commute
  gcd_nat.right_neutral mult_0)

lemma gcd_bezout_sum_nat:
  fixes a::nat
  assumes "a * x + b * y = d"
  shows "gcd a b dvd d"
proof-
  let ?g = "gcd a b"
    have dv: "?g dvd a*x" "?g dvd b * y"
      by simp_all
    from dvd_add[OF dv] assms
    show ?thesis by auto
qed


text \<open>A binary form of the Chinese Remainder Theorem.\<close>

(* TODO: Generalise? *)
lemma chinese_remainder:
  fixes a::nat  assumes ab: "coprime a b" and a: "a \<noteq> 0" and b: "b \<noteq> 0"
  shows "\<exists>x q1 q2. x = u + q1 * a \<and> x = v + q2 * b"
proof-
  from bezout_add_strong_nat[OF a, of b] bezout_add_strong_nat[OF b, of a]
  obtain d1 x1 y1 d2 x2 y2 where dxy1: "d1 dvd a" "d1 dvd b" "a * x1 = b * y1 + d1"
    and dxy2: "d2 dvd b" "d2 dvd a" "b * x2 = a * y2 + d2" by blast
  then have d12: "d1 = 1" "d2 =1"
    by (metis ab coprime_nat)+
  let ?x = "v * a * x1 + u * b * x2"
  let ?q1 = "v * x1 + u * y2"
  let ?q2 = "v * y1 + u * x2"
  from dxy2(3)[simplified d12] dxy1(3)[simplified d12]
  have "?x = u + ?q1 * a" "?x = v + ?q2 * b"
    by algebra+
  thus ?thesis by blast
qed

text \<open>Primality\<close>

lemma coprime_bezout_strong:
  fixes a::nat assumes "coprime a b"  "b \<noteq> 1"
  shows "\<exists>x y. a * x = b * y + 1"
by (metis assms bezout_nat gcd_nat.left_neutral)

lemma bezout_prime:
  assumes p: "prime p" and pa: "\<not> p dvd a"
  shows "\<exists>x y. a*x = Suc (p*y)"
proof -
  have ap: "coprime a p"
    by (metis gcd.commute p pa prime_imp_coprime)
  moreover from p have "p \<noteq> 1" by auto
  ultimately have "\<exists>x y. a * x = p * y + 1"
    by (rule coprime_bezout_strong)
  then show ?thesis by simp    
qed
(* END TODO *)



subsection \<open>Multiplicity and primality for natural numbers and integers\<close>

lemma prime_factors_gt_0_nat:
  "p \<in> prime_factors x \<Longrightarrow> p > (0::nat)"
  by (simp add: prime_factors_prime prime_gt_0_nat)

lemma prime_factors_gt_0_int:
  "p \<in> prime_factors x \<Longrightarrow> p > (0::int)"
  by (simp add: prime_factors_prime prime_gt_0_int)

lemma prime_factors_ge_0_int [elim]:
  fixes n :: int
  shows "p \<in> prime_factors n \<Longrightarrow> p \<ge> 0"
  unfolding prime_factors_def 
  by (auto split: if_splits simp: prime_def dest!: in_prime_factorization_imp_prime)

lemma msetprod_prime_factorization_int:
  fixes n :: int
  assumes "n > 0"
  shows   "msetprod (prime_factorization n) = n"
  using assms by (simp add: msetprod_prime_factorization)

lemma prime_factorization_exists_nat:
  "n > 0 \<Longrightarrow> (\<exists>M. (\<forall>p::nat \<in> set_mset M. prime p) \<and> n = (\<Prod>i \<in># M. i))"
  using prime_factorization_exists[of n] by (auto simp: prime_def)

lemma msetprod_prime_factorization_nat [simp]: 
  "(n::nat) > 0 \<Longrightarrow> msetprod (prime_factorization n) = n"
  by (subst msetprod_prime_factorization) simp_all

lemma prime_factorization_nat:
    "n > (0::nat) \<Longrightarrow> n = (\<Prod>p \<in> prime_factors n. p ^ multiplicity p n)"
  by (simp add: setprod_prime_factors)

lemma prime_factorization_int:
    "n > (0::int) \<Longrightarrow> n = (\<Prod>p \<in> prime_factors n. p ^ multiplicity p n)"
  by (simp add: setprod_prime_factors)

lemma prime_factorization_unique_nat:
  fixes f :: "nat \<Rightarrow> _"
  assumes S_eq: "S = {p. 0 < f p}"
    and "finite S"
    and S: "\<forall>p\<in>S. prime p" "n = (\<Prod>p\<in>S. p ^ f p)"
  shows "S = prime_factors n \<and> (\<forall>p. prime p \<longrightarrow> f p = multiplicity p n)"
  using assms by (intro prime_factorization_unique'') auto

lemma prime_factorization_unique_int:
  fixes f :: "int \<Rightarrow> _"
  assumes S_eq: "S = {p. 0 < f p}"
    and "finite S"
    and S: "\<forall>p\<in>S. prime p" "abs n = (\<Prod>p\<in>S. p ^ f p)"
  shows "S = prime_factors n \<and> (\<forall>p. prime p \<longrightarrow> f p = multiplicity p n)"
  using assms by (intro prime_factorization_unique'') auto

lemma prime_factors_characterization_nat:
  "S = {p. 0 < f (p::nat)} \<Longrightarrow>
    finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> prime_factors n = S"
  by (rule prime_factorization_unique_nat [THEN conjunct1, symmetric])

lemma prime_factors_characterization'_nat:
  "finite {p. 0 < f (p::nat)} \<Longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow>
      prime_factors (\<Prod>p | 0 < f p. p ^ f p) = {p. 0 < f p}"
  by (rule prime_factors_characterization_nat) auto

lemma prime_factors_characterization_int:
  "S = {p. 0 < f (p::int)} \<Longrightarrow> finite S \<Longrightarrow>
    \<forall>p\<in>S. prime p \<Longrightarrow> abs n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> prime_factors n = S"
  by (rule prime_factorization_unique_int [THEN conjunct1, symmetric])

(* TODO Move *)
lemma abs_setprod: "abs (setprod f A :: 'a :: linordered_idom) = setprod (\<lambda>x. abs (f x)) A"
  by (cases "finite A", induction A rule: finite_induct) (simp_all add: abs_mult)

lemma primes_characterization'_int [rule_format]:
  "finite {p. p \<ge> 0 \<and> 0 < f (p::int)} \<Longrightarrow> \<forall>p. 0 < f p \<longrightarrow> prime p \<Longrightarrow>
      prime_factors (\<Prod>p | p \<ge> 0 \<and> 0 < f p. p ^ f p) = {p. p \<ge> 0 \<and> 0 < f p}"
  by (rule prime_factors_characterization_int) (auto simp: abs_setprod prime_ge_0_int)

lemma multiplicity_characterization_nat:
  "S = {p. 0 < f (p::nat)} \<Longrightarrow> finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> prime p \<Longrightarrow>
    n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> multiplicity p n = f p"
  by (frule prime_factorization_unique_nat [of S f n, THEN conjunct2, rule_format, symmetric]) auto

lemma multiplicity_characterization'_nat: "finite {p. 0 < f (p::nat)} \<longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<longrightarrow> prime p \<longrightarrow>
      multiplicity p (\<Prod>p | 0 < f p. p ^ f p) = f p"
  by (intro impI, rule multiplicity_characterization_nat) auto

lemma multiplicity_characterization_int: "S = {p. 0 < f (p::int)} \<Longrightarrow>
    finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> prime p \<Longrightarrow> n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> multiplicity p n = f p"
  by (frule prime_factorization_unique_int [of S f n, THEN conjunct2, rule_format, symmetric]) 
     (auto simp: abs_setprod power_abs prime_ge_0_int intro!: setprod.cong)

lemma multiplicity_characterization'_int [rule_format]:
  "finite {p. p \<ge> 0 \<and> 0 < f (p::int)} \<Longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow> prime p \<Longrightarrow>
      multiplicity p (\<Prod>p | p \<ge> 0 \<and> 0 < f p. p ^ f p) = f p"
  by (rule multiplicity_characterization_int) (auto simp: prime_ge_0_int)

lemma multiplicity_one_nat [simp]: "multiplicity p (Suc 0) = 0"
  unfolding One_nat_def [symmetric] by (rule multiplicity_one)

lemma multiplicity_eq_nat:
  fixes x and y::nat
  assumes "x > 0" "y > 0" "\<And>p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"
  using multiplicity_eq_imp_eq[of x y] assms by simp

lemma multiplicity_eq_int:
  fixes x y :: int
  assumes "x > 0" "y > 0" "\<And>p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"
  using multiplicity_eq_imp_eq[of x y] assms by simp

lemma multiplicity_prod_prime_powers:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> prime x" "prime p"
  shows   "multiplicity p (\<Prod>p \<in> S. p ^ f p) = (if p \<in> S then f p else 0)"
proof -
  define g where "g = (\<lambda>x. if x \<in> S then f x else 0)"
  define A where "A = Abs_multiset g"
  have "{x. g x > 0} \<subseteq> S" by (auto simp: g_def)
  from finite_subset[OF this assms(1)] have [simp]: "g :  multiset"
    by (simp add: multiset_def)
  from assms have count_A: "count A x = g x" for x unfolding A_def
    by simp
  have set_mset_A: "set_mset A = {x\<in>S. f x > 0}"
    unfolding set_mset_def count_A by (auto simp: g_def)
  with assms have prime: "prime x" if "x \<in># A" for x using that by auto
  from set_mset_A assms have "(\<Prod>p \<in> S. p ^ f p) = (\<Prod>p \<in> S. p ^ g p) "
    by (intro setprod.cong) (auto simp: g_def)
  also from set_mset_A assms have "\<dots> = (\<Prod>p \<in> set_mset A. p ^ g p)"
    by (intro setprod.mono_neutral_right) (auto simp: g_def set_mset_A)
  also have "\<dots> = msetprod A"
    by (auto simp: msetprod_multiplicity count_A set_mset_A intro!: setprod.cong)
  also from assms have "multiplicity p \<dots> = msetsum (image_mset (multiplicity p) A)"
    by (subst prime_elem_multiplicity_msetprod_distrib) (auto dest: prime)
  also from assms have "image_mset (multiplicity p) A = image_mset (\<lambda>x. if x = p then 1 else 0) A"
    by (intro image_mset_cong) (auto simp: prime_multiplicity_other dest: prime)
  also have "msetsum \<dots> = (if p \<in> S then f p else 0)" by (simp add: msetsum_delta count_A g_def)
  finally show ?thesis .
qed

lemma prime_dvd_fact_iff:
  assumes "prime p"
  shows   "p dvd fact n \<longleftrightarrow> p \<le> n"
proof (induction n)
  case 0
  with assms show ?case by auto
next
  case (Suc n)
  have "p dvd fact (Suc n) \<longleftrightarrow> p dvd (Suc n) * fact n" by simp
  also from assms have "\<dots> \<longleftrightarrow> p dvd Suc n \<or> p dvd fact n"
    by (rule prime_dvd_mult_iff)
  also note Suc.IH
  also have "p dvd Suc n \<or> p \<le> n \<longleftrightarrow> p \<le> Suc n"
    by (auto dest: dvd_imp_le simp: le_Suc_eq)
  finally show ?case .
qed

(* TODO Legacy names *)
lemmas prime_imp_coprime_nat = prime_imp_coprime[where ?'a = nat]
lemmas prime_imp_coprime_int = prime_imp_coprime[where ?'a = int]
lemmas prime_dvd_mult_nat = prime_dvd_mult_iff[where ?'a = nat]
lemmas prime_dvd_mult_int = prime_dvd_mult_iff[where ?'a = int]
lemmas prime_dvd_mult_eq_nat = prime_dvd_mult_iff[where ?'a = nat]
lemmas prime_dvd_mult_eq_int = prime_dvd_mult_iff[where ?'a = int]
lemmas prime_dvd_power_nat = prime_dvd_power[where ?'a = nat]
lemmas prime_dvd_power_int = prime_dvd_power[where ?'a = int]
lemmas prime_dvd_power_nat_iff = prime_dvd_power_iff[where ?'a = nat]
lemmas prime_dvd_power_int_iff = prime_dvd_power_iff[where ?'a = int]
lemmas prime_imp_power_coprime_nat = prime_imp_power_coprime[where ?'a = nat]
lemmas prime_imp_power_coprime_int = prime_imp_power_coprime[where ?'a = int]
lemmas primes_coprime_nat = primes_coprime[where ?'a = nat]
lemmas primes_coprime_int = primes_coprime[where ?'a = nat]
lemmas prime_divprod_pow_nat = prime_elem_divprod_pow[where ?'a = nat]
lemmas prime_exp = prime_elem_power_iff[where ?'a = nat]

end
