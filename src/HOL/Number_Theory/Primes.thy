(*  Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad, Tobias Nipkow


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
*)


section {* Primes *}

theory Primes
imports "~~/src/HOL/GCD" "~~/src/HOL/Binomial"
begin

declare [[coercion int]]
declare [[coercion_enabled]]

definition prime :: "nat \<Rightarrow> bool"
  where "prime p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"

lemmas prime_nat_def = prime_def


subsection {* Primes *}

lemma prime_odd_nat: "prime p \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  apply (auto simp add: prime_nat_def even_iff_mod_2_eq_zero dvd_eq_mod_eq_0)
  apply (metis dvd_eq_mod_eq_0 even_Suc even_iff_mod_2_eq_zero mod_by_1 nat_dvd_not_less not_mod_2_eq_0_eq_1 zero_less_numeral)
  done

(* FIXME Is there a better way to handle these, rather than making them elim rules? *)

lemma prime_gt_0_nat [elim]: "prime p \<Longrightarrow> p > 0"
  unfolding prime_nat_def by auto

lemma prime_ge_1_nat [elim]: "prime p \<Longrightarrow> p >= 1"
  unfolding prime_nat_def by auto

lemma prime_gt_1_nat [elim]: "prime p \<Longrightarrow> p > 1"
  unfolding prime_nat_def by auto

lemma prime_ge_Suc_0_nat [elim]: "prime p \<Longrightarrow> p >= Suc 0"
  unfolding prime_nat_def by auto

lemma prime_gt_Suc_0_nat [elim]: "prime p \<Longrightarrow> p > Suc 0"
  unfolding prime_nat_def by auto

lemma prime_ge_2_nat [elim]: "prime p \<Longrightarrow> p >= 2"
  unfolding prime_nat_def by auto

lemma prime_imp_coprime_nat: "prime p \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_nat_def)
  apply (metis gcd_dvd1_nat gcd_dvd2_nat)
  done

lemma prime_int_altdef:
  "prime p = (1 < p \<and> (\<forall>m::int. m \<ge> 0 \<longrightarrow> m dvd p \<longrightarrow>
    m = 1 \<or> m = p))"
  apply (simp add: prime_def)
  apply (auto simp add: )
  apply (metis One_nat_def int_1 nat_0_le nat_dvd_iff)
  apply (metis zdvd_int One_nat_def le0 of_nat_0 of_nat_1 of_nat_eq_iff of_nat_le_iff)
  done

lemma prime_imp_coprime_int:
  fixes n::int shows "prime p \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_int_altdef)
  apply (metis gcd_dvd1_int gcd_dvd2_int gcd_ge_0_int)
  done

lemma prime_dvd_mult_nat: "prime p \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: coprime_dvd_mult_nat prime_imp_coprime_nat)

lemma prime_dvd_mult_int:
  fixes n::int shows "prime p \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: coprime_dvd_mult_int prime_imp_coprime_int)

lemma prime_dvd_mult_eq_nat [simp]: "prime p \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule prime_dvd_mult_nat, auto)

lemma prime_dvd_mult_eq_int [simp]:
  fixes n::int
  shows "prime p \<Longrightarrow> p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule prime_dvd_mult_int, auto)

lemma not_prime_eq_prod_nat: "(n::nat) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  unfolding prime_nat_def dvd_def apply auto
  by (metis mult.commute linorder_neq_iff linorder_not_le mult_1
      n_less_n_mult_m one_le_mult_iff less_imp_le_nat)

lemma prime_dvd_power_nat: "prime p \<Longrightarrow> p dvd x^n \<Longrightarrow> p dvd x"
  by (induct n) auto

lemma prime_dvd_power_int:
  fixes x::int shows "prime p \<Longrightarrow> p dvd x^n \<Longrightarrow> p dvd x"
  by (induct n) auto

lemma prime_dvd_power_nat_iff: "prime p \<Longrightarrow> n > 0 \<Longrightarrow>
    p dvd x^n \<longleftrightarrow> p dvd x"
  by (cases n) (auto elim: prime_dvd_power_nat)

lemma prime_dvd_power_int_iff:
  fixes x::int
  shows "prime p \<Longrightarrow> n > 0 \<Longrightarrow> p dvd x^n \<longleftrightarrow> p dvd x"
  by (cases n) (auto elim: prime_dvd_power_int)


subsubsection {* Make prime naively executable *}

lemma zero_not_prime_nat [simp]: "~prime (0::nat)"
  by (simp add: prime_nat_def)

lemma one_not_prime_nat [simp]: "~prime (1::nat)"
  by (simp add: prime_nat_def)

lemma Suc_0_not_prime_nat [simp]: "~prime (Suc 0)"
  by (simp add: prime_nat_def)

lemma prime_nat_code [code]:
    "prime p \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p)"
  apply (simp add: Ball_def)
  apply (metis One_nat_def less_not_refl prime_nat_def dvd_triv_right not_prime_eq_prod_nat)
  done

lemma prime_nat_simp:
    "prime p \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> set [2..<p]. \<not> n dvd p)"
  by (auto simp add: prime_nat_code)

lemmas prime_nat_simp_numeral [simp] = prime_nat_simp [of "numeral m"] for m

lemma two_is_prime_nat [simp]: "prime (2::nat)"
  by simp

text{* A bit of regression testing: *}

lemma "prime(97::nat)" by simp
lemma "prime(997::nat)" by eval


lemma prime_imp_power_coprime_nat: "prime p \<Longrightarrow> ~ p dvd a \<Longrightarrow> coprime a (p^m)"
  by (metis coprime_exp_nat gcd_nat.commute prime_imp_coprime_nat)

lemma prime_imp_power_coprime_int:
  fixes a::int shows "prime p \<Longrightarrow> ~ p dvd a \<Longrightarrow> coprime a (p^m)"
  by (metis coprime_exp_int gcd_int.commute prime_imp_coprime_int)

lemma primes_coprime_nat: "prime p \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  by (metis gcd_nat.absorb1 gcd_nat.absorb2 prime_imp_coprime_nat)

lemma primes_imp_powers_coprime_nat:
    "prime p \<Longrightarrow> prime q \<Longrightarrow> p ~= q \<Longrightarrow> coprime (p^m) (q^n)"
  by (rule coprime_exp2_nat, rule primes_coprime_nat)

lemma prime_factor_nat: "n \<noteq> (1::nat) \<Longrightarrow> \<exists> p. prime p \<and> p dvd n"
  apply (induct n rule: nat_less_induct)
  apply (case_tac "n = 0")
  using two_is_prime_nat
  apply blast
  apply (metis One_nat_def dvd.order_trans dvd_refl less_Suc0 linorder_neqE_nat
    nat_dvd_not_less neq0_conv prime_nat_def)
  done

text {* One property of coprimality is easier to prove via prime factors. *}

lemma prime_divprod_pow_nat:
  assumes p: "prime p" and ab: "coprime a b" and pab: "p^n dvd a * b"
  shows "p^n dvd a \<or> p^n dvd b"
proof-
  { assume "n = 0 \<or> a = 1 \<or> b = 1" with pab have ?thesis
      apply (cases "n=0", simp_all)
      apply (cases "a=1", simp_all)
      done }
  moreover
  { assume n: "n \<noteq> 0" and a: "a\<noteq>1" and b: "b\<noteq>1"
    then obtain m where m: "n = Suc m" by (cases n) auto
    from n have "p dvd p^n" apply (intro dvd_power) apply auto done
    also note pab
    finally have pab': "p dvd a * b".
    from prime_dvd_mult_nat[OF p pab']
    have "p dvd a \<or> p dvd b" .
    moreover
    { assume pa: "p dvd a"
      from coprime_common_divisor_nat [OF ab, OF pa] p have "\<not> p dvd b" by auto
      with p have "coprime b p"
        by (subst gcd_commute_nat, intro prime_imp_coprime_nat)
      then have pnb: "coprime (p^n) b"
        by (subst gcd_commute_nat, rule coprime_exp_nat)
      from coprime_dvd_mult_nat[OF pnb pab] have ?thesis by blast }
    moreover
    { assume pb: "p dvd b"
      have pnba: "p^n dvd b*a" using pab by (simp add: mult.commute)
      from coprime_common_divisor_nat [OF ab, of p] pb p have "\<not> p dvd a"
        by auto
      with p have "coprime a p"
        by (subst gcd_commute_nat, intro prime_imp_coprime_nat)
      then have pna: "coprime (p^n) a"
        by (subst gcd_commute_nat, rule coprime_exp_nat)
      from coprime_dvd_mult_nat[OF pna pnba] have ?thesis by blast }
    ultimately have ?thesis by blast }
  ultimately show ?thesis by blast
qed


subsection {* Infinitely many primes *}

lemma next_prime_bound: "\<exists>p. prime p \<and> n < p \<and> p <= fact n + 1"
proof-
  have f1: "fact n + 1 \<noteq> (1::nat)" using fact_ge_1 [of n, where 'a=nat] by arith
  from prime_factor_nat [OF f1]
  obtain p where "prime p" and "p dvd fact n + 1" by auto
  then have "p \<le> fact n + 1" apply (intro dvd_imp_le) apply auto done
  { assume "p \<le> n"
    from `prime p` have "p \<ge> 1"
      by (cases p, simp_all)
    with `p <= n` have "p dvd fact n"
      by (intro dvd_fact)
    with `p dvd fact n + 1` have "p dvd fact n + 1 - fact n"
      by (rule dvd_diff_nat)
    then have "p dvd 1" by simp
    then have "p <= 1" by auto
    moreover from `prime p` have "p > 1" by auto
    ultimately have False by auto}
  then have "n < p" by presburger
  with `prime p` and `p <= fact n + 1` show ?thesis by auto
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

subsection{*Powers of Primes*}

text{*Versions for type nat only*}

lemma prime_product:
  fixes p::nat
  assumes "prime (p * q)"
  shows "p = 1 \<or> q = 1"
proof -
  from assms have
    "1 < p * q" and P: "\<And>m. m dvd p * q \<Longrightarrow> m = 1 \<or> m = p * q"
    unfolding prime_nat_def by auto
  from `1 < p * q` have "p \<noteq> 0" by (cases p) auto
  then have Q: "p = p * q \<longleftrightarrow> q = 1" by auto
  have "p dvd p * q" by simp
  then have "p = 1 \<or> p = p * q" by (rule P)
  then show ?thesis by (simp add: Q)
qed

lemma prime_exp:
  fixes p::nat
  shows "prime (p^n) \<longleftrightarrow> prime p \<and> n = 1"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  {assume "p = 0" hence ?case by simp}
  moreover
  {assume "p=1" hence ?case by simp}
  moreover
  {assume p: "p \<noteq> 0" "p\<noteq>1"
    {assume pp: "prime (p^Suc n)"
      hence "p = 1 \<or> p^n = 1" using prime_product[of p "p^n"] by simp
      with p have n: "n = 0"
        by (metis One_nat_def nat_power_eq_Suc_0_iff)
      with pp have "prime p \<and> Suc n = 1" by simp}
    moreover
    {assume n: "prime p \<and> Suc n = 1" hence "prime (p^Suc n)" by simp}
    ultimately have ?case by blast}
  ultimately show ?case by blast
qed

lemma prime_power_mult:
  fixes p::nat
  assumes p: "prime p" and xy: "x * y = p ^ k"
  shows "\<exists>i j. x = p ^i \<and> y = p^ j"
using xy
proof(induct k arbitrary: x y)
  case 0 thus ?case apply simp by (rule exI[where x="0"], simp)
next
  case (Suc k x y)
  from Suc.prems have pxy: "p dvd x*y" by auto
  from Primes.prime_dvd_mult_nat [OF p pxy] have pxyc: "p dvd x \<or> p dvd y" .
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

lemma prime_power_exp:
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
    from prime_power_mult[OF p th]
    obtain i j where ij: "x = p^i" "x^n = p^j"by blast
    from Suc.hyps[OF n ij(2)] have ?case .}
  ultimately show ?case by blast
qed

lemma divides_primepow:
  fixes p::nat
  assumes p: "prime p"
  shows "d dvd p^k \<longleftrightarrow> (\<exists> i. i \<le> k \<and> d = p ^i)"
proof
  assume H: "d dvd p^k" then obtain e where e: "d*e = p^k"
    unfolding dvd_def  apply (auto simp add: mult.commute) by blast
  from prime_power_mult[OF p e] obtain i j where ij: "d = p^i" "e=p^j" by blast
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

subsection {*Chinese Remainder Theorem Variants*}

lemma bezout_gcd_nat:
  fixes a::nat shows "\<exists>x y. a * x - b * y = gcd a b \<or> b * x - a * y = gcd a b"
  using bezout_nat[of a b]
by (metis bezout_nat diff_add_inverse gcd_add_mult_nat gcd_nat.commute
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


text {* A binary form of the Chinese Remainder Theorem. *}

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

text {* Primality *}

lemma coprime_bezout_strong:
  fixes a::nat assumes "coprime a b"  "b \<noteq> 1"
  shows "\<exists>x y. a * x = b * y + 1"
by (metis assms bezout_nat gcd_nat.left_neutral)

lemma bezout_prime:
  assumes p: "prime p" and pa: "\<not> p dvd a"
  shows "\<exists>x y. a*x = Suc (p*y)"
proof-
  have ap: "coprime a p"
    by (metis gcd_nat.commute p pa prime_imp_coprime_nat)
  from coprime_bezout_strong[OF ap] show ?thesis
    by (metis Suc_eq_plus1 gcd_lcm_complete_lattice_nat.bot.extremum pa)
qed

end
