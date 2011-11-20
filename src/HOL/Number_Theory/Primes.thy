(*  Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad, Tobias Nipkow


This file deals with properties of primes. Definitions and lemmas are
proved uniformly for the natural numbers and integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on \cite{davenport92}. They introduced
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


header {* Primes *}

theory Primes
imports "~~/src/HOL/GCD"
begin

class prime = one +
  fixes prime :: "'a \<Rightarrow> bool"

instantiation nat :: prime
begin

definition prime_nat :: "nat \<Rightarrow> bool"
  where "prime_nat p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"

instance ..

end

instantiation int :: prime
begin

definition prime_int :: "int \<Rightarrow> bool"
  where "prime_int p = prime (nat p)"

instance ..

end


subsection {* Set up Transfer *}

lemma transfer_nat_int_prime:
  "(x::int) >= 0 \<Longrightarrow> prime (nat x) = prime x"
  unfolding gcd_int_def lcm_int_def prime_int_def by auto

declare transfer_morphism_nat_int[transfer add return:
    transfer_nat_int_prime]

lemma transfer_int_nat_prime: "prime (int x) = prime x"
  unfolding gcd_int_def lcm_int_def prime_int_def by auto

declare transfer_morphism_int_nat[transfer add return:
    transfer_int_nat_prime]


subsection {* Primes *}

lemma prime_odd_nat: "prime (p::nat) \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  unfolding prime_nat_def
  by (metis gcd_lcm_complete_lattice_nat.bot_least nat_even_iff_2_dvd nat_neq_iff odd_1_nat)

lemma prime_odd_int: "prime (p::int) \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  unfolding prime_int_def
  apply (frule prime_odd_nat)
  apply (auto simp add: even_nat_def)
  done

(* FIXME Is there a better way to handle these, rather than making them elim rules? *)

lemma prime_ge_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= 0"
  unfolding prime_nat_def by auto

lemma prime_gt_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p > 0"
  unfolding prime_nat_def by auto

lemma prime_ge_1_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= 1"
  unfolding prime_nat_def by auto

lemma prime_gt_1_nat [elim]: "prime (p::nat) \<Longrightarrow> p > 1"
  unfolding prime_nat_def by auto

lemma prime_ge_Suc_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= Suc 0"
  unfolding prime_nat_def by auto

lemma prime_gt_Suc_0_nat [elim]: "prime (p::nat) \<Longrightarrow> p > Suc 0"
  unfolding prime_nat_def by auto

lemma prime_ge_2_nat [elim]: "prime (p::nat) \<Longrightarrow> p >= 2"
  unfolding prime_nat_def by auto

lemma prime_ge_0_int [elim]: "prime (p::int) \<Longrightarrow> p >= 0"
  unfolding prime_int_def prime_nat_def by auto

lemma prime_gt_0_int [elim]: "prime (p::int) \<Longrightarrow> p > 0"
  unfolding prime_int_def prime_nat_def by auto

lemma prime_ge_1_int [elim]: "prime (p::int) \<Longrightarrow> p >= 1"
  unfolding prime_int_def prime_nat_def by auto

lemma prime_gt_1_int [elim]: "prime (p::int) \<Longrightarrow> p > 1"
  unfolding prime_int_def prime_nat_def by auto

lemma prime_ge_2_int [elim]: "prime (p::int) \<Longrightarrow> p >= 2"
  unfolding prime_int_def prime_nat_def by auto


lemma prime_int_altdef: "prime (p::int) = (1 < p \<and> (\<forall>m \<ge> 0. m dvd p \<longrightarrow>
    m = 1 \<or> m = p))"
  using prime_nat_def [transferred]
  apply (cases "p >= 0")
  apply blast
  apply (auto simp add: prime_ge_0_int)
  done

lemma prime_imp_coprime_nat: "prime (p::nat) \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_nat_def)
  apply (metis gcd_dvd1_nat gcd_dvd2_nat)
  done

lemma prime_imp_coprime_int: "prime (p::int) \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply (unfold prime_int_altdef)
  apply (metis gcd_dvd1_int gcd_dvd2_int gcd_ge_0_int)
  done

lemma prime_dvd_mult_nat: "prime (p::nat) \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: coprime_dvd_mult_nat prime_imp_coprime_nat)

lemma prime_dvd_mult_int: "prime (p::int) \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (blast intro: coprime_dvd_mult_int prime_imp_coprime_int)

lemma prime_dvd_mult_eq_nat [simp]: "prime (p::nat) \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule prime_dvd_mult_nat, auto)

lemma prime_dvd_mult_eq_int [simp]: "prime (p::int) \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  by (rule iffI, rule prime_dvd_mult_int, auto)

lemma not_prime_eq_prod_nat: "(n::nat) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  unfolding prime_nat_def dvd_def apply auto
  by (metis mult_commute linorder_neq_iff linorder_not_le mult_1
      n_less_n_mult_m one_le_mult_iff less_imp_le_nat)

lemma not_prime_eq_prod_int: "(n::int) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  unfolding prime_int_altdef dvd_def
  apply auto
  by (metis div_mult_self1_is_id div_mult_self2_is_id
      int_div_less_self int_one_le_iff_zero_less zero_less_mult_pos less_le)

lemma prime_dvd_power_nat [rule_format]: "prime (p::nat) -->
    n > 0 --> (p dvd x^n --> p dvd x)"
  by (induct n rule: nat_induct) auto

lemma prime_dvd_power_int [rule_format]: "prime (p::int) -->
    n > 0 --> (p dvd x^n --> p dvd x)"
  apply (induct n rule: nat_induct)
  apply auto
  apply (frule prime_ge_0_int)
  apply auto
  done

subsubsection {* Make prime naively executable *}

lemma zero_not_prime_nat [simp]: "~prime (0::nat)"
  by (simp add: prime_nat_def)

lemma zero_not_prime_int [simp]: "~prime (0::int)"
  by (simp add: prime_int_def)

lemma one_not_prime_nat [simp]: "~prime (1::nat)"
  by (simp add: prime_nat_def)

lemma Suc_0_not_prime_nat [simp]: "~prime (Suc 0)"
  by (simp add: prime_nat_def One_nat_def)

lemma one_not_prime_int [simp]: "~prime (1::int)"
  by (simp add: prime_int_def)

lemma prime_nat_code [code]:
    "prime (p::nat) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p)"
  apply (simp add: Ball_def)
  apply (metis less_not_refl prime_nat_def dvd_triv_right not_prime_eq_prod_nat)
  done

lemma prime_nat_simp:
    "prime (p::nat) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> set [2..<p]. \<not> n dvd p)"
  by (auto simp add: prime_nat_code)

lemmas prime_nat_simp_number_of [simp] = prime_nat_simp [of "number_of m"] for m

lemma prime_int_code [code]:
  "prime (p::int) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p)" (is "?L = ?R")
proof
  assume "?L"
  then show "?R"
    by (clarsimp simp: prime_gt_1_int) (metis int_one_le_iff_zero_less prime_int_altdef less_le)
next
  assume "?R"
  then show "?L" by (clarsimp simp: Ball_def) (metis dvdI not_prime_eq_prod_int)
qed

lemma prime_int_simp: "prime (p::int) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> set [2..p - 1]. ~ n dvd p)"
  by (auto simp add: prime_int_code)

lemmas prime_int_simp_number_of [simp] = prime_int_simp [of "number_of m"] for m

lemma two_is_prime_nat [simp]: "prime (2::nat)"
  by simp

lemma two_is_prime_int [simp]: "prime (2::int)"
  by simp

text{* A bit of regression testing: *}

lemma "prime(97::nat)" by simp
lemma "prime(97::int)" by simp
lemma "prime(997::nat)" by eval
lemma "prime(997::int)" by eval


lemma prime_imp_power_coprime_nat: "prime (p::nat) \<Longrightarrow> ~ p dvd a \<Longrightarrow> coprime a (p^m)"
  apply (rule coprime_exp_nat)
  apply (subst gcd_commute_nat)
  apply (erule (1) prime_imp_coprime_nat)
  done

lemma prime_imp_power_coprime_int: "prime (p::int) \<Longrightarrow> ~ p dvd a \<Longrightarrow> coprime a (p^m)"
  apply (rule coprime_exp_int)
  apply (subst gcd_commute_int)
  apply (erule (1) prime_imp_coprime_int)
  done

lemma primes_coprime_nat: "prime (p::nat) \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  apply (rule prime_imp_coprime_nat, assumption)
  apply (unfold prime_nat_def)
  apply auto
  done

lemma primes_coprime_int: "prime (p::int) \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  apply (rule prime_imp_coprime_int, assumption)
  apply (unfold prime_int_altdef)
  apply (metis int_one_le_iff_zero_less less_le)
  done

lemma primes_imp_powers_coprime_nat:
    "prime (p::nat) \<Longrightarrow> prime q \<Longrightarrow> p ~= q \<Longrightarrow> coprime (p^m) (q^n)"
  by (rule coprime_exp2_nat, rule primes_coprime_nat)

lemma primes_imp_powers_coprime_int:
    "prime (p::int) \<Longrightarrow> prime q \<Longrightarrow> p ~= q \<Longrightarrow> coprime (p^m) (q^n)"
  by (rule coprime_exp2_int, rule primes_coprime_int)

lemma prime_factor_nat: "n \<noteq> (1::nat) \<Longrightarrow> \<exists> p. prime p \<and> p dvd n"
  apply (induct n rule: nat_less_induct)
  apply (case_tac "n = 0")
  using two_is_prime_nat
  apply blast
  apply (metis One_nat_def dvd.order_trans dvd_refl less_Suc0 linorder_neqE_nat
    nat_dvd_not_less neq0_conv prime_nat_def)
  done

(* An Isar version:

lemma prime_factor_b_nat:
  fixes n :: nat
  assumes "n \<noteq> 1"
  shows "\<exists>p. prime p \<and> p dvd n"

using `n ~= 1`
proof (induct n rule: less_induct_nat)
  fix n :: nat
  assume "n ~= 1" and
    ih: "\<forall>m<n. m \<noteq> 1 \<longrightarrow> (\<exists>p. prime p \<and> p dvd m)"
  then show "\<exists>p. prime p \<and> p dvd n"
  proof -
  {
    assume "n = 0"
    moreover note two_is_prime_nat
    ultimately have ?thesis
      by (auto simp del: two_is_prime_nat)
  }
  moreover
  {
    assume "prime n"
    then have ?thesis by auto
  }
  moreover
  {
    assume "n ~= 0" and "~ prime n"
    with `n ~= 1` have "n > 1" by auto
    with `~ prime n` and not_prime_eq_prod_nat obtain m k where
      "n = m * k" and "1 < m" and "m < n" by blast
    with ih obtain p where "prime p" and "p dvd m" by blast
    with `n = m * k` have ?thesis by auto
  }
  ultimately show ?thesis by blast
  qed
qed

*)

text {* One property of coprimality is easier to prove via prime factors. *}

lemma prime_divprod_pow_nat:
  assumes p: "prime (p::nat)" and ab: "coprime a b" and pab: "p^n dvd a * b"
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
      have pnba: "p^n dvd b*a" using pab by (simp add: mult_commute)
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

lemma next_prime_bound: "\<exists>(p::nat). prime p \<and> n < p \<and> p <= fact n + 1"
proof-
  have f1: "fact n + 1 \<noteq> 1" using fact_ge_one_nat [of n] by arith 
  from prime_factor_nat [OF f1]
  obtain p where "prime p" and "p dvd fact n + 1" by auto
  then have "p \<le> fact n + 1" apply (intro dvd_imp_le) apply auto done
  { assume "p \<le> n"
    from `prime p` have "p \<ge> 1" 
      by (cases p, simp_all)
    with `p <= n` have "p dvd fact n" 
      by (intro dvd_fact_nat)
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

end
