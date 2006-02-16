(*  Title:      HOL/Library/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

header {* Primality on nat *}

theory Primes
imports Main
begin

definition
  coprime :: "nat => nat => bool"
  "coprime m n = (gcd (m, n) = 1)"

  prime :: "nat \<Rightarrow> bool"
  "prime p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"


lemma two_is_prime: "prime 2"
  apply (auto simp add: prime_def)
  apply (case_tac m)
   apply (auto dest!: dvd_imp_le)
  done

lemma prime_imp_relprime: "prime p ==> \<not> p dvd n ==> gcd (p, n) = 1"
  apply (auto simp add: prime_def)
  apply (drule_tac x = "gcd (p, n)" in spec)
  apply auto
  apply (insert gcd_dvd2 [of p n])
  apply simp
  done

text {*
  This theorem leads immediately to a proof of the uniqueness of
  factorization.  If @{term p} divides a product of primes then it is
  one of those primes.
*}

lemma prime_dvd_mult: "prime p ==> p dvd m * n ==> p dvd m \<or> p dvd n"
  by (blast intro: relprime_dvd_mult prime_imp_relprime)

lemma prime_dvd_square: "prime p ==> p dvd m^Suc (Suc 0) ==> p dvd m"
  by (auto dest: prime_dvd_mult)

lemma prime_dvd_power_two: "prime p ==> p dvd m\<twosuperior> ==> p dvd m"
  by (rule prime_dvd_square) (simp_all add: power2_eq_square)


end
