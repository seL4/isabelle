(*  Title:      HOL/Library/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

header {*
  \title{The Greatest Common Divisor and Euclid's algorithm}
  \author{Christophe Tabacznyj and Lawrence C Paulson}
*}

theory Primes = Main:

text {*
  See \cite{davenport92}.
  \bigskip
*}

consts
  gcd  :: "nat \<times> nat => nat"  -- {* Euclid's algorithm *}

recdef gcd  "measure ((\<lambda>(m, n). n) :: nat \<times> nat => nat)"
  "gcd (m, n) = (if n = 0 then m else gcd (n, m mod n))"

constdefs
  is_gcd :: "nat => nat => nat => bool"  -- {* @{term gcd} as a relation *}
  "is_gcd p m n == p dvd m \<and> p dvd n \<and>
    (\<forall>d. d dvd m \<and> d dvd n --> d dvd p)"

  coprime :: "nat => nat => bool"
  "coprime m n == gcd (m, n) = 1"

  prime :: "nat set"
  "prime == {p. 1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p)}"


lemma gcd_induct:
  "(!!m. P m 0) ==>
    (!!m n. 0 < n ==> P n (m mod n) ==> P m n)
  ==> P (m::nat) (n::nat)"
  apply (induct m n rule: gcd.induct)
  apply (case_tac "n = 0")
   apply simp_all
  done


lemma gcd_0 [simp]: "gcd (m, 0) = m"
  apply simp
  done

lemma gcd_non_0: "0 < n ==> gcd (m, n) = gcd (n, m mod n)"
  apply simp
  done

declare gcd.simps [simp del]

lemma gcd_1 [simp]: "gcd (m, Suc 0) = 1"
  apply (simp add: gcd_non_0)
  done

text {*
  \medskip @{term "gcd (m, n)"} divides @{text m} and @{text n}.  The
  conjunctions don't seem provable separately.
*}

lemma gcd_dvd1 [iff]: "gcd (m, n) dvd m"
  and gcd_dvd2 [iff]: "gcd (m, n) dvd n"
  apply (induct m n rule: gcd_induct)
   apply (simp_all add: gcd_non_0)
  apply (blast dest: dvd_mod_imp_dvd)
  done

text {*
  \medskip Maximality: for all @{term m}, @{term n}, @{term k}
  naturals, if @{term k} divides @{term m} and @{term k} divides
  @{term n} then @{term k} divides @{term "gcd (m, n)"}.
*}

lemma gcd_greatest: "k dvd m ==> k dvd n ==> k dvd gcd (m, n)"
  apply (induct m n rule: gcd_induct)
   apply (simp_all add: gcd_non_0 dvd_mod)
  done

lemma gcd_greatest_iff [iff]: "(k dvd gcd (m, n)) = (k dvd m \<and> k dvd n)"
  apply (blast intro!: gcd_greatest intro: dvd_trans)
  done

lemma gcd_zero: "(gcd (m, n) = 0) = (m = 0 \<and> n = 0)"
  by (simp only: dvd_0_left_iff [THEN sym] gcd_greatest_iff)


text {*
  \medskip Function gcd yields the Greatest Common Divisor.
*}

lemma is_gcd: "is_gcd (gcd (m, n)) m n"
  apply (simp add: is_gcd_def gcd_greatest)
  done

text {*
  \medskip Uniqueness of GCDs.
*}

lemma is_gcd_unique: "is_gcd m a b ==> is_gcd n a b ==> m = n"
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_anti_sym)
  done

lemma is_gcd_dvd: "is_gcd m a b ==> k dvd a ==> k dvd b ==> k dvd m"
  apply (auto simp add: is_gcd_def)
  done


text {*
  \medskip Commutativity
*}

lemma is_gcd_commute: "is_gcd k m n = is_gcd k n m"
  apply (auto simp add: is_gcd_def)
  done

lemma gcd_commute: "gcd (m, n) = gcd (n, m)"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (subst is_gcd_commute)
  apply (simp add: is_gcd)
  done

lemma gcd_assoc: "gcd (gcd (k, m), n) = gcd (k, gcd (m, n))"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_trans)
  done

lemma gcd_0_left [simp]: "gcd (0, m) = m"
  apply (simp add: gcd_commute [of 0])
  done

lemma gcd_1_left [simp]: "gcd (Suc 0, m) = 1"
  apply (simp add: gcd_commute [of "Suc 0"])
  done


text {*
  \medskip Multiplication laws
*}

lemma gcd_mult_distrib2: "k * gcd (m, n) = gcd (k * m, k * n)"
    -- {* \cite[page 27]{davenport92} *}
  apply (induct m n rule: gcd_induct)
   apply simp
  apply (case_tac "k = 0")
   apply (simp_all add: mod_geq gcd_non_0 mod_mult_distrib2)
  done

lemma gcd_mult [simp]: "gcd (k, k * n) = k"
  apply (rule gcd_mult_distrib2 [of k 1 n, simplified, symmetric])
  done

lemma gcd_self [simp]: "gcd (k, k) = k"
  apply (rule gcd_mult [of k 1, simplified])
  done

lemma relprime_dvd_mult: "gcd (k, n) = 1 ==> k dvd m * n ==> k dvd m"
  apply (insert gcd_mult_distrib2 [of m k n])
  apply simp
  apply (erule_tac t = m in ssubst)
  apply simp
  done

lemma relprime_dvd_mult_iff: "gcd (k, n) = 1 ==> (k dvd m * n) = (k dvd m)"
  apply (blast intro: relprime_dvd_mult dvd_trans)
  done

lemma prime_imp_relprime: "p \<in> prime ==> \<not> p dvd n ==> gcd (p, n) = 1"
  apply (auto simp add: prime_def)
  apply (drule_tac x = "gcd (p, n)" in spec)
  apply auto
  apply (insert gcd_dvd2 [of p n])
  apply simp
  done

lemma two_is_prime: "2 \<in> prime"
  apply (auto simp add: prime_def)
  apply (case_tac m)
   apply (auto dest!: dvd_imp_le)
  done

text {*
  This theorem leads immediately to a proof of the uniqueness of
  factorization.  If @{term p} divides a product of primes then it is
  one of those primes.
*}

lemma prime_dvd_mult: "p \<in> prime ==> p dvd m * n ==> p dvd m \<or> p dvd n"
  by (blast intro: relprime_dvd_mult prime_imp_relprime)

lemma prime_dvd_square: "p \<in> prime ==> p dvd m^Suc (Suc 0) ==> p dvd m"
  by (auto dest: prime_dvd_mult)

lemma prime_dvd_power_two: "p \<in> prime ==> p dvd m\<twosuperior> ==> p dvd m"
  by (rule prime_dvd_square) (simp_all add: power_two)


text {* \medskip Addition laws *}

lemma gcd_add1 [simp]: "gcd (m + n, n) = gcd (m, n)"
  apply (case_tac "n = 0")
   apply (simp_all add: gcd_non_0)
  done

lemma gcd_add2 [simp]: "gcd (m, m + n) = gcd (m, n)"
  apply (rule gcd_commute [THEN trans])
  apply (subst add_commute)
  apply (simp add: gcd_add1)
  apply (rule gcd_commute)
  done

lemma gcd_add2' [simp]: "gcd (m, n + m) = gcd (m, n)"
  apply (subst add_commute)
  apply (rule gcd_add2)
  done

lemma gcd_add_mult: "gcd (m, k * m + n) = gcd (m, n)"
  apply (induct k)
   apply (simp_all add: gcd_add2 add_assoc)
  done


text {* \medskip More multiplication laws *}

lemma gcd_mult_cancel: "gcd (k, n) = 1 ==> gcd (k * m, n) = gcd (m, n)"
  apply (rule dvd_anti_sym)
   apply (rule gcd_greatest)
    apply (rule_tac n = k in relprime_dvd_mult)
     apply (simp add: gcd_assoc)
     apply (simp add: gcd_commute)
    apply (simp_all add: mult_commute gcd_dvd1 gcd_dvd2)
  apply (blast intro: gcd_dvd1 dvd_trans)
  done

end
