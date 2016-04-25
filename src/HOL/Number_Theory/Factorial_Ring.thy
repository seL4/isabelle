(*  Title:      HOL/Number_Theory/Factorial_Ring.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Factorial (semi)rings\<close>

theory Factorial_Ring
imports Main Primes "~~/src/HOL/Library/Multiset"
begin

context algebraic_semidom
begin

lemma dvd_mult_imp_div:
  assumes "a * c dvd b"
  shows "a dvd b div c"
proof (cases "c = 0")
  case True then show ?thesis by simp
next
  case False
  from \<open>a * c dvd b\<close> obtain d where "b = a * c * d" ..
  with False show ?thesis by (simp add: mult.commute [of a] mult.assoc)
qed

end

class factorial_semiring = normalization_semidom +
  assumes finite_divisors: "a \<noteq> 0 \<Longrightarrow> finite {b. b dvd a \<and> normalize b = b}"
  fixes is_prime :: "'a \<Rightarrow> bool"
  assumes not_is_prime_zero [simp]: "\<not> is_prime 0"
    and is_prime_not_unit: "is_prime p \<Longrightarrow> \<not> is_unit p"
    and no_prime_divisorsI2: "(\<And>b. b dvd a \<Longrightarrow> \<not> is_prime b) \<Longrightarrow> is_unit a"
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

lemma no_prime_divisorsI:
  assumes "\<And>b. b dvd a \<Longrightarrow> normalize b = b \<Longrightarrow> \<not> is_prime b"
  shows "is_unit a"
proof (rule no_prime_divisorsI2)
  fix b
  assume "b dvd a"
  then have "normalize b dvd a"
    by simp
  moreover have "normalize (normalize b) = normalize b"
    by simp
  ultimately have "\<not> is_prime (normalize b)"
    by (rule assms)
  then show "\<not> is_prime b"
    by simp
qed

lemma prime_divisorE:
  assumes "a \<noteq> 0" and "\<not> is_unit a" 
  obtains p where "is_prime p" and "p dvd a"
  using assms no_prime_divisorsI [of a] by blast

lemma is_prime_associated:
  assumes "is_prime p" and "is_prime q" and "q dvd p"
  shows "normalize q = normalize p"
using \<open>q dvd p\<close> proof (rule associatedI)
  from \<open>is_prime q\<close> have "\<not> is_unit q"
    by (simp add: is_prime_not_unit)
  with \<open>is_prime p\<close> \<open>q dvd p\<close> show "p dvd q"
    by (blast intro: is_primeD2)
qed

lemma prime_dvd_mult_iff:  
  assumes "is_prime p"
  shows "p dvd a * b \<longleftrightarrow> p dvd a \<or> p dvd b"
  using assms by (auto dest: is_primeD)

lemma prime_dvd_msetprod:
  assumes "is_prime p"
  assumes dvd: "p dvd msetprod A"
  obtains a where "a \<in># A" and "p dvd a"
proof -
  from dvd have "\<exists>a. a \<in># A \<and> p dvd a"
  proof (induct A)
    case empty then show ?case
    using \<open>is_prime p\<close> by (simp add: is_prime_not_unit)
  next
    case (add A a)
    then have "p dvd msetprod A * a" by simp
    with \<open>is_prime p\<close> consider (A) "p dvd msetprod A" | (B) "p dvd a"
      by (blast dest: is_primeD)
    then show ?case proof cases
      case B then show ?thesis by auto
    next
      case A
      with add.hyps obtain b where "b \<in># A" "p dvd b"
        by auto
      then show ?thesis by auto
    qed
  qed
  with that show thesis by blast
qed

lemma msetprod_eq_iff:
  assumes "\<forall>p\<in>set_mset P. is_prime p \<and> normalize p = p" and "\<forall>p\<in>set_mset Q. is_prime p \<and> normalize p = p"
  shows "msetprod P = msetprod Q \<longleftrightarrow> P = Q" (is "?R \<longleftrightarrow> ?S")
proof
  assume ?S then show ?R by simp
next
  assume ?R then show ?S using assms proof (induct P arbitrary: Q)
    case empty then have Q: "msetprod Q = 1" by simp
    have "Q = {#}"
    proof (rule ccontr)
      assume "Q \<noteq> {#}"
      then obtain r R where "Q = R + {#r#}"
        using multi_nonempty_split by blast 
      moreover with empty have "is_prime r" by simp
      ultimately have "msetprod Q = msetprod R * r"
        by simp
      with Q have "msetprod R * r = 1"
        by simp
      then have "is_unit r"
        by (metis local.dvd_triv_right)
      with \<open>is_prime r\<close> show False by (simp add: is_prime_not_unit)
    qed
    then show ?case by simp
  next
    case (add P p)
    then have "is_prime p" and "normalize p = p"
      and "msetprod Q = msetprod P * p" and "p dvd msetprod Q"
      by auto (metis local.dvd_triv_right)
    with prime_dvd_msetprod
      obtain q where "q \<in># Q" and "p dvd q"
      by blast
    with add.prems have "is_prime q" and "normalize q = q"
      by simp_all
    from \<open>is_prime p\<close> have "p \<noteq> 0"
      by auto 
    from \<open>is_prime q\<close> \<open>is_prime p\<close> \<open>p dvd q\<close>
      have "normalize p = normalize q"
      by (rule is_prime_associated)
    from \<open>normalize p = p\<close> \<open>normalize q = q\<close> have "p = q"
      unfolding \<open>normalize p = normalize q\<close> by simp
    with \<open>q \<in># Q\<close> have "p \<in># Q" by simp
    have "msetprod P = msetprod (Q - {#p#})"
      using \<open>p \<in># Q\<close> \<open>p \<noteq> 0\<close> \<open>msetprod Q = msetprod P * p\<close>
      by (simp add: msetprod_minus)
    then have "P = Q - {#p#}"
      using add.prems(2-3)
      by (auto intro: add.hyps dest: in_diffD)
    with \<open>p \<in># Q\<close> show ?case by simp
  qed
qed

lemma prime_dvd_power_iff:
  assumes "is_prime p"
  shows "p dvd a ^ n \<longleftrightarrow> p dvd a \<and> n > 0"
  using assms by (induct n) (auto dest: is_prime_not_unit is_primeD)

lemma prime_power_dvd_multD:
  assumes "is_prime p"
  assumes "p ^ n dvd a * b" and "n > 0" and "\<not> p dvd a"
  shows "p ^ n dvd b"
using \<open>p ^ n dvd a * b\<close> and \<open>n > 0\<close> proof (induct n arbitrary: b)
  case 0 then show ?case by simp
next
  case (Suc n) show ?case
  proof (cases "n = 0")
    case True with Suc \<open>is_prime p\<close> \<open>\<not> p dvd a\<close> show ?thesis
      by (simp add: prime_dvd_mult_iff)
  next
    case False then have "n > 0" by simp
    from \<open>is_prime p\<close> have "p \<noteq> 0" by auto
    from Suc.prems have *: "p * p ^ n dvd a * b"
      by simp
    then have "p dvd a * b"
      by (rule dvd_mult_left)
    with Suc \<open>is_prime p\<close> \<open>\<not> p dvd a\<close> have "p dvd b"
      by (simp add: prime_dvd_mult_iff)
    moreover define c where "c = b div p"
    ultimately have b: "b = p * c" by simp
    with * have "p * p ^ n dvd p * (a * c)"
      by (simp add: ac_simps)
    with \<open>p \<noteq> 0\<close> have "p ^ n dvd a * c"
      by simp
    with Suc.hyps \<open>n > 0\<close> have "p ^ n dvd c"
      by blast
    with \<open>p \<noteq> 0\<close> show ?thesis
      by (simp add: b)
  qed
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

definition factorization :: "'a \<Rightarrow> 'a multiset option"
  where "factorization a = (if a = 0 then None
    else Some (setsum (\<lambda>p. replicate_mset (Max {n. p ^ n dvd a}) p)
      {p. p dvd a \<and> is_prime p \<and> normalize p = p}))"

lemma factorization_normalize [simp]:
  "factorization (normalize a) = factorization a"
  by (simp add: factorization_def)

lemma factorization_0 [simp]:
  "factorization 0 = None"
  by (simp add: factorization_def)

lemma factorization_eq_None_iff [simp]:
  "factorization a = None \<longleftrightarrow> a = 0"
  by (simp add: factorization_def)

lemma factorization_eq_Some_iff:
  "factorization a = Some P \<longleftrightarrow>
   normalize a = msetprod P \<and> 0 \<notin># P \<and> (\<forall>p \<in> set_mset P. is_prime p \<and> normalize p = p)"
proof (cases "a = 0")
  have [simp]: "0 = msetprod P \<longleftrightarrow> 0 \<in># P"
    using msetprod_zero_iff [of P] by blast
  case True
  then show ?thesis by auto
next
  case False    
  let ?prime_factors = "\<lambda>a. {p. p dvd a \<and> is_prime p \<and> normalize p = p}"
  have "?prime_factors a \<subseteq> {b. b dvd a \<and> normalize b = b}"
    by auto
  moreover from \<open>a \<noteq> 0\<close> have "finite {b. b dvd a \<and> normalize b = b}"
    by (rule finite_divisors)
  ultimately have "finite (?prime_factors a)"
    by (rule finite_subset)
  then show ?thesis using \<open>a \<noteq> 0\<close>
  proof (induct "?prime_factors a" arbitrary: a P)
    case empty then have
      *: "{p. p dvd a \<and> is_prime p \<and> normalize p = p} = {}"
        and "a \<noteq> 0"
      by auto
    from \<open>a \<noteq> 0\<close> have "factorization a = Some {#}"
      by (simp only: factorization_def *) simp
    from * have "normalize a = 1"
      by (auto intro: is_unit_normalize no_prime_divisorsI)
    show ?case (is "?lhs \<longleftrightarrow> ?rhs") proof
      assume ?lhs with \<open>factorization a = Some {#}\<close> \<open>normalize a = 1\<close>
      show ?rhs by simp
    next
      assume ?rhs have "P = {#}"
      proof (rule ccontr)
        assume "P \<noteq> {#}"
        then obtain q Q where "P = Q + {#q#}"
          using multi_nonempty_split by blast
        with \<open>?rhs\<close> \<open>normalize a = 1\<close>
        have "1 = q * msetprod Q" and "is_prime q"
          by (simp_all add: ac_simps)
        then have "is_unit q" by (auto intro: dvdI)
        with \<open>is_prime q\<close> show False
          using is_prime_not_unit by blast
      qed
      with \<open>factorization a = Some {#}\<close> show ?lhs by simp
    qed
  next
    case (insert p F)
    from \<open>insert p F = ?prime_factors a\<close>
    have "?prime_factors a = insert p F"
      by simp
    then have "p dvd a" and "is_prime p" and "normalize p = p" and "p \<noteq> 0"
      by (auto intro!: is_prime_not_zeroI)
    define n where "n = Max {n. p ^ n dvd a}"
    then have "n > 0" and "p ^ n dvd a" and "\<not> p ^ Suc n dvd a" 
    proof -
      define N where "N = {n. p ^ n dvd a}"
      then have n_M: "n = Max N" by (simp add: n_def)
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
      with * have "Max N > 0"
        by (auto simp add: Max_gr_iff)
      then show "n > 0" by (simp add: n_M)
      from * have "Max N \<in> N" by (rule Max_in)
      then have "p ^ Max N dvd a" by (simp add: N_def)
      then show "p ^ n dvd a" by (simp add: n_M)
      from * have "\<forall>n\<in>N. n \<le> Max N"
        by (simp add: Max_le_iff [symmetric])
      then have "p ^ Suc (Max N) dvd a \<Longrightarrow> Suc (Max N) \<le> Max N"
        by (rule bspec) (simp add: N_def)
      then have "\<not> p ^ Suc (Max N) dvd a"
        by auto
      then show "\<not> p ^ Suc n dvd a"
        by (simp add: n_M)
    qed
    define b where "b = a div p ^ n"
    with \<open>p ^ n dvd a\<close> have a: "a = p ^ n * b"
      by simp
    with \<open>\<not> p ^ Suc n dvd a\<close> have "\<not> p dvd b" and "b \<noteq> 0"
      by (auto elim: dvdE simp add: ac_simps)
    have "?prime_factors a = insert p (?prime_factors b)"
    proof (rule set_eqI)
      fix q
      show "q \<in> ?prime_factors a \<longleftrightarrow> q \<in> insert p (?prime_factors b)"
      using \<open>is_prime p\<close> \<open>normalize p = p\<close> \<open>n > 0\<close>
        by (auto simp add: a prime_dvd_mult_iff prime_dvd_power_iff)
          (auto dest: is_prime_associated)
    qed
    with \<open>\<not> p dvd b\<close> have "?prime_factors a - {p} = ?prime_factors b"
      by auto
    with insert.hyps have "F = ?prime_factors b"
      by auto
    then have "?prime_factors b = F"
      by simp
    with \<open>?prime_factors a = insert p (?prime_factors b)\<close> have "?prime_factors a = insert p F"
      by simp
    have equiv: "(\<Sum>p\<in>F. replicate_mset (Max {n. p ^ n dvd a}) p) =
      (\<Sum>p\<in>F. replicate_mset (Max {n. p ^ n dvd b}) p)"
    using refl proof (rule Groups_Big.setsum.cong)
      fix q
      assume "q \<in> F"
      have "{n. q ^ n dvd a} = {n. q ^ n dvd b}"
      proof -
        have "q ^ m dvd a \<longleftrightarrow> q ^ m dvd b" (is "?R \<longleftrightarrow> ?S")
          for m
        proof (cases "m = 0")
          case True then show ?thesis by simp
        next
          case False then have "m > 0" by simp
          show ?thesis
          proof
            assume ?S then show ?R by (simp add: a)
          next
            assume ?R
            then have *: "q ^ m dvd p ^ n * b" by (simp add: a)
            from insert.hyps \<open>q \<in> F\<close>
            have "is_prime q" "normalize q = q" "p \<noteq> q" "q dvd p ^ n * b"
              by (auto simp add: a)
            from \<open>is_prime q\<close> * \<open>m > 0\<close> show ?S
            proof (rule prime_power_dvd_multD)
              have "\<not> q dvd p"
              proof
                assume "q dvd p"
                with \<open>is_prime q\<close> \<open>is_prime p\<close> have "normalize q = normalize p"
                  by (blast intro: is_prime_associated)
                with \<open>normalize p = p\<close> \<open>normalize q = q\<close> \<open>p \<noteq> q\<close> show False
                  by simp
              qed
              with \<open>is_prime q\<close> show "\<not> q dvd p ^ n"
                by (simp add: prime_dvd_power_iff)
            qed
          qed
        qed
        then show ?thesis by auto
      qed
      then show
        "replicate_mset (Max {n. q ^ n dvd a}) q = replicate_mset (Max {n. q ^ n dvd b}) q"
        by simp
    qed
    define Q where "Q = the (factorization b)"
    with \<open>b \<noteq> 0\<close> have [simp]: "factorization b = Some Q"
      by simp
    from \<open>a \<noteq> 0\<close> have "factorization a =
      Some (\<Sum>p\<in>?prime_factors a. replicate_mset (Max {n. p ^ n dvd a}) p)"
      by (simp add: factorization_def)
    also have "\<dots> =
      Some (\<Sum>p\<in>insert p F. replicate_mset (Max {n. p ^ n dvd a}) p)"
      by (simp add: \<open>?prime_factors a = insert p F\<close>)
    also have "\<dots> =
      Some (replicate_mset n p + (\<Sum>p\<in>F. replicate_mset (Max {n. p ^ n dvd a}) p))"
      using \<open>finite F\<close> \<open>p \<notin> F\<close> n_def by simp
    also have "\<dots> =
      Some (replicate_mset n p + (\<Sum>p\<in>F. replicate_mset (Max {n. p ^ n dvd b}) p))"
      using equiv by simp
    also have "\<dots> = Some (replicate_mset n p + the (factorization b))"
      using \<open>b \<noteq> 0\<close> by (simp add: factorization_def \<open>?prime_factors a = insert p F\<close> \<open>?prime_factors b = F\<close>)
    finally have fact_a: "factorization a = 
      Some (replicate_mset n p + Q)"
      by simp
    moreover have "factorization b = Some Q \<longleftrightarrow>
      normalize b = msetprod Q \<and>
      0 \<notin># Q \<and>
      (\<forall>p\<in>#Q. is_prime p \<and> normalize p = p)"
      using \<open>F = ?prime_factors b\<close> \<open>b \<noteq> 0\<close> by (rule insert.hyps)
    ultimately have
      norm_a: "normalize a = msetprod (replicate_mset n p + Q)" and
      prime_Q: "\<forall>p\<in>set_mset Q. is_prime p \<and> normalize p = p"
      by (simp_all add: a normalize_mult normalize_power \<open>normalize p = p\<close>)
    show ?case (is "?lhs \<longleftrightarrow> ?rhs") proof
      assume ?lhs with fact_a
      have "P = replicate_mset n p + Q" by simp
      with \<open>n > 0\<close> \<open>is_prime p\<close> \<open>normalize p = p\<close> prime_Q
        show ?rhs by (auto simp add: norm_a dest: is_prime_not_zeroI)
    next
      assume ?rhs
      with \<open>n > 0\<close> \<open>is_prime p\<close> \<open>normalize p = p\<close> \<open>n > 0\<close> prime_Q
      have "msetprod P = msetprod (replicate_mset n p + Q)"
        and "\<forall>p\<in>set_mset P. is_prime p \<and> normalize p = p"
        and "\<forall>p\<in>set_mset (replicate_mset n p + Q). is_prime p \<and> normalize p = p"
        by (simp_all add: norm_a)
      then have "P = replicate_mset n p + Q"
        by (simp only: msetprod_eq_iff)
      then show ?lhs
        by (simp add: fact_a)
    qed
  qed
qed

lemma factorization_cases [case_names 0 factorization]:
  assumes "0": "a = 0 \<Longrightarrow> P"
  assumes factorization: "\<And>A. a \<noteq> 0 \<Longrightarrow> factorization a = Some A \<Longrightarrow> msetprod A = normalize a
    \<Longrightarrow> 0 \<notin># A \<Longrightarrow> (\<And>p. p \<in># A \<Longrightarrow> normalize p = p) \<Longrightarrow> (\<And>p. p \<in># A \<Longrightarrow> is_prime p) \<Longrightarrow> P"
  shows P
proof (cases "a = 0")
  case True with 0 show P .
next
  case False
  then have "factorization a \<noteq> None" by simp
  then obtain A where "factorization a = Some A" by blast
  moreover from this have "msetprod A = normalize a"
    "0 \<notin># A" "\<And>p. p \<in># A \<Longrightarrow> normalize p = p" "\<And>p. p \<in># A \<Longrightarrow> is_prime p"
    by (auto simp add: factorization_eq_Some_iff)
  ultimately show P using \<open>a \<noteq> 0\<close> factorization by blast
qed

lemma factorizationE:
  assumes "a \<noteq> 0"
  obtains A u where "factorization a = Some A" "normalize a = msetprod A"
    "0 \<notin># A" "\<And>p. p \<in># A \<Longrightarrow> is_prime p" "\<And>p. p \<in># A \<Longrightarrow> normalize p = p"
  using assms by (cases a rule: factorization_cases) simp_all

lemma prime_dvd_mset_prod_iff:
  assumes "is_prime p" "normalize p = p" "\<And>p. p \<in># A \<Longrightarrow> is_prime p" "\<And>p. p \<in># A \<Longrightarrow> normalize p = p"
  shows "p dvd msetprod A \<longleftrightarrow> p \<in># A"
using assms proof (induct A)
  case empty then show ?case by (auto dest: is_prime_not_unit)
next
  case (add A q) then show ?case
    using is_prime_associated [of q p]
    by (simp_all add: prime_dvd_mult_iff, safe, simp_all)
qed

end

class factorial_semiring_gcd = factorial_semiring + gcd +
  assumes gcd_unfold: "gcd a b =
    (if a = 0 then normalize b
     else if b = 0 then normalize a
     else msetprod (the (factorization a) #\<inter> the (factorization b)))"
  and lcm_unfold: "lcm a b =
    (if a = 0 \<or> b = 0 then 0
     else msetprod (the (factorization a) #\<union> the (factorization b)))"
begin

subclass semiring_gcd
proof
  fix a b
  have comm: "gcd a b = gcd b a" for a b
   by (simp add: gcd_unfold ac_simps)
  have "gcd a b dvd a" for a b
  proof (cases a rule: factorization_cases)
    case 0 then show ?thesis by simp
  next
    case (factorization A) note fact_A = this
    then have non_zero: "\<And>p. p \<in>#A \<Longrightarrow> p \<noteq> 0"
      using normalize_0 not_is_prime_zero by blast
    show ?thesis
    proof (cases b rule: factorization_cases)
      case 0 then show ?thesis by (simp add: gcd_unfold)
    next
      case (factorization B) note fact_B = this
      have "msetprod (A #\<inter> B) dvd msetprod A"
      using non_zero proof (induct B arbitrary: A)
        case empty show ?case by simp
      next
        case (add B p) show ?case
        proof (cases "p \<in># A")
          case True then obtain C where "A = C + {#p#}"
            by (metis insert_DiffM2)
          moreover with True add have "p \<noteq> 0" and "\<And>p. p \<in># C \<Longrightarrow> p \<noteq> 0"
            by auto
          ultimately show ?thesis
            using True add.hyps [of C]
            by (simp add: inter_union_distrib_left [symmetric])
        next
          case False with add.prems add.hyps [of A] show ?thesis
            by (simp add: inter_add_right1)
        qed
      qed
      with fact_A fact_B show ?thesis by (simp add: gcd_unfold)
    qed
  qed
  then have "gcd a b dvd a" and "gcd b a dvd b"
    by simp_all
  then show "gcd a b dvd a" and "gcd a b dvd b"
    by (simp_all add: comm)
  show "c dvd gcd a b" if "c dvd a" and "c dvd b" for c
  proof (cases "a = 0 \<or> b = 0 \<or> c = 0")
    case True with that show ?thesis by (auto simp add: gcd_unfold)
  next
    case False then have "a \<noteq> 0" and "b \<noteq> 0" and "c \<noteq> 0"
      by simp_all
    then obtain A B C where fact:
      "factorization a = Some A" "factorization b = Some B" "factorization c = Some C"
      and norm: "normalize a = msetprod A" "normalize b = msetprod B" "normalize c = msetprod C"
      and A: "0 \<notin># A" "\<And>p. p \<in># A \<Longrightarrow> normalize p = p" "\<And>p. p \<in># A \<Longrightarrow> is_prime p"
      and B: "0 \<notin># B" "\<And>p. p \<in># B \<Longrightarrow> normalize p = p" "\<And>p. p \<in># B \<Longrightarrow> is_prime p"
      and C: "0 \<notin># C" "\<And>p. p \<in># C \<Longrightarrow> normalize p = p" "\<And>p. p \<in># C \<Longrightarrow> is_prime p"
      by (blast elim!: factorizationE)
    moreover from that have "normalize c dvd normalize a" and "normalize c dvd normalize b"
      by simp_all
    ultimately have "msetprod C dvd msetprod A" and "msetprod C dvd msetprod B"
      by simp_all
    with A B C have "msetprod C dvd msetprod (A #\<inter> B)"
    proof (induct C arbitrary: A B)
      case empty then show ?case by simp
    next
      case add: (add C p)
      from add.prems
        have p: "p \<noteq> 0" "is_prime p" "normalize p = p" by auto
      from add.prems have prems: "msetprod C * p dvd msetprod A" "msetprod C * p dvd msetprod B"
        by simp_all
      then have "p dvd msetprod A" "p dvd msetprod B"
        by (auto dest: dvd_mult_imp_div dvd_mult_right)
      with p add.prems have "p \<in># A" "p \<in># B"
        by (simp_all add: prime_dvd_mset_prod_iff)
      then obtain A' B' where ABp: "A = {#p#} + A'" "B = {#p#} + B'"
        by (auto dest!: multi_member_split simp add: ac_simps)
      with add.prems prems p have "msetprod C dvd msetprod (A' #\<inter> B')"
        by (auto intro: add.hyps simp add: ac_simps)
      with p have "msetprod ({#p#} + C) dvd msetprod (({#p#} + A') #\<inter> ({#p#} + B'))"
        by (simp add: inter_union_distrib_right [symmetric])
      then show ?case by (simp add: ABp ac_simps)
    qed
    with \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> that fact have "normalize c dvd gcd a b"
      by (simp add: norm [symmetric] gcd_unfold fact)
    then show ?thesis by simp
  qed
  show "normalize (gcd a b) = gcd a b"
    apply (simp add: gcd_unfold)
    apply safe
    apply (rule normalized_msetprodI)
    apply (auto elim: factorizationE)
    done
  show "lcm a b = normalize (a * b) div gcd a b"
    by (auto elim!: factorizationE simp add: gcd_unfold lcm_unfold normalize_mult
      union_diff_inter_eq_sup [symmetric] msetprod_diff inter_subset_eq_union)
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
