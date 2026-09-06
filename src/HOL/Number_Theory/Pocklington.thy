(*  Title:      HOL/Number_Theory/Pocklington.thy
    Author:     Amine Chaieb, Manuel Eberl
*)

section \<open>Pocklington's Theorem for Primes\<close>

theory Pocklington
imports Residues
begin

subsection \<open>Lemmas about previously defined terms\<close>

lemma prime_nat_iff'': "prime (p::nat) \<longleftrightarrow> p \<noteq> 0 \<and> p \<noteq> 1 \<and> (\<forall>m. 0 < m \<and> m < p \<longrightarrow> coprime p m)"
proof -
have \<section>: "\<And>m. \<lbrakk>0 < p; \<forall>m. 0 < m \<and> m < p \<longrightarrow> coprime p m; m dvd p; m \<noteq> p\<rbrakk>
         \<Longrightarrow> m = Suc 0"
  by (metis One_nat_def coprime_absorb_right dvd_1_iff_1 dvd_nat_bounds
      nless_le)
  show ?thesis
    by (auto simp: nat_dvd_not_less prime_imp_coprime_nat prime_nat_iff elim!: \<section>)
qed

lemma finite_number_segment: "card { m. 0 < m \<and> m < n } = n - 1"
proof -
  have "{ m. 0 < m \<and> m < n } = {1..<n}" by auto
  then show ?thesis by simp
qed


subsection \<open>Some basic theorems about solving congruences\<close>

lemma cong_solve:
  fixes n :: nat
  assumes an: "coprime a n"
  shows "\<exists>x. [a * x = b] (mod n)"
proof (cases "a = 0")
  case True
  with an show ?thesis
    by (simp add: cong_def)
next
  case False
  from bezout_add_strong_nat [OF this]
  obtain d x y where dxy: "d dvd a" "d dvd n" "a * x = n * y + d" by blast
  then have d1: "d = 1"
    using assms coprime_common_divisor [of a n d] by simp
  with dxy(3) have "a * x * b = (n * y + 1) * b"
    by simp
  then have "a * (x * b) = n * (y * b) + b"
    by (auto simp: algebra_simps)
  then have "a * (x * b) mod n = (n * (y * b) + b) mod n"
    by simp
  then have "a * (x * b) mod n = b mod n"
    by (simp add: mod_add_left_eq)
  then have "[a * (x * b) = b] (mod n)"
    by (simp only: cong_def)
  then show ?thesis by blast
qed

lemma cong_solve_unique:
  fixes n :: nat
  assumes an: "coprime a n" and nz: "n \<noteq> 0"
  shows "\<exists>!x. x < n \<and> [a * x = b] (mod n)"
proof -
  from cong_solve[OF an] obtain x where x: "[a * x = b] (mod n)"
    by blast
  let ?P = "\<lambda>x. x < n \<and> [a * x = b] (mod n)"
  let ?x = "x mod n"
  from x have *: "[a * ?x = b] (mod n)"
    by (simp add: cong_def mod_mult_right_eq[of a x n])
  from mod_less_divisor[ of n x] nz * have Px: "?P ?x" by simp
  have "y = ?x" if Py: "y < n" "[a * y = b] (mod n)" for y
  proof -
    from Py(2) * have "[a * y = a * ?x] (mod n)"
      by (simp add: cong_def)
    then have "[y = ?x] (mod n)"
      by (metis an cong_mult_lcancel_nat)
    with mod_less[OF Py(1)] mod_less_divisor[ of n x] nz
    show ?thesis
      by (simp add: cong_def)
  qed
  with Px show ?thesis by blast
qed

lemma cong_solve_unique_nontrivial:
  fixes p :: nat
  assumes p: "prime p"
    and pa: "coprime p a"
    and x0: "0 < x"
    and xp: "x < p"
  shows "\<exists>!y. 0 < y \<and> y < p \<and> [x * y = a] (mod p)"
proof -
  from pa have ap: "coprime a p"
    by (simp add: ac_simps)
  from x0 xp p have px: "coprime x p"
    by (auto simp add: prime_nat_iff'' ac_simps)
  obtain y where y: "y < p" "[x * y = a] (mod p)" "\<forall>z. z < p \<and> [x * z = a] (mod p) \<longrightarrow> z = y"
    by (metis cong_solve_unique neq0_conv p prime_gt_0_nat px)
  have "y \<noteq> 0"
  proof
    assume "y = 0"
    with y(2) have "p dvd a"
      using cong_dvd_iff by auto
    with not_prime_1 p pa show False
      by (auto simp add: gcd_nat.order_iff)
  qed
  with y show ?thesis
    by blast
qed

lemma cong_unique_inverse_prime:
  fixes p :: nat
  assumes "prime p" and "0 < x" and "x < p"
  shows "\<exists>!y. 0 < y \<and> y < p \<and> [x * y = 1] (mod p)"
  by (rule cong_solve_unique_nontrivial) (use assms in simp_all)

lemma chinese_remainder_coprime_unique:
  fixes a :: nat
  assumes ab: "coprime a b" and az: "a \<noteq> 0" and bz: "b \<noteq> 0"
    and ma: "coprime m a" and nb: "coprime n b"
  shows "\<exists>!x. coprime x (a * b) \<and> x < a * b \<and> [x = m] (mod a) \<and> [x = n] (mod b)"
proof -
  let ?P = "\<lambda>x. x < a * b \<and> [x = m] (mod a) \<and> [x = n] (mod b)"
  from binary_chinese_remainder_unique_nat[OF ab az bz]
  obtain x where x: "x < a * b" "[x = m] (mod a)" "[x = n] (mod b)" "\<forall>y. ?P y \<longrightarrow> y = x"
    by blast
  from ma nb x have "coprime x a" "coprime x b"
    using cong_imp_coprime cong_sym by blast+
  then have "coprime x (a*b)"
    by simp
  with x show ?thesis
    by blast
qed


subsection \<open>Another trivial primality characterization\<close>

lemma prime_prime_factor: "prime n \<longleftrightarrow> n \<noteq> 1 \<and> (\<forall>p. prime p \<and> p dvd n \<longrightarrow> p = n)"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for n :: nat
proof (cases "n = 0 \<or> n = 1")
  case True
  then show ?thesis
     by (metis bigger_prime dvd_0_right not_prime_1 not_prime_0)
next
  case False
  show ?thesis
  proof
    assume "prime n"
    then show ?rhs
      by (metis not_prime_1 prime_nat_iff)
  next
    assume ?rhs
    with False show "prime n"
      by (auto simp: prime_nat_iff) (metis One_nat_def prime_factor_nat prime_nat_iff)
  qed
qed

lemma prime_divisor_sqrt: "prime n \<longleftrightarrow> n \<noteq> 1 \<and> (\<forall>d. d dvd n \<and> d\<^sup>2 \<le> n \<longrightarrow> d = 1)"
  for n :: nat
proof -
  consider "n = 0" | "n = 1" | "n \<noteq> 0" "n \<noteq> 1" by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    then show ?thesis by simp
  next
    case n: 3
    then have np: "n > 1" by arith
    {
      fix d
      assume d: "d dvd n" "d\<^sup>2 \<le> n"
        and H: "\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n"
      from H d have d1n: "d = 1 \<or> d = n" by blast
      then have "d = 1"
      proof
        assume dn: "d = n"
        from n have "n\<^sup>2 > n * 1"
          by (simp add: power2_eq_square)
        with dn d(2) show ?thesis by simp
      qed
    }
    moreover
    {
      fix d assume d: "d dvd n" and H: "\<forall>d'. d' dvd n \<and> d'\<^sup>2 \<le> n \<longrightarrow> d' = 1"
      from d n have "d \<noteq> 0"
        by (metis dvd_0_left_iff)
      then have dp: "d > 0" by simp
      from d[unfolded dvd_def] obtain e where e: "n= d*e" by blast
      from n dp e have ep:"e > 0" by simp
      from dp ep have "d\<^sup>2 \<le> n \<or> e\<^sup>2 \<le> n"
        by (auto simp add: e power2_eq_square mult_le_cancel_left)
      then have "d = 1 \<or> d = n"
      proof
        assume "d\<^sup>2 \<le> n"
        with H[rule_format, of d] d have "d = 1" by blast
        then show ?thesis ..
      next
        assume h: "e\<^sup>2 \<le> n"
        from e have "e dvd n" by (simp add: dvd_def mult.commute)
        with H[rule_format, of e] h have "e = 1" by simp
        with e have "d = n" by simp
        then show ?thesis ..
      qed
    }
    ultimately show ?thesis
      unfolding prime_nat_iff using np n(2) by blast
  qed
qed

lemma prime_prime_factor_sqrt:
  "prime (n::nat) \<longleftrightarrow> n \<noteq> 0 \<and> n \<noteq> 1 \<and> (\<nexists>p. prime p \<and> p dvd n \<and> p\<^sup>2 \<le> n)"
  (is "?lhs \<longleftrightarrow>?rhs")
proof -
  consider "n = 0" | "n = 1" | "n \<noteq> 0" "n \<noteq> 1"
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (metis not_prime_0)
  next
    case 2
    then show ?thesis by (metis not_prime_1)
  next
    case n: 3
    show ?thesis
    proof
      assume ?lhs
      from this[unfolded prime_divisor_sqrt] n show ?rhs
        by (metis prime_prime_factor)
    next
      assume ?rhs
      {
        fix d
        assume d: "d dvd n" "d\<^sup>2 \<le> n" "d \<noteq> 1"
        then obtain p where p: "prime p" "p dvd d"
          by (metis prime_factor_nat)
        from d(1) n have dp: "d > 0"
          by (metis dvd_0_left neq0_conv)
        from mult_mono[OF dvd_imp_le[OF p(2) dp] dvd_imp_le[OF p(2) dp]] d(2)
        have "p\<^sup>2 \<le> n" unfolding power2_eq_square by arith
        with \<open>?rhs\<close> n p(1) dvd_trans[OF p(2) d(1)] have False
          by blast
      }
      with n prime_divisor_sqrt show ?lhs by auto
    qed
  qed
qed


subsection \<open>Pocklington theorem\<close>

lemma pocklington_lemma:
  fixes p :: nat
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q * r"
    and an: "[a^ (n - 1) = 1] (mod n)"
    and aq: "\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a ^ ((n - 1) div p) - 1) n"
    and pp: "prime p" and pn: "p dvd n"
  shows "[p = 1] (mod q)"
proof -
  have p01: "p \<noteq> 0" "p \<noteq> 1"
    using pp by (auto intro: prime_gt_0_nat)
  obtain k where k: "a ^ (q * r) - 1 = n * k"
    by (metis an cong_to_1_nat dvd_def nqr)
  from pn[unfolded dvd_def] obtain l where l: "n = p * l"
    by blast
  have a0: "a \<noteq> 0"
  proof
    assume "a = 0"
    with n have "a^ (n - 1) = 0"
      by (simp add: power_0_left)
    with n an mod_less[of 1 n] show False
      by (simp add: power_0_left cong_def)
  qed
  with n nqr have aqr0: "a ^ (q * r) \<noteq> 0"
    by simp
  then have "(a ^ (q * r) - 1) + 1  = a ^ (q * r)"
    by simp
  with k l have "a ^ (q * r) = p * l * k + 1"
    by simp
  then have "a ^ (r * q) + p * 0 = 1 + p * (l * k)"
    by (simp add: ac_simps)
  then have odq: "ord p (a^r) dvd q"
    unfolding ord_divides[symmetric] power_mult[symmetric]
    by (metis an cong_dvd_modulus_nat mult.commute nqr pn)
  from odq[unfolded dvd_def] obtain d where d: "q = ord p (a^r) * d"
    by blast
  have d1: "d = 1"
  proof (rule ccontr)
    assume d1: "d \<noteq> 1"
    obtain P where P: "prime P" "P dvd d"
      by (metis d1 prime_factor_nat)
    from d dvd_mult[OF P(2), of "ord p (a^r)"] have Pq: "P dvd q" by simp
    from aq P(1) Pq have caP:"coprime (a^ ((n - 1) div P) - 1) n" by blast
    from Pq obtain s where s: "q = P*s" unfolding dvd_def by blast
    from P(1) have P0: "P \<noteq> 0"
      by (metis not_prime_0)
    from P(2) obtain t where t: "d = P*t" unfolding dvd_def by blast
    from d s t P0  have s': "ord p (a^r) * t = s"
      by (metis mult.commute mult_cancel1 mult.assoc)
    have "ord p (a^r) * t*r = r * ord p (a^r) * t"
      by (metis mult.assoc mult.commute)
    then have exps: "a^(ord p (a^r) * t*r) = ((a ^ r) ^ ord p (a^r)) ^ t"
      by (simp only: power_mult)
    then have "[((a ^ r) ^ ord p (a^r)) ^ t= 1] (mod p)"
      by (metis cong_pow ord power_one)
    then have pd0: "p dvd a^(ord p (a^r) * t*r) - 1"
      by (metis cong_to_1_nat exps)
    from nqr s s' have "(n - 1) div P = ord p (a^r) * t*r"
      using P0 by simp
    with caP have "coprime (a ^ (ord p (a ^ r) * t * r) - 1) n"
      by simp
    with p01 pn pd0 coprime_common_divisor [of _ n p] show False
      by auto
  qed
  with d have o: "ord p (a^r) = q" by simp
  from pp totient_prime [of p] have totient_eq: "totient p = p - 1"
    by simp
  {
    fix d
    assume d: "d dvd p" "d dvd a" "d \<noteq> 1"
    from pp[unfolded prime_nat_iff] d have dp: "d = p" by blast
    from n have "n \<noteq> 0" by simp
    then have False using d dp pn an
      by auto (metis One_nat_def Suc_lessI
        \<open>1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> m = 1 \<or> m = p)\<close> \<open>a ^ (q * r) = p * l * k + 1\<close> add_diff_cancel_left' dvd_diff_nat dvd_power dvd_triv_left gcd_nat.trans nat_dvd_not_less nqr zero_less_diff zero_less_one) 
  }
  then have cpa: "coprime p a"
    by (auto intro: coprimeI)
  then have arp: "coprime (a ^ r) p"
    by (cases "r > 0") (simp_all add: ac_simps)
  from euler_theorem [OF arp, simplified ord_divides] o totient_eq have "q dvd (p - 1)"
    by simp
  then obtain d where d:"p - 1 = q * d"
    unfolding dvd_def by blast
  have "p \<noteq> 0"
    by (metis p01(1))
  with d have "p + q * 0 = 1 + q * d" by simp
  then show ?thesis
    by (metis cong_iff_lin_nat mult.commute)
qed

theorem pocklington:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q * r" and sqr: "n \<le> q\<^sup>2"
    and an: "[a^ (n - 1) = 1] (mod n)"
    and aq: "\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a^ ((n - 1) div p) - 1) n"
  shows "prime n"
  unfolding prime_prime_factor_sqrt[of n]
proof -
  let ?ths = "n \<noteq> 0 \<and> n \<noteq> 1 \<and> (\<nexists>p. prime p \<and> p dvd n \<and> p\<^sup>2 \<le> n)"
  from n have n01: "n \<noteq> 0" "n \<noteq> 1" by arith+
  {
    fix p
    assume p: "prime p" "p dvd n" "p\<^sup>2 \<le> n"
    from p(3) sqr have "p^(Suc 1) \<le> q^(Suc 1)"
      by (simp add: power2_eq_square)
    then have pq: "p \<le> q"
      by (metis le0 power_le_imp_le_base)
    from pocklington_lemma[OF n nqr an aq p(1,2)] have *: "q dvd p - 1"
      by (metis cong_to_1_nat)
    have "p - 1 \<noteq> 0"
      using prime_ge_2_nat [OF p(1)] by arith
    with pq * have False
      by (simp add: nat_dvd_not_less)
  }
  with n01 show ?ths by blast
qed

text \<open>Variant for application, to separate the exponentiation.\<close>
lemma pocklington_alt:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q * r" and sqr: "n \<le> q\<^sup>2"
    and an: "[a^ (n - 1) = 1] (mod n)"
    and aq: "\<forall>p. prime p \<and> p dvd q \<longrightarrow> (\<exists>b. [a^((n - 1) div p) = b] (mod n) \<and> coprime (b - 1) n)"
  shows "prime n"
proof -
  {
    fix p
    assume p: "prime p" "p dvd q"
    from aq[rule_format] p obtain b where b: "[a^((n - 1) div p) = b] (mod n)" "coprime (b - 1) n"
      by blast
    have a0: "a \<noteq> 0"
    proof
      assume a0: "a = 0"
      from n an have "[0 = 1] (mod n)"
        unfolding a0 power_0_left by auto
      then show False
        using n by (simp add: cong_def dvd_eq_mod_eq_0[symmetric])
    qed
    then have a1: "a \<ge> 1" by arith
    from one_le_power[OF a1] have ath: "1 \<le> a ^ ((n - 1) div p)" .
    have b0: "b \<noteq> 0"
    proof
      assume b0: "b = 0"
      from p(2) nqr have "(n - 1) mod p = 0"
        by (metis mod_0 mod_mod_cancel mod_mult_self1_is_0)
      with div_mult_mod_eq[of "n - 1" p]
      have "(n - 1) div p * p= n - 1" by auto
      then have eq: "(a^((n - 1) div p))^p = a^(n - 1)"
        by (simp only: power_mult[symmetric])
      have "p - 1 \<noteq> 0"
        using prime_ge_2_nat [OF p(1)] by arith
      then have pS: "Suc (p - 1) = p" by arith
      from b have d: "n dvd a^((n - 1) div p)"
        unfolding b0 by auto
      from divides_rexp[OF d, of "p - 1"] pS eq cong_dvd_iff [OF an] n show False
        by simp
    qed
    then have b1: "b \<ge> 1" by arith
    from cong_imp_coprime[OF Cong.cong_diff_nat[OF cong_sym [OF b(1)] cong_refl [of 1] b1]]
      ath b1 b nqr
    have "coprime (a ^ ((n - 1) div p) - 1) n"
      by simp
  }
  then have "\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a ^ ((n - 1) div p) - 1) n "
    by blast
  then show ?thesis by (rule pocklington[OF n nqr sqr an])
qed


subsection \<open>Prime factorizations\<close>

(* FIXME some overlap with material in UniqueFactorization, class unique_factorization *)

definition "primefact ps n \<longleftrightarrow> foldr (*) ps 1 = n \<and> (\<forall>p\<in> set ps. prime p)"

lemma primefact:
  fixes n :: nat
  assumes n: "n \<noteq> 0"
  shows "\<exists>ps. primefact ps n"
proof -
  obtain xs where xs: "mset xs = prime_factorization n"
    using ex_mset [of "prime_factorization n"] by blast
  from assms have "n = prod_mset (prime_factorization n)"
    by (simp add: prod_mset_prime_factorization)
  also have "\<dots> = prod_mset (mset xs)" by (simp add: xs)
  also have "\<dots> = foldr (*) xs 1" by (induct xs) simp_all
  finally have "foldr (*) xs 1 = n" ..
  moreover from xs have "\<forall>p\<in>#mset xs. prime p" by auto
  ultimately have "primefact xs n" by (auto simp: primefact_def)
  then show ?thesis ..
qed

lemma primefact_contains:
  fixes p :: nat
  assumes pf: "primefact ps n"
    and p: "prime p"
    and pn: "p dvd n"
  shows "p \<in> set ps"
  using pf p pn
proof (induct ps arbitrary: p n)
  case Nil
  then show ?case by (auto simp: primefact_def)
next
  case (Cons q qs)
  from Cons.prems[unfolded primefact_def]
  have q: "prime q" "q * foldr (*) qs 1 = n" "\<forall>p \<in>set qs. prime p"
    and p: "prime p" "p dvd q * foldr (*) qs 1"
    by simp_all
  consider "p dvd q" | "p dvd foldr (*) qs 1"
    by (metis p prime_dvd_mult_eq_nat)
  then show ?case
  proof cases
    case 1
    with p(1) q(1) have "p = q"
      unfolding prime_nat_iff by auto
    then show ?thesis by simp
  next
    case prem: 2
    from q(3) have pqs: "primefact qs (foldr (*) qs 1)"
      by (simp add: primefact_def)
    from Cons.hyps[OF pqs p(1) prem] show ?thesis by simp
  qed
qed

lemma primefact_variant: "primefact ps n \<longleftrightarrow> foldr (*) ps 1 = n \<and> list_all prime ps"
  by (auto simp add: primefact_def list_all_iff)

text \<open>Variant of Lucas theorem.\<close>
lemma lucas_primefact:
  assumes n: "n \<ge> 2" and an: "[a^(n - 1) = 1] (mod n)"
    and psn: "foldr (*) ps 1 = n - 1"
    and psp: "list_all (\<lambda>p. prime p \<and> \<not> [a^((n - 1) div p) = 1] (mod n)) ps"
  shows "prime n"
proof -
  {
    fix p
    assume p: "prime p" "p dvd n - 1" "[a ^ ((n - 1) div p) = 1] (mod n)"
    from psn psp have psn1: "primefact ps (n - 1)"
      by (auto simp add: list_all_iff primefact_variant)
    from p(3) primefact_contains[OF psn1 p(1,2)] psp
    have False by (induct ps) auto
  }
  with lucas[OF n an] show ?thesis by blast
qed

text \<open>Variant of Pocklington theorem.\<close>
lemma pocklington_primefact:
  assumes n: "n \<ge> 2" and qrn: "q*r = n - 1" and nq2: "n \<le> q\<^sup>2"
    and arnb: "(a^r) mod n = b" and psq: "foldr (*) ps 1 = q"
    and bqn: "(b^q) mod n = 1"
    and psp: "list_all (\<lambda>p. prime p \<and> coprime ((b^(q div p)) mod n - 1) n) ps"
  shows "prime n"
proof -
  from bqn psp qrn
  have bqn: "a ^ (n - 1) mod n = 1"
    and psp: "list_all (\<lambda>p. prime p \<and> coprime (a^(r *(q div p)) mod n - 1) n) ps"
    unfolding arnb[symmetric] power_mod
    by (simp_all add: power_mult[symmetric] algebra_simps)
  from n have n0: "n > 0" by arith
  from div_mult_mod_eq[of "a^(n - 1)" n]
    mod_less_divisor[OF n0, of "a^(n - 1)"]
  have an1: "[a ^ (n - 1) = 1] (mod n)"
    by (metis bqn cong_def mod_mod_trivial)
  have "coprime (a ^ ((n - 1) div p) - 1) n" if p: "prime p" "p dvd q" for p
  proof -
    from psp psq have pfpsq: "primefact ps q"
      by (auto simp add: primefact_variant list_all_iff)
    from psp primefact_contains[OF pfpsq p]
    have p': "coprime (a ^ (r * (q div p)) mod n - 1) n"
      by (simp add: list_all_iff)
    from p prime_nat_iff have p01: "p \<noteq> 0" "p \<noteq> 1" "p = Suc (p - 1)"
      by auto
    from div_mult1_eq[of r q p] p(2)
    have eq1: "r* (q div p) = (n - 1) div p"
      unfolding qrn[symmetric] dvd_eq_mod_eq_0 by (simp add: mult.commute)
    have ath: "a \<le> b \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> 1 \<le> a \<and> 1 \<le> b" for a b :: nat
      by arith
    {
      assume "a ^ ((n - 1) div p) mod n = 0"
      then obtain s where s: "a ^ ((n - 1) div p) = n * s"
        by blast
      then have eq0: "(a^((n - 1) div p))^p = (n*s)^p" by simp
      from qrn[symmetric] have qn1: "q dvd n - 1"
        by (auto simp: dvd_def)
      from dvd_trans[OF p(2) qn1] have npp: "(n - 1) div p * p = n - 1"
        by simp
      with eq0 have "a ^ (n - 1) = (n * s) ^ p"
        by (simp add: power_mult[symmetric])
      with bqn p01 have "1 = (n * s)^(Suc (p - 1)) mod n"
        by simp
      also have "\<dots> = 0" by (simp add: mult.assoc)
      finally have False by simp
    }
    then have *: "a ^ ((n - 1) div p) mod n \<noteq> 0" by auto
    have "[a ^ ((n - 1) div p) mod n = a ^ ((n - 1) div p)] (mod n)"
      by (simp add: cong_def)
    with ath[OF mod_less_eq_dividend *]
    have "[a ^ ((n - 1) div p) mod n - 1 = a ^ ((n - 1) div p) - 1] (mod n)"
      by (simp add: cong_diff_nat)
    then show ?thesis
      by (metis cong_imp_coprime eq1 p')
  qed
  with pocklington[OF n qrn[symmetric] nq2 an1] show ?thesis
    by blast
qed

end
