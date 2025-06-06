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


subsection \<open>Lucas's theorem\<close>

lemma lucas_coprime_lemma:
  fixes n :: nat
  assumes m: "m \<noteq> 0" and am: "[a^m = 1] (mod n)"
  shows "coprime a n"
proof -
  consider "n = 1" | "n = 0" | "n > 1" by arith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    with am m show ?thesis
      by simp
  next
    case 3
    from m obtain m' where m': "m = Suc m'" by (cases m) blast+
    have "d = 1" if d: "d dvd a" "d dvd n" for d
    proof -
      from am mod_less[OF \<open>n > 1\<close>] have am1: "a^m mod n = 1"
        by (simp add: cong_def)
      from dvd_mult2[OF d(1), of "a^m'"] have dam: "d dvd a^m"
        by (simp add: m')
      from dvd_mod_iff[OF d(2), of "a^m"] dam am1 show ?thesis
        by simp
    qed
    then show ?thesis
      by (auto intro: coprimeI)
  qed
qed

lemma lucas_weak:
  fixes n :: nat
  assumes n: "n \<ge> 2"
    and an: "[a ^ (n - 1) = 1] (mod n)"
    and nm: "\<forall>m. 0 < m \<and> m < n - 1 \<longrightarrow> \<not> [a ^ m = 1] (mod n)"
  shows "prime n"
proof (rule totient_imp_prime)
  show "totient n = n - 1"
  proof (rule ccontr)
    have "[a ^ totient n = 1] (mod n)"
      by (rule euler_theorem, rule lucas_coprime_lemma [of "n - 1"]) (use n an in auto)
    moreover assume "totient n \<noteq> n - 1"
    then have "totient n > 0" "totient n < n - 1"
      using \<open>n \<ge> 2\<close> and totient_less[of n] by simp_all
    ultimately show False
      using nm by auto
  qed
qed (use n in auto)

theorem lucas:
  assumes n2: "n \<ge> 2" and an1: "[a^(n - 1) = 1] (mod n)"
    and pn: "\<forall>p. prime p \<and> p dvd n - 1 \<longrightarrow> [a^((n - 1) div p) \<noteq> 1] (mod n)"
  shows "prime n"
proof-
  from n2 have n01: "n \<noteq> 0" "n \<noteq> 1" "n - 1 \<noteq> 0"
    by arith+
  from mod_less_divisor[of n 1] n01 have onen: "1 mod n = 1"
    by simp
  from lucas_coprime_lemma[OF n01(3) an1] cong_imp_coprime an1
  have an: "coprime a n" "coprime (a ^ (n - 1)) n"
    using \<open>n \<ge> 2\<close> by simp_all
  have False if H0: "\<exists>m. 0 < m \<and> m < n - 1 \<and> [a ^ m = 1] (mod n)" (is "\<exists>m. ?P m")
  proof -
    from H0[unfolded exists_least_iff[of ?P]] obtain m where
      m: "0 < m" "m < n - 1" "[a ^ m = 1] (mod n)" "\<forall>k <m. \<not>?P k"
      by blast
    have False if nm1: "(n - 1) mod m > 0"
    proof -
      from mod_less_divisor[OF m(1)] have th0:"(n - 1) mod m < m" by blast
      let ?y = "a^ ((n - 1) div m * m)"
      note mdeq = div_mult_mod_eq[of "(n - 1)" m]
      have yn: "coprime ?y n"
        using an(1) by (cases "(n - Suc 0) div m * m = 0") auto
      have "?y mod n = (a^m)^((n - 1) div m) mod n"
        by (simp add: algebra_simps power_mult)
      also have "\<dots> = (a^m mod n)^((n - 1) div m) mod n"
        using power_mod[of "a^m" n "(n - 1) div m"] by simp
      also have "\<dots> = 1" using m(3)[unfolded cong_def onen] onen
        by (metis power_one)
      finally have *: "?y mod n = 1"  .
      have **: "[?y * a ^ ((n - 1) mod m) = ?y* 1] (mod n)"
        using an1[unfolded cong_def onen] onen
          div_mult_mod_eq[of "(n - 1)" m, symmetric]
        by (simp add:power_add[symmetric] cong_def * del: One_nat_def)
      have "[a ^ ((n - 1) mod m) = 1] (mod n)"
        by (metis cong_mult_rcancel_nat mult.commute ** yn)
      with m(4)[rule_format, OF th0] nm1
        less_trans[OF mod_less_divisor[OF m(1), of "n - 1"] m(2)] show ?thesis
        by blast
    qed
    then have "(n - 1) mod m = 0" by auto
    then have mn: "m dvd n - 1" by presburger
    then obtain r where r: "n - 1 = m * r"
      unfolding dvd_def by blast
    from n01 r m(2) have r01: "r \<noteq> 0" "r \<noteq> 1" by auto
    obtain p where p: "prime p" "p dvd r"
      by (metis prime_factor_nat r01(2))
    then have th: "prime p \<and> p dvd n - 1"
      unfolding r by (auto intro: dvd_mult)
    from r have "(a ^ ((n - 1) div p)) mod n = (a^(m*r div p)) mod n"
      by (simp add: power_mult)
    also have "\<dots> = (a^(m*(r div p))) mod n"
      using div_mult1_eq[of m r p] p(2)[unfolded dvd_eq_mod_eq_0] by simp
    also have "\<dots> = ((a^m)^(r div p)) mod n"
      by (simp add: power_mult)
    also have "\<dots> = ((a^m mod n)^(r div p)) mod n"
      using power_mod ..
    also from m(3) onen have "\<dots> = 1"
      by (simp add: cong_def)
    finally have "[(a ^ ((n - 1) div p))= 1] (mod n)"
      using onen by (simp add: cong_def)
    with pn th show ?thesis by blast
  qed
  then have "\<forall>m. 0 < m \<and> m < n - 1 \<longrightarrow> \<not> [a ^ m = 1] (mod n)"
    by blast
  then show ?thesis by (rule lucas_weak[OF n2 an1])
qed


subsection \<open>Definition of the order of a number mod \<open>n\<close>\<close>

definition "ord n a = (if coprime n a then Least (\<lambda>d. d > 0 \<and> [a ^d = 1] (mod n)) else 0)"

text \<open>This has the expected properties.\<close>

lemma coprime_ord:
  fixes n::nat
  assumes "coprime n a"
  shows "ord n a > 0 \<and> [a ^(ord n a) = 1] (mod n) \<and> (\<forall>m. 0 < m \<and> m < ord n a \<longrightarrow> [a^ m \<noteq> 1] (mod n))"
proof-
  let ?P = "\<lambda>d. 0 < d \<and> [a ^ d = 1] (mod n)"
  from bigger_prime[of a] obtain p where p: "prime p" "a < p"
    by blast
  from assms have o: "ord n a = Least ?P"
    by (simp add: ord_def)
  have ex: "\<exists>m>0. ?P m"
  proof (cases "n \<ge> 2")
    case True
    moreover from assms have "coprime a n"
      by (simp add: ac_simps)
    then have "[a ^ totient n = 1] (mod n)"
      by (rule euler_theorem)
    ultimately show ?thesis
      by (auto intro: exI [where x = "totient n"])
  next
    case False
    then have "n = 0 \<or> n = 1"
      by auto
    with assms show ?thesis
      by auto
  qed
  from exists_least_iff'[of ?P] ex assms show ?thesis
    unfolding o[symmetric] by auto
qed

text \<open>With the special value \<open>0\<close> for non-coprime case, it's more convenient.\<close>
lemma ord_works: "[a ^ (ord n a) = 1] (mod n) \<and> (\<forall>m. 0 < m \<and> m < ord n a \<longrightarrow> \<not> [a^ m = 1] (mod n))"
  for n :: nat
  by (cases "coprime n a") (use coprime_ord[of n a] in \<open>auto simp add: ord_def cong_def\<close>)

lemma ord: "[a^(ord n a) = 1] (mod n)"
  for n :: nat
  using ord_works by blast

lemma ord_minimal: "0 < m \<Longrightarrow> m < ord n a \<Longrightarrow> \<not> [a^m = 1] (mod n)"
  for n :: nat
  using ord_works by blast

lemma ord_eq_0: "ord n a = 0 \<longleftrightarrow> \<not> coprime n a"
  for n :: nat
  by (cases "coprime n a") (simp add: coprime_ord, simp add: ord_def)

lemma divides_rexp: "x dvd y \<Longrightarrow> x dvd (y ^ Suc n)"
  for x y :: nat
  by (simp add: dvd_mult2[of x y])

lemma ord_divides:"[a ^ d = 1] (mod n) \<longleftrightarrow> ord n a dvd d"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for n :: nat
proof
  assume ?rhs
  then obtain k where "d = ord n a * k"
    unfolding dvd_def by blast
  then have "[a ^ d = (a ^ (ord n a) mod n)^k] (mod n)"
    by (simp add : cong_def power_mult power_mod)
  also have "[(a ^ (ord n a) mod n)^k = 1] (mod n)"
    using ord[of a n, unfolded cong_def]
    by (simp add: cong_def power_mod)
  finally show ?lhs .
next
  assume ?lhs
  show ?rhs
  proof (cases "coprime n a")
    case prem: False
    then have o: "ord n a = 0" by (simp add: ord_def)
    show ?thesis
    proof (cases d)
      case 0
      with o prem show ?thesis by (simp add: cong_def)
    next
      case (Suc d')
      then have d0: "d \<noteq> 0" by simp
      from prem obtain p where p: "p dvd n" "p dvd a" "p \<noteq> 1"
        by (auto elim: not_coprimeE) 
      from \<open>?lhs\<close> obtain q1 q2 where q12: "a ^ d + n * q1 = 1 + n * q2"
        using prem d0 lucas_coprime_lemma
        by (auto elim: not_coprimeE simp add: ac_simps)
      then have "a ^ d + n * q1 - n * q2 = 1" by simp
      with dvd_diff_nat [OF dvd_add [OF divides_rexp]]  dvd_mult2 Suc p have "p dvd 1"
        by metis
      with p(3) have False by simp
      then show ?thesis ..
    qed
  next
    case H: True
    let ?o = "ord n a"
    let ?q = "d div ord n a"
    let ?r = "d mod ord n a"
    have eqo: "[(a^?o)^?q = 1] (mod n)"
      using cong_pow ord_works by fastforce
    from H have onz: "?o \<noteq> 0" by (simp add: ord_eq_0)
    then have opos: "?o > 0" by simp
    from div_mult_mod_eq[of d "ord n a"] \<open>?lhs\<close>
    have "[a^(?o*?q + ?r) = 1] (mod n)"
      by (simp add: cong_def mult.commute)
    then have "[(a^?o)^?q * (a^?r) = 1] (mod n)"
      by (simp add: cong_def power_mult[symmetric] power_add[symmetric])
    then have th: "[a^?r = 1] (mod n)"
      using eqo mod_mult_left_eq[of "(a^?o)^?q" "a^?r" n]
      by (simp add: cong_def del: One_nat_def) (metis mod_mult_left_eq nat_mult_1)
    show ?thesis
    proof (cases "?r = 0")
      case True
      then show ?thesis by (simp add: dvd_eq_mod_eq_0)
    next
      case False
      with mod_less_divisor[OF opos, of d] have r0o:"?r >0 \<and> ?r < ?o" by simp
      from conjunct2[OF ord_works[of a n], rule_format, OF r0o] th
      show ?thesis by blast
    qed
  qed
qed

lemma order_divides_totient:
  "ord n a dvd totient n" if "coprime n a"
  using that euler_theorem [of a n]
  by (simp add: ord_divides [symmetric] ac_simps)

lemma order_divides_expdiff:
  fixes n::nat and a::nat assumes na: "coprime n a"
  shows "[a^d = a^e] (mod n) \<longleftrightarrow> [d = e] (mod (ord n a))"
proof -
  have th: "[a^d = a^e] (mod n) \<longleftrightarrow> [d = e] (mod (ord n a))"
    if na: "coprime n a" and ed: "(e::nat) \<le> d"
    for n a d e :: nat
  proof -
    from na ed have "\<exists>c. d = e + c" by presburger
    then obtain c where c: "d = e + c" ..
    from na have an: "coprime a n"
      by (simp add: ac_simps)
    then have aen: "coprime (a ^ e) n"
      by (cases "e > 0") simp_all
    from an have acn: "coprime (a ^ c) n"
      by (cases "c > 0") simp_all
    from c have "[a^d = a^e] (mod n) \<longleftrightarrow> [a^(e + c) = a^(e + 0)] (mod n)"
      by simp
    also have "\<dots> \<longleftrightarrow> [a^e* a^c = a^e *a^0] (mod n)" by (simp add: power_add)
    also have  "\<dots> \<longleftrightarrow> [a ^ c = 1] (mod n)"
      using cong_mult_lcancel_nat [OF aen, of "a^c" "a^0"] by simp
    also have "\<dots> \<longleftrightarrow> ord n a dvd c"
      by (simp only: ord_divides)
    also have "\<dots> \<longleftrightarrow> [e + c = e + 0] (mod ord n a)"
      by (auto simp add: cong_altdef_nat)
    finally show ?thesis
      using c by simp
  qed
  consider "e \<le> d" | "d \<le> e" by arith
  then show ?thesis
  proof cases
    case 1
    with na show ?thesis by (rule th)
  next
    case 2
    from th[OF na this] show ?thesis
      by (metis cong_sym)
  qed
qed

lemma ord_not_coprime [simp]: "\<not>coprime n a \<Longrightarrow> ord n a = 0"
  by (simp add: ord_def)

lemma ord_1 [simp]: "ord 1 n = 1"
proof -
  have "(LEAST k. k > 0) = (1 :: nat)"
    by (rule Least_equality) auto
  thus ?thesis by (simp add: ord_def)
qed

lemma ord_1_right [simp]: "ord (n::nat) 1 = 1"
  using ord_divides[of 1 1 n] by simp

lemma ord_Suc_0_right [simp]: "ord (n::nat) (Suc 0) = 1"
  using ord_divides[of 1 1 n] by simp

lemma ord_0_nat [simp]: "ord 0 (n :: nat) = (if n = 1 then 1 else 0)"
proof -
  have "(LEAST k. k > 0) = (1 :: nat)"
    by (rule Least_equality) auto
  thus ?thesis by (auto simp: ord_def)
qed

lemma ord_0_right_nat [simp]: "ord (n :: nat) 0 = (if n = 1 then 1 else 0)"
proof -
  have "(LEAST k. k > 0) = (1 :: nat)"
    by (rule Least_equality) auto
  thus ?thesis by (auto simp: ord_def)
qed

lemma ord_divides': "[a ^ d = Suc 0] (mod n) = (ord n a dvd d)"
  using ord_divides[of a d n] by simp

lemma ord_Suc_0 [simp]: "ord (Suc 0) n = 1"
  using ord_1[where 'a = nat] by (simp del: ord_1)

lemma ord_mod [simp]: "ord n (k mod n) = ord n k"
  by (cases "n = 0") (auto simp add: ord_def cong_def power_mod)

lemma ord_gt_0_iff [simp]: "ord (n::nat) x > 0 \<longleftrightarrow> coprime n x"
  using ord_eq_0[of n x] by auto

lemma ord_eq_Suc_0_iff: "ord n (x::nat) = Suc 0 \<longleftrightarrow> [x = 1] (mod n)"
  using ord_divides[of x 1 n] by (auto simp: ord_divides')

lemma ord_cong:
  assumes "[k1 = k2] (mod n)"
  shows   "ord n k1 = ord n k2"
proof -
  have "ord n (k1 mod n) = ord n (k2 mod n)"
    by (simp only: assms[unfolded cong_def])
  thus ?thesis by simp
qed

lemma ord_nat_code [code_unfold]:
  "ord n a =
     (if n = 0 then if a = 1 then 1 else 0 else
        if coprime n a then Min (Set.filter (\<lambda>k. [a ^ k = 1] (mod n)) {0<..n}) else 0)"
proof (cases "coprime n a \<and> n > 0")
  case True
  define A where "A = {k\<in>{0<..n}. [a ^ k = 1] (mod n)}"
  define k where "k = (LEAST k. k > 0 \<and> [a ^ k = 1] (mod n))"
  have totient: "totient n \<in> A"
    using euler_theorem[of a n] True
    by (auto simp: A_def coprime_commute intro!: Nat.gr0I totient_le)
  moreover have "finite A" by (auto simp: A_def)
  ultimately have *: "Min A \<in> A" and "\<forall>y. y \<in> A \<longrightarrow> Min A \<le> y"
    by (auto intro: Min_in)

  have "k > 0 \<and> [a ^ k = 1] (mod n)"
    unfolding k_def by (rule LeastI[of _ "totient n"]) (use totient in \<open>auto simp: A_def\<close>)
  moreover have "k \<le> totient n"
    unfolding k_def by (intro Least_le) (use totient in \<open>auto simp: A_def\<close>)
  ultimately have "k \<in> A" using totient_le[of n] by (auto simp: A_def)
  hence "Min A \<le> k" by (intro Min_le) (auto simp: \<open>finite A\<close>)
  moreover from * have "k \<le> Min A"
    unfolding k_def by (intro Least_le) (auto simp: A_def)
  ultimately show ?thesis using True
    by (simp add: ord_def k_def A_def)
qed auto

theorem ord_modulus_mult_coprime:
  fixes x :: nat
  assumes "coprime m n"
  shows   "ord (m * n) x = lcm (ord m x) (ord n x)"
proof (intro dvd_antisym)
  have "[x ^ lcm (ord m x) (ord n x) = 1] (mod (m * n))"
    using assms by (intro coprime_cong_mult_nat assms) (auto simp: ord_divides')
  thus "ord (m * n) x dvd lcm (ord m x) (ord n x)"
    by (simp add: ord_divides')
next
  show "lcm (ord m x) (ord n x) dvd ord (m * n) x"
  proof (intro lcm_least)
    show "ord m x dvd ord (m * n) x"
      using cong_modulus_mult_nat[of "x ^ ord (m * n) x" 1 m n] assms
      by (simp add: ord_divides')
    show "ord n x dvd ord (m * n) x"
      using cong_modulus_mult_nat[of "x ^ ord (m * n) x" 1 n m] assms
      by (simp add: ord_divides' mult.commute)
  qed
qed

corollary ord_modulus_prod_coprime:
  assumes "finite A" "\<And>i j. i \<in> A \<Longrightarrow> j \<in> A \<Longrightarrow> i \<noteq> j \<Longrightarrow> coprime (f i) (f j)"
  shows   "ord (\<Prod>i\<in>A. f i :: nat) x = (LCM i\<in>A. ord (f i) x)"
  using assms by (induction A rule: finite_induct)
                 (simp, simp, subst ord_modulus_mult_coprime, auto intro!: prod_coprime_right)

lemma ord_power_aux:
  fixes m x k a :: nat
  defines "l \<equiv> ord m a"
  shows   "ord m (a ^ k) * gcd k l = l"
proof (rule dvd_antisym)
  have "[a ^ lcm k l = 1] (mod m)"
    unfolding ord_divides by (simp add: l_def)
  also have "lcm k l = k * (l div gcd k l)"
    by (simp add: lcm_nat_def div_mult_swap)
  finally have "ord m (a ^ k) dvd l div gcd k l"
    unfolding ord_divides [symmetric] by (simp add: power_mult [symmetric])
  thus "ord m (a ^ k) * gcd k l dvd l"
    by (cases "l = 0") (auto simp: dvd_div_iff_mult)

  have "[(a ^ k) ^ ord m (a ^ k) = 1] (mod m)"
    by (rule ord)
  also have "(a ^ k) ^ ord m (a ^ k) = a ^ (k * ord m (a ^ k))"
    by (simp add: power_mult)
  finally have "ord m a dvd k * ord m (a ^ k)"
    by (simp add: ord_divides')
  hence "l dvd gcd (k * ord m (a ^ k)) (l * ord m (a ^ k))"
    by (intro gcd_greatest dvd_triv_left) (auto simp: l_def ord_divides')
  also have "gcd (k * ord m (a ^ k)) (l * ord m (a ^ k)) = ord m (a ^ k) * gcd k l"
    by (subst gcd_mult_distrib_nat) (auto simp: mult_ac)
  finally show "l dvd ord m (a ^ k) * gcd k l" .
qed

theorem ord_power: "coprime m a \<Longrightarrow> ord m (a ^ k :: nat) = ord m a div gcd k (ord m a)"
  using ord_power_aux[of m a k] by (metis div_mult_self_is_m gcd_pos_nat ord_eq_0)

lemma inj_power_mod:
  assumes "coprime n (a :: nat)"
  shows   "inj_on (\<lambda>k. a ^ k mod n) {..<ord n a}"
proof
  fix k l assume *: "k \<in> {..<ord n a}" "l \<in> {..<ord n a}" "a ^ k mod n = a ^ l mod n"
  have "k = l" if "k < l" "l < ord n a" "[a ^ k = a ^ l] (mod n)" for k l
  proof -
    have "l = k + (l - k)" using that by simp
    also have "a ^ \<dots> = a ^ k * a ^ (l - k)"
      by (simp add: power_add)
    also have "[\<dots> = a ^ l * a ^ (l - k)] (mod n)"
      using that by (intro cong_mult) auto
    finally have "[a ^ l * a ^ (l - k) = a ^ l * 1] (mod n)"
      by (simp add: cong_sym_eq)
    with assms have "[a ^ (l - k) = 1] (mod n)"
      by (subst (asm) cong_mult_lcancel_nat) (auto simp: coprime_commute)
    hence "ord n a dvd l - k"
      by (simp add: ord_divides')
    from dvd_imp_le[OF this] and \<open>l < ord n a\<close> have "l - k = 0"
      by (cases "l - k = 0") auto
    with \<open>k < l\<close> show "k = l" by simp
  qed
  from this[of k l] and this[of l k] and * show "k = l"
    by (cases k l rule: linorder_cases) (auto simp: cong_def)
qed

lemma ord_eq_2_iff: "ord n (x :: nat) = 2 \<longleftrightarrow> [x \<noteq> 1] (mod n) \<and> [x\<^sup>2 = 1] (mod n)"
proof
  assume x: "[x \<noteq> 1] (mod n) \<and> [x\<^sup>2 = 1] (mod n)"
  hence "coprime n x"
    by (metis coprime_commute lucas_coprime_lemma zero_neq_numeral)
  with x have "ord n x dvd 2" "ord n x \<noteq> 1" "ord n x > 0"
    by (auto simp: ord_divides' ord_eq_Suc_0_iff)
  thus "ord n x = 2" by (auto dest!: dvd_imp_le simp del: ord_gt_0_iff)
qed (use ord_divides[of _ 2] ord_divides[of _ 1] in auto)

lemma square_mod_8_eq_1_iff: "[x\<^sup>2 = 1] (mod 8) \<longleftrightarrow> odd (x :: nat)"
proof -
  have "[x\<^sup>2 = 1] (mod 8) \<longleftrightarrow> ((x mod 8)\<^sup>2 mod 8 = 1)"
    by (simp add: power_mod cong_def)
  also have "\<dots> \<longleftrightarrow> x mod 8 \<in> {1, 3, 5, 7}"
  proof
    assume x: "(x mod 8)\<^sup>2 mod 8 = 1"
    have "x mod 8 \<in> {..<8}" by simp
    also have "{..<8} = {0, 1, 2, 3, 4, 5, 6, 7::nat}"
      by (simp add: lessThan_nat_numeral lessThan_Suc insert_commute)
    finally have x_cases: "x mod 8 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" .
    from x have "x mod 8 \<notin> {0, 2, 4, 6}"
      using x by (auto intro: Nat.gr0I)
    with x_cases show "x mod 8 \<in> {1, 3, 5, 7}" by simp
  qed auto
  also have "\<dots> \<longleftrightarrow> odd (x mod 8)"
    by (auto elim!: oddE)
  also have "\<dots> \<longleftrightarrow> odd x"
    by presburger
  finally show ?thesis .
qed

lemma ord_twopow_aux:
  assumes "k \<ge> 3" and "odd (x :: nat)"
  shows   "[x ^ (2 ^ (k - 2)) = 1] (mod (2 ^ k))"
  using assms(1)
proof (induction k rule: dec_induct)
  case base
  from assms have "[x\<^sup>2 = 1] (mod 8)"
    by (subst square_mod_8_eq_1_iff) auto
  thus ?case by simp
next
  case (step k)
  define k' where "k' = k - 2"
  have k: "k = Suc (Suc k')"
    using \<open>k \<ge> 3\<close> by (simp add: k'_def)
  from \<open>k \<ge> 3\<close> have "2 * k \<ge> Suc k" by presburger

  from \<open>odd x\<close> have "x > 0" by (intro Nat.gr0I) auto
  from step.IH have "2 ^ k dvd (x ^ (2 ^ (k - 2)) - 1)"
    by (rule cong_to_1_nat)
  then obtain t where "x ^ (2 ^ (k - 2)) - 1 = t * 2 ^ k"
    by auto
  hence "x ^ (2 ^ (k - 2)) = t * 2 ^ k + 1"
    by (metis \<open>0 < x\<close> add.commute add_diff_inverse_nat less_one neq0_conv power_eq_0_iff)
  hence "(x ^ (2 ^ (k - 2))) ^ 2 = (t * 2 ^ k + 1) ^ 2"
    by (rule arg_cong)
  hence "[(x ^ (2 ^ (k - 2))) ^ 2 = (t * 2 ^ k + 1) ^ 2] (mod (2 ^ Suc k))"
    by simp
  also have "(x ^ (2 ^ (k - 2))) ^ 2 = x ^ (2 ^ (k - 1))"
    by (simp_all add: power_even_eq[symmetric] power_mult k )
  also have "(t * 2 ^ k + 1) ^ 2 = t\<^sup>2 * 2 ^ (2 * k) + t * 2 ^ Suc k + 1"
    by (subst power2_eq_square)
       (auto simp: algebra_simps k power2_eq_square[of t]
                   power_even_eq[symmetric] power_add [symmetric])
  also have "[\<dots> = 0 + 0 + 1] (mod 2 ^ Suc k)"
    using \<open>2 * k \<ge> Suc k\<close>
    by (intro cong_add)
       (auto simp: cong_0_iff intro: dvd_mult[OF le_imp_power_dvd] simp del: power_Suc)
  finally show ?case by simp
qed

lemma ord_twopow_3_5:
  assumes "k \<ge> 3" "x mod 8 \<in> {3, 5 :: nat}"
  shows   "ord (2 ^ k) x = 2 ^ (k - 2)"
  using assms(1)
proof (induction k rule: less_induct)
  have "x mod 8 = 3 \<or> x mod 8 = 5" using assms by auto
  hence "odd x" by presburger
  case (less k)
  from \<open>k \<ge> 3\<close> consider "k = 3" | "k = 4" | "k \<ge> 5" by force
  thus ?case
  proof cases
    case 1
    thus ?thesis using assms
      by (auto simp: ord_eq_2_iff cong_def simp flip: power_mod[of x])
  next
    case 2
    from assms have "x mod 8 = 3 \<or> x mod 8 = 5" by auto
    then have x': "x mod 16 = 3 \<or> x mod 16 = 5 \<or> x mod 16 = 11 \<or> x mod 16 = 13"
      using mod_double_nat [of x 8] by auto
    hence "[x ^ 4 = 1] (mod 16)" using assms
      by (auto simp: cong_def simp flip: power_mod[of x])
    hence "ord 16 x dvd 2\<^sup>2" by (simp add: ord_divides')
    then obtain l where l: "ord 16 x = 2 ^ l" "l \<le> 2"
      by (subst (asm) divides_primepow_nat) auto

    have "[x ^ 2 \<noteq> 1] (mod 16)"
      using x' by (auto simp: cong_def simp flip: power_mod[of x])
    hence "\<not>ord 16 x dvd 2" by (simp add: ord_divides')
    with l have "l = 2"
      using le_imp_power_dvd[of l 1 2] by (cases "l \<le> 1") auto
    with l show ?thesis by (simp add: \<open>k = 4\<close>)
  next
    case 3
    define k' where "k' = k - 2"
    have k': "k' \<ge> 2" and [simp]: "k = Suc (Suc k')"
      using 3 by (simp_all add: k'_def)
    have IH: "ord (2 ^ k') x = 2 ^ (k' - 2)" "ord (2 ^ Suc k') x = 2 ^ (k' - 1)"
      using less.IH[of k'] less.IH[of "Suc k'"] 3 by simp_all
    from IH have cong: "[x ^ (2 ^ (k' - 2)) = 1] (mod (2 ^ k'))"
      by (simp_all add: ord_divides')
    have notcong: "[x ^ (2 ^ (k' - 2)) \<noteq> 1] (mod (2 ^ Suc k'))"
    proof
      assume "[x ^ (2 ^ (k' - 2)) = 1] (mod (2 ^ Suc k'))"
      hence "ord (2 ^ Suc k') x dvd 2 ^ (k' - 2)"
        by (simp add: ord_divides')
      also have "ord (2 ^ Suc k') x = 2 ^ (k' - 1)"
        using IH by simp
      finally have "k' - 1 \<le> k' - 2"
        by (rule power_dvd_imp_le) auto
      with \<open>k' \<ge> 2\<close> show False by simp
    qed

    have "2 ^ k' + 1 < 2 ^ k' + (2 ^ k' :: nat)"
      using one_less_power[of "2::nat" k'] k' by (intro add_strict_left_mono) auto
    with cong notcong have cong': "x ^ (2 ^ (k' - 2)) mod 2 ^ Suc k' = 1 + 2 ^ k'"
      using mod_double_nat [of \<open>x ^ 2 ^ (k' - 2)\<close> \<open>2 ^ k'\<close>] k' by (auto simp: cong_def)

    hence "x ^ (2 ^ (k' - 2)) mod 2 ^ k = 1 + 2 ^ k' \<or>
           x ^ (2 ^ (k' - 2)) mod 2 ^ k = 1 + 2 ^ k' + 2 ^ Suc k'"
      using mod_double_nat [of \<open>x ^ 2 ^ (k' - 2)\<close> \<open>2 ^ Suc k'\<close>] by auto
    hence eq: "[x ^ 2 ^ (k' - 1) = 1 + 2 ^ (k - 1)] (mod 2 ^ k)"
    proof
      assume *: "x ^ (2 ^ (k' - 2)) mod (2 ^ k) = 1 + 2 ^ k'"
      have "[x ^ (2 ^ (k' - 2)) = x ^ (2 ^ (k' - 2)) mod 2 ^ k] (mod 2 ^ k)"
        by simp
      also have "[x ^ (2 ^ (k' - 2)) mod (2 ^ k) = 1 + 2 ^ k'] (mod 2 ^ k)"
        by (subst *) auto
      finally have "[(x ^ 2 ^ (k' - 2)) ^ 2 = (1 + 2 ^ k') ^ 2] (mod 2 ^ k)"
        by (rule cong_pow)
      hence "[x ^ 2 ^ Suc (k' - 2) = (1 + 2 ^ k') ^ 2] (mod 2 ^ k)"
        by (simp add: power_mult [symmetric] power_Suc2 [symmetric] del: power_Suc)
      also have "Suc (k' - 2) = k' - 1"
        using k' by simp
      also have "(1 + 2 ^ k' :: nat)\<^sup>2 = 1 + 2 ^ (k - 1) + 2 ^ (2 * k')"
        by (subst power2_eq_square) (simp add: algebra_simps flip: power_add)
      also have "(2 ^ k :: nat) dvd 2 ^ (2 * k')"
        using k' by (intro le_imp_power_dvd) auto
      hence "[1 + 2 ^ (k - 1) + 2 ^ (2 * k') = 1 + 2 ^ (k - 1) + (0 :: nat)] (mod 2 ^ k)"
        by (intro cong_add) (auto simp: cong_0_iff)
      finally show "[x ^ 2 ^ (k' - 1) = 1 + 2 ^ (k - 1)] (mod 2 ^ k)"
        by simp
    next
      assume *: "x ^ (2 ^ (k' - 2)) mod 2 ^ k = 1 + 2 ^ k' + 2 ^ Suc k'"
      have "[x ^ (2 ^ (k' - 2)) = x ^ (2 ^ (k' - 2)) mod 2 ^ k] (mod 2 ^ k)"
        by simp
      also have "[x ^ (2 ^ (k' - 2)) mod (2 ^ k) = 1 + 3 * 2 ^ k'] (mod 2 ^ k)"
        by (subst *) auto
      finally have "[(x ^ 2 ^ (k' - 2)) ^ 2 = (1 + 3 * 2 ^ k') ^ 2] (mod 2 ^ k)"
        by (rule cong_pow)
      hence "[x ^ 2 ^ Suc (k' - 2) = (1 + 3 * 2 ^ k') ^ 2] (mod 2 ^ k)"
        by (simp add: power_mult [symmetric] power_Suc2 [symmetric] del: power_Suc)
      also have "Suc (k' - 2) = k' - 1"
        using k' by simp
      also have "(1 + 3 * 2 ^ k' :: nat)\<^sup>2 = 1 + 2 ^ (k - 1) + 2 ^ k + 9 * 2 ^ (2 * k')"
        by (subst power2_eq_square) (simp add: algebra_simps flip: power_add)
      also have "(2 ^ k :: nat) dvd 9 * 2 ^ (2 * k')"
        using k' by (intro dvd_mult le_imp_power_dvd) auto
      hence "[1 + 2 ^ (k - 1) + 2 ^ k + 9 * 2 ^ (2 * k') = 1 + 2 ^ (k - 1) + 0 + (0 :: nat)]
               (mod 2 ^ k)"
        by (intro cong_add) (auto simp: cong_0_iff)
      finally show "[x ^ 2 ^ (k' - 1) = 1 + 2 ^ (k - 1)] (mod 2 ^ k)"
        by simp
    qed

    have notcong': "[x ^ 2 ^ (k - 3) \<noteq> 1] (mod 2 ^ k)"
    proof
      assume "[x ^ 2 ^ (k - 3) = 1] (mod 2 ^ k)"
      hence "[x ^ 2 ^ (k' - 1) - x ^ 2 ^ (k' - 1) = 1 + 2 ^ (k - 1) - 1] (mod 2 ^ k)"
        by (intro cong_diff_nat eq) auto
      hence "[2 ^ (k - 1) = (0 :: nat)] (mod 2 ^ k)"
        by (simp add: cong_sym_eq)
      hence "2 ^ k dvd 2 ^ (k - 1)"
        by (simp add: cong_0_iff)
      hence "k \<le> k - 1"
        by (rule power_dvd_imp_le) auto
      thus False by simp
    qed

    have "[x ^ 2 ^ (k - 2) = 1] (mod 2 ^ k)"
      using ord_twopow_aux[of k x] \<open>odd x\<close> \<open>k \<ge> 3\<close> by simp
    hence "ord (2 ^ k) x dvd 2 ^ (k - 2)"
      by (simp add: ord_divides')
    then obtain l where l: "l \<le> k - 2" "ord (2 ^ k) x = 2 ^ l"
      using divides_primepow_nat[of 2 "ord (2 ^ k) x" "k - 2"] by auto

    from notcong' have "\<not>ord (2 ^ k) x dvd 2 ^ (k - 3)"
      by (simp add: ord_divides')
    with l have "l = k - 2"
      using le_imp_power_dvd[of l "k - 3" 2] by (cases "l \<le> k - 3") auto
    with l show ?thesis by simp
  qed
qed

lemma ord_4_3 [simp]: "ord 4 (3::nat) = 2"
proof -
  have "[3 ^ 2 = (1 :: nat)] (mod 4)"
    by (simp add: cong_def)
  hence "ord 4 (3::nat) dvd 2"
    by (subst (asm) ord_divides) auto
  hence "ord 4 (3::nat) \<le> 2"
    by (intro dvd_imp_le) auto
  moreover have "ord 4 (3::nat) \<noteq> 1"
    by (auto simp: ord_eq_Suc_0_iff cong_def)
  moreover have "ord 4 (3::nat) \<noteq> 0"
    by (auto simp: gcd_non_0_nat coprime_iff_gcd_eq_1)
  ultimately show "ord 4 (3 :: nat) = 2"
    by linarith
qed

lemma elements_with_ord_1: "n > 0 \<Longrightarrow> {x\<in>totatives n. ord n x = Suc 0} = {1}"
  by (auto simp: ord_eq_Suc_0_iff cong_def totatives_less)

lemma residue_prime_has_primroot:
  fixes p :: nat
  assumes "prime p"
  shows "\<exists>a\<in>totatives p. ord p a = p - 1"
proof -
  from residue_prime_mult_group_has_gen[OF assms]
    obtain a where a: "a \<in> {1..p-1}" "{1..p-1} = {a ^ i mod p |i. i \<in> UNIV}" by blast
  from a have "coprime p a"
    using a assms by (intro prime_imp_coprime) (auto dest: dvd_imp_le)
  with a(1) have "a \<in> totatives p" by (auto simp: totatives_def coprime_commute)

  have "p - 1 = card {1..p-1}" by simp
  also have "{1..p-1} = {a ^ i mod p |i. i \<in> UNIV}" by fact
  also have "{a ^ i mod p |i. i \<in> UNIV} = (\<lambda>i. a ^ i mod p) ` {..<ord p a}"
  proof (intro equalityI subsetI)
    fix x assume "x \<in> {a ^ i mod p |i. i \<in> UNIV}"
    then obtain i where [simp]: "x = a ^ i mod p" by auto

    have "[a ^ i = a ^ (i mod ord p a)] (mod p)"
      using \<open>coprime p a\<close> by (subst order_divides_expdiff) auto
    hence "\<exists>j. a ^ i mod p = a ^ j mod p \<and> j < ord p a"
      using \<open>coprime p a\<close> by (intro exI[of _ "i mod ord p a"]) (auto simp: cong_def)
    thus "x \<in> (\<lambda>i. a ^ i mod p) ` {..<ord p a}"
      by auto
  qed auto
  also have "card \<dots> = ord p a"
    using inj_power_mod[OF \<open>coprime p a\<close>] by (subst card_image) auto
  finally show ?thesis using \<open>a \<in> totatives p\<close>
    by auto
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
