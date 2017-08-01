(*  Title:      HOL/Number_Theory/Pocklington.thy
    Author:     Amine Chaieb
*)

section \<open>Pocklington's Theorem for Primes\<close>

theory Pocklington
imports Residues
begin

subsection \<open>Lemmas about previously defined terms\<close>

lemma prime_nat_iff'': "prime (p::nat) \<longleftrightarrow> p \<noteq> 0 \<and> p \<noteq> 1 \<and> (\<forall>m. 0 < m \<and> m < p \<longrightarrow> coprime p m)"
  unfolding prime_nat_iff
proof safe
  fix m
  assume p: "p > 0" "p \<noteq> 1"
    and m: "m dvd p" "m \<noteq> p"
    and *: "\<forall>m. m > 0 \<and> m < p \<longrightarrow> coprime p m"
  from p m have "m \<noteq> 0" by (intro notI) auto
  moreover from p m have "m < p" by (auto dest: dvd_imp_le)
  ultimately have "coprime p m"
    using * by blast
  with m show "m = 1" by simp
qed (auto simp: prime_nat_iff simp del: One_nat_def intro!: prime_imp_coprime dest: dvd_imp_le)

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
    by (simp add: cong_nat_def)
next
  case False
  from bezout_add_strong_nat [OF this]
  obtain d x y where dxy: "d dvd a" "d dvd n" "a * x = n * y + d" by blast
  from dxy(1,2) have d1: "d = 1"
    by (metis assms coprime_nat)
  with dxy(3) have "a * x * b = (n * y + 1) * b"
    by simp
  then have "a * (x * b) = n * (y * b) + b"
    by (auto simp: algebra_simps)
  then have "a * (x * b) mod n = (n * (y * b) + b) mod n"
    by simp
  then have "a * (x * b) mod n = b mod n"
    by (simp add: mod_add_left_eq)
  then have "[a * (x * b) = b] (mod n)"
    by (simp only: cong_nat_def)
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
    by (simp add: cong_nat_def mod_mult_right_eq[of a x n])
  from mod_less_divisor[ of n x] nz * have Px: "?P ?x" by simp
  have "y = ?x" if Py: "y < n" "[a * y = b] (mod n)" for y
  proof -
    from Py(2) * have "[a * y = a * ?x] (mod n)"
      by (simp add: cong_nat_def)
    then have "[y = ?x] (mod n)"
      by (metis an cong_mult_lcancel_nat)
    with mod_less[OF Py(1)] mod_less_divisor[ of n x] nz
    show ?thesis
      by (simp add: cong_nat_def)
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
    by (metis gcd.commute)
  have px: "coprime x p"
    by (metis gcd.commute p prime_nat_iff'' x0 xp)
  obtain y where y: "y < p" "[x * y = a] (mod p)" "\<forall>z. z < p \<and> [x * z = a] (mod p) \<longrightarrow> z = y"
    by (metis cong_solve_unique neq0_conv p prime_gt_0_nat px)
  have "y \<noteq> 0"
  proof
    assume "y = 0"
    with y(2) have "p dvd a"
      by (auto dest: cong_dvd_eq_nat)
    then show False
      by (metis gcd_nat.absorb1 not_prime_1 p pa)
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
    by (metis cong_gcd_eq_nat)+
  then have "coprime x (a*b)"
    by (metis coprime_mul_eq)
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
      by (metis am cong_0_nat gcd_nat.right_neutral power_eq_one_eq_nat)
  next
    case 3
    from m obtain m' where m': "m = Suc m'" by (cases m) blast+
    have "d = 1" if d: "d dvd a" "d dvd n" for d
    proof -
      from am mod_less[OF \<open>n > 1\<close>] have am1: "a^m mod n = 1"
        by (simp add: cong_nat_def)
      from dvd_mult2[OF d(1), of "a^m'"] have dam: "d dvd a^m"
        by (simp add: m')
      from dvd_mod_iff[OF d(2), of "a^m"] dam am1 show ?thesis
        by simp
    qed
    then show ?thesis by blast
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

lemma nat_exists_least_iff: "(\<exists>(n::nat). P n) \<longleftrightarrow> (\<exists>n. P n \<and> (\<forall>m < n. \<not> P m))"
  by (metis ex_least_nat_le not_less0)

lemma nat_exists_least_iff': "(\<exists>(n::nat). P n) \<longleftrightarrow> P (Least P) \<and> (\<forall>m < (Least P). \<not> P m)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?lhs if ?rhs
    using that by blast
  show ?rhs if ?lhs
  proof -
    from \<open>?lhs\<close> obtain n where n: "P n" by blast
    let ?x = "Least P"
    have "\<not> P m" if "m < ?x" for m
      by (rule not_less_Least[OF that])
    with LeastI_ex[OF \<open>?lhs\<close>] show ?thesis
      by blast
  qed
qed

theorem lucas:
  assumes n2: "n \<ge> 2" and an1: "[a^(n - 1) = 1] (mod n)"
    and pn: "\<forall>p. prime p \<and> p dvd n - 1 \<longrightarrow> [a^((n - 1) div p) \<noteq> 1] (mod n)"
  shows "prime n"
proof-
  from n2 have n01: "n \<noteq> 0" "n \<noteq> 1" "n - 1 \<noteq> 0"
    by arith+
  from mod_less_divisor[of n 1] n01 have onen: "1 mod n = 1"
    by simp
  from lucas_coprime_lemma[OF n01(3) an1] cong_imp_coprime_nat an1
  have an: "coprime a n" "coprime (a^(n - 1)) n"
    by (auto simp add: coprime_exp gcd.commute)
  have False if H0: "\<exists>m. 0 < m \<and> m < n - 1 \<and> [a ^ m = 1] (mod n)" (is "EX m. ?P m")
  proof -
    from H0[unfolded nat_exists_least_iff[of ?P]] obtain m where
      m: "0 < m" "m < n - 1" "[a ^ m = 1] (mod n)" "\<forall>k <m. \<not>?P k"
      by blast
    have False if nm1: "(n - 1) mod m > 0"
    proof -
      from mod_less_divisor[OF m(1)] have th0:"(n - 1) mod m < m" by blast
      let ?y = "a^ ((n - 1) div m * m)"
      note mdeq = div_mult_mod_eq[of "(n - 1)" m]
      have yn: "coprime ?y n"
        by (metis an(1) coprime_exp gcd.commute)
      have "?y mod n = (a^m)^((n - 1) div m) mod n"
        by (simp add: algebra_simps power_mult)
      also have "\<dots> = (a^m mod n)^((n - 1) div m) mod n"
        using power_mod[of "a^m" n "(n - 1) div m"] by simp
      also have "\<dots> = 1" using m(3)[unfolded cong_nat_def onen] onen
        by (metis power_one)
      finally have *: "?y mod n = 1"  .
      have **: "[?y * a ^ ((n - 1) mod m) = ?y* 1] (mod n)"
        using an1[unfolded cong_nat_def onen] onen
          div_mult_mod_eq[of "(n - 1)" m, symmetric]
        by (simp add:power_add[symmetric] cong_nat_def * del: One_nat_def)
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
      by (simp add: cong_nat_def)
    finally have "[(a ^ ((n - 1) div p))= 1] (mod n)"
      using onen by (simp add: cong_nat_def)
    with pn th show ?thesis by blast
  qed
  then have "\<forall>m. 0 < m \<and> m < n - 1 \<longrightarrow> \<not> [a ^ m = 1] (mod n)"
    by blast
  then show ?thesis by (rule lucas_weak[OF n2 an1])
qed


subsection \<open>Definition of the order of a number mod n (0 in non-coprime case)\<close>

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
  from nat_exists_least_iff'[of ?P] ex assms show ?thesis
    unfolding o[symmetric] by auto
qed

text \<open>With the special value \<open>0\<close> for non-coprime case, it's more convenient.\<close>
lemma ord_works: "[a ^ (ord n a) = 1] (mod n) \<and> (\<forall>m. 0 < m \<and> m < ord n a \<longrightarrow> \<not> [a^ m = 1] (mod n))"
  for n :: nat
  by (cases "coprime n a") (use coprime_ord[of n a] in \<open>auto simp add: ord_def cong_nat_def\<close>)

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
    by (simp add : cong_nat_def power_mult power_mod)
  also have "[(a ^ (ord n a) mod n)^k = 1] (mod n)"
    using ord[of a n, unfolded cong_nat_def]
    by (simp add: cong_nat_def power_mod)
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
      with o prem show ?thesis by (simp add: cong_nat_def)
    next
      case (Suc d')
      then have d0: "d \<noteq> 0" by simp
      from prem obtain p where p: "p dvd n" "p dvd a" "p \<noteq> 1" by auto
      from \<open>?lhs\<close> obtain q1 q2 where q12: "a ^ d + n * q1 = 1 + n * q2"
        by (metis prem d0 gcd.commute lucas_coprime_lemma)
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
      by (metis cong_exp_nat ord power_one)
    from H have onz: "?o \<noteq> 0" by (simp add: ord_eq_0)
    then have op: "?o > 0" by simp
    from div_mult_mod_eq[of d "ord n a"] \<open>?lhs\<close>
    have "[a^(?o*?q + ?r) = 1] (mod n)"
      by (simp add: cong_nat_def mult.commute)
    then have "[(a^?o)^?q * (a^?r) = 1] (mod n)"
      by (simp add: cong_nat_def power_mult[symmetric] power_add[symmetric])
    then have th: "[a^?r = 1] (mod n)"
      using eqo mod_mult_left_eq[of "(a^?o)^?q" "a^?r" n]
      by (simp add: cong_nat_def del: One_nat_def) (metis mod_mult_left_eq nat_mult_1)
    show ?thesis
    proof (cases "?r = 0")
      case True
      then show ?thesis by (simp add: dvd_eq_mod_eq_0)
    next
      case False
      with mod_less_divisor[OF op, of d] have r0o:"?r >0 \<and> ?r < ?o" by simp
      from conjunct2[OF ord_works[of a n], rule_format, OF r0o] th
      show ?thesis by blast
    qed
  qed
qed

lemma order_divides_totient: "ord n a dvd totient n" if "coprime n a"
  by (metis euler_theorem gcd.commute ord_divides that)

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
      by (metis gcd.commute)
    have aen: "coprime (a^e) n"
      by (metis coprime_exp gcd.commute na)
    have acn: "coprime (a^c) n"
      by (metis coprime_exp gcd.commute na)
    from c have "[a^d = a^e] (mod n) \<longleftrightarrow> [a^(e + c) = a^(e + 0)] (mod n)"
      by simp
    also have "\<dots> \<longleftrightarrow> [a^e* a^c = a^e *a^0] (mod n)" by (simp add: power_add)
    also have  "\<dots> \<longleftrightarrow> [a ^ c = 1] (mod n)"
      using cong_mult_lcancel_nat [OF aen, of "a^c" "a^0"] by simp
    also have "\<dots> \<longleftrightarrow> ord n a dvd c"
      by (simp only: ord_divides)
    also have "\<dots> \<longleftrightarrow> [e + c = e + 0] (mod ord n a)"
      using cong_add_lcancel_nat
      by (metis cong_dvd_eq_nat dvd_0_right cong_dvd_modulus_nat cong_mult_self_nat nat_mult_1)
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
      by (metis cong_sym_nat)
  qed
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
      by (simp add: power_0_left cong_nat_def)
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
      by (metis cong_exp_nat ord power_one)
    then have pd0: "p dvd a^(ord p (a^r) * t*r) - 1"
      by (metis cong_to_1_nat exps)
    from nqr s s' have "(n - 1) div P = ord p (a^r) * t*r"
      using P0 by simp
    with caP have "coprime (a^(ord p (a^r) * t*r) - 1) n" by simp
    with p01 pn pd0 coprime_common_divisor_nat show False
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
    then have False using d dp pn
      by auto (metis One_nat_def Suc_pred an dvd_1_iff_1 gcd_greatest_iff lucas_coprime_lemma)
  }
  then have cpa: "coprime p a" by auto
  have arp: "coprime (a^r) p"
    by (metis coprime_exp cpa gcd.commute)
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
        using n by (simp add: cong_nat_def dvd_eq_mod_eq_0[symmetric])
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
      from divides_rexp[OF d, of "p - 1"] pS eq cong_dvd_eq_nat [OF an] n show False
        by simp
    qed
    then have b1: "b \<ge> 1" by arith
    from cong_imp_coprime_nat[OF Cong.cong_diff_nat[OF cong_sym_nat [OF b(1)] cong_refl_nat[of 1] b1]]
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

definition "primefact ps n \<longleftrightarrow> foldr op * ps 1 = n \<and> (\<forall>p\<in> set ps. prime p)"

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
  also have "\<dots> = foldr op * xs 1" by (induct xs) simp_all
  finally have "foldr op * xs 1 = n" ..
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
  have q: "prime q" "q * foldr op * qs 1 = n" "\<forall>p \<in>set qs. prime p"
    and p: "prime p" "p dvd q * foldr op * qs 1"
    by simp_all
  consider "p dvd q" | "p dvd foldr op * qs 1"
    by (metis p prime_dvd_mult_eq_nat)
  then show ?case
  proof cases
    case 1
    with p(1) q(1) have "p = q"
      unfolding prime_nat_iff by auto
    then show ?thesis by simp
  next
    case prem: 2
    from q(3) have pqs: "primefact qs (foldr op * qs 1)"
      by (simp add: primefact_def)
    from Cons.hyps[OF pqs p(1) prem] show ?thesis by simp
  qed
qed

lemma primefact_variant: "primefact ps n \<longleftrightarrow> foldr op * ps 1 = n \<and> list_all prime ps"
  by (auto simp add: primefact_def list_all_iff)

text \<open>Variant of Lucas theorem.\<close>
lemma lucas_primefact:
  assumes n: "n \<ge> 2" and an: "[a^(n - 1) = 1] (mod n)"
    and psn: "foldr op * ps 1 = n - 1"
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
    and arnb: "(a^r) mod n = b" and psq: "foldr op * ps 1 = q"
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
    by (metis bqn cong_nat_def mod_mod_trivial)
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
        unfolding mod_eq_0_iff by blast
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
      by (simp add: cong_nat_def)
    with ath[OF mod_less_eq_dividend *]
    have "[a ^ ((n - 1) div p) mod n - 1 = a ^ ((n - 1) div p) - 1] (mod n)"
      by (metis cong_diff_nat cong_refl_nat)
    then show ?thesis
      by (metis cong_imp_coprime_nat eq1 p')
  qed
  with pocklington[OF n qrn[symmetric] nq2 an1] show ?thesis
    by blast
qed

end
