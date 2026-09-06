section \<open>Residues: Euler, Fermat, Wilson and a primitive root, without any algebra library\<close>

theory Residues
  imports Cong Totient "HOL-Computational_Algebra.Polynomial"
begin

text \<open>
  This is a replacement for \<open>HOL-Number_Theory.Residues\<close> that uses no algebra library at all: the
  import closure is \<open>Cong\<close>, \<open>Totient\<close> and \<open>Polynomial\<close>.  It supplies everything the theories above
  \<open>Residues\<close> consume --- \<open>QuadRes\<close>, \<open>Legendre\<close>, \<open>euler_theorem\<close>, \<open>fermat_theorem\<close>,
  \<open>wilson_theorem\<close>, \<open>roots_mod_prime_bound\<close> and the existence of a primitive root.

  Two ingredients make it possible.  Root counting needs no field:
  @{thm [source] synthetic_div_correct'} splits a linear factor off with a constant remainder over any
  commutative ring, so @{typ "int poly"} reduced modulo a prime is enough.  And the primitive root
  then falls out of counting alone: each order class has at most \<open>totient d\<close> members, and
  @{thm [source] totient_divisor_sum} says those bounds already sum to \<open>p - 1\<close>, so none can fall
  short.
\<close>

text \<open>The factor theorem needs no field: over any commutative ring
  @{thm [source] synthetic_div_correct'} splits a linear factor off with a constant remainder.  So
  @{typ "int poly"} reduced modulo a prime is enough to bound the number of roots by the degree ---
  the one ingredient HOL-Algebra was supplying to \<open>Residues\<close>.  Being divisible by \<open>p\<close> coefficientwise
  is stated as @{term "[:p:] dvd f"}, which @{thm [source] const_poly_dvd_iff} relates to the
  coefficients.\<close>

lemma card_roots_mod_prime_le:
  fixes p :: int and f :: "int poly"
  assumes p: "prime p"
  shows "\<not> [:p:] dvd f \<Longrightarrow> card {x \<in> {0..<p}. [poly f x = 0] (mod p)} \<le> degree f"
proof (induct "degree f" arbitrary: f rule: less_induct)
  case (less f)
  define A where "A = {x \<in> {0..<p}. [poly f x = 0] (mod p)}"
  have finA: "finite A"
    unfolding A_def by (rule finite_subset [of _ "{0..<p}"]) auto
  have "card A \<le> degree f"
  proof (cases "A = {}")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain a where a: "a \<in> {0..<p}" and root: "[poly f a = 0] (mod p)"
      by (auto simp: A_def)
    define g where "g = synthetic_div f a"
    have fg: "[:- a, 1:] * g + [:poly f a:] = f"
      unfolding g_def by (rule synthetic_div_correct')
    have pa: "[:p:] dvd [:poly f a:]"
      using root by (simp add: cong_0_iff const_poly_dvd_iff coeff_pCons split: nat.split)
    \<comment> \<open>The quotient is not itself divisible by \<open>p\<close>, or neither would @{term f} be.\<close>
    have gnz: "\<not> [:p:] dvd g"
    proof
      assume "[:p:] dvd g"
      then have "[:p:] dvd [:- a, 1:] * g" by (rule dvd_mult)
      with pa have "[:p:] dvd f" using fg by (metis dvd_add)
      with less.prems show False by blast
    qed
    have deg: "degree g < degree f"
    proof -
      have "f \<noteq> 0" using less.prems by auto
      moreover have "degree f \<noteq> 0"
      proof
        assume "degree f = 0"
        then obtain c where "f = [:c:]" by (meson degree_eq_zeroE)
        with root have "[:p:] dvd f"
          by (simp add: cong_0_iff const_poly_dvd_iff coeff_pCons split: nat.split)
        with less.prems show False by blast
      qed
      ultimately show ?thesis
        unfolding g_def by (simp add: degree_synthetic_div)
    qed
    \<comment> \<open>Every root of @{term f} other than @{term a} is a root of the quotient: primality cancels.\<close>
    have sub: "A \<subseteq> insert a {x \<in> {0..<p}. [poly g x = 0] (mod p)}"
    proof
      fix b assume "b \<in> A"
      then have bp: "b \<in> {0..<p}" and rb: "[poly f b = 0] (mod p)" by (auto simp: A_def)
      show "b \<in> insert a {x \<in> {0..<p}. [poly g x = 0] (mod p)}"
      proof (cases "b = a")
        case True
        then show ?thesis by simp
      next
        case False
        have "poly f b = poly ([:- a, 1:] * g + [:poly f a:]) b"
          using fg by simp
        also have "\<dots> = (b - a) * poly g b + poly f a"
          by (simp add: algebra_simps)
        finally have "poly f b = (b - a) * poly g b + poly f a" .
        moreover have "p dvd poly f b" and "p dvd poly f a"
          using rb root by (simp_all add: cong_0_iff)
        ultimately have "p dvd (b - a) * poly g b" by algebra
        moreover have "\<not> p dvd (b - a)"
        proof
          assume pd: "p dvd (b - a)"
          have "b - a \<noteq> 0" using False by simp
          then have pos: "0 < \<bar>b - a\<bar>" by simp
          have "p dvd \<bar>b - a\<bar>" using pd by (simp add: dvd_abs_iff)
          then have "p \<le> \<bar>b - a\<bar>" using pos by (rule zdvd_imp_le)
          moreover have "\<bar>b - a\<bar> < p" using a bp by auto
          ultimately show False by simp
        qed
        ultimately have "p dvd poly g b"
          using p by (simp add: prime_dvd_mult_iff)
        with bp show ?thesis by (simp add: cong_0_iff)
      qed
    qed
    have fing: "finite {x \<in> {0..<p}. [poly g x = 0] (mod p)}"
      by (rule finite_subset [of _ "{0..<p}"]) auto
    have "card A \<le> card (insert a {x \<in> {0..<p}. [poly g x = 0] (mod p)})"
      using fing sub by (intro card_mono) auto
    also have "\<dots> \<le> Suc (card {x \<in> {0..<p}. [poly g x = 0] (mod p)})"
      using fing by (simp add: card_insert_if)
    also have "\<dots> \<le> Suc (degree g)"
      using less.hyps [OF deg gnz] by simp
    also have "\<dots> \<le> degree f" using deg by simp
    finally show ?thesis .
  qed
  then show ?case by (simp add: A_def)
qed

text \<open>Specialising to \<open>x\<^sup>n = c\<close> gives exactly the statement \<open>Residues\<close> currently obtains from
  HOL-Algebra's polynomial ring over \<open>\<int>/p\<int>\<close>.  The polynomial is monic, so \<open>p\<close> cannot divide it.\<close>

corollary roots_mod_prime_bound:
  fixes n c p :: nat
  assumes p: "prime p" and n: "n > 0"
  shows "card {x \<in> {..<p}. [x ^ n = c] (mod p)} \<le> n"
proof -
  define f :: "int poly" where "f = monom 1 n + (- [:int c:])"
  have degf: "degree f = n"
    unfolding f_def using n by (subst degree_add_eq_left) (simp_all add: degree_monom_eq)
  have coeffn: "coeff f n = 1"
    unfolding f_def using n by (cases n) simp_all
  have ndvd: "\<not> [:int p:] dvd f"
  proof
    assume "[:int p:] dvd f"
    then have "int p dvd coeff f n" by (simp add: const_poly_dvd_iff)
    with coeffn have "int p dvd 1" by simp
    with p show False by (simp add: prime_nat_iff)
  qed
  have polyf: "poly f (int x) = int (x ^ n) - int c" for x
    by (simp add: f_def poly_monom)
  \<comment> \<open>The nat solutions inject into the int ones.\<close>
  have "card {x \<in> {..<p}. [x ^ n = c] (mod p)}
        = card (int ` {x \<in> {..<p}. [x ^ n = c] (mod p)})"
    by (simp add: card_image)
  also have "\<dots> \<le> card {x \<in> {0..<int p}. [poly f x = 0] (mod int p)}"
  proof (rule card_mono)
    show "finite {x \<in> {0..<int p}. [poly f x = 0] (mod int p)}"
      by (rule finite_subset [of _ "{0..<int p}"]) auto
    show "int ` {x \<in> {..<p}. [x ^ n = c] (mod p)}
          \<subseteq> {x \<in> {0..<int p}. [poly f x = 0] (mod int p)}"
      using polyf by (auto simp: cong_iff_dvd_diff cong_int_iff [symmetric] of_nat_diff)
  qed
  also have "\<dots> \<le> degree f"
    by (rule card_roots_mod_prime_le [OF _ ndvd]) (use p in \<open>simp add: prime_int_nat_transfer\<close>)
  finally show ?thesis by (simp add: degf)
qed


subsection \<open>Euler's and Fermat's theorems\<close>

text \<open>Multiplication by a unit permutes the totatives: it is injective by cancellation and maps the
  set into itself, and a finite set admits no proper injection into itself.  Taking the product over
  the totatives and cancelling it --- it is coprime to the modulus --- gives Euler's theorem with no
  group theory at all.\<close>

lemma totatives_less:
  assumes "x \<in> totatives n" "n > 1"
  shows "x < n"
proof -
  have "x \<noteq> n" using assms by (auto simp: in_totatives_iff)
  with assms show ?thesis by (auto simp: in_totatives_iff)
qed

lemma mult_in_totatives:
  fixes a n x :: nat
  assumes n: "n > 1" and a: "coprime a n" and x: "x \<in> totatives n"
  shows "a * x mod n \<in> totatives n"
proof -
  have "coprime x n" using x by (simp add: in_totatives_iff)
  with a have "coprime (a * x) n" by simp
  then have cop: "coprime (a * x mod n) n"
    using n by (simp add: coprime_mod_left_iff)
  moreover have "a * x mod n \<noteq> 0"
  proof
    assume "a * x mod n = 0"
    then have dvd: "n dvd a * x" by auto
    have "coprime n (a * x)"
      using a \<open>coprime x n\<close> by (simp add: coprime_commute)
    from this dvd_refl dvd have "is_unit n" by (rule coprime_common_divisor)
    with n show False by simp
  qed
  ultimately show ?thesis using n by (auto simp: in_totatives_iff)
qed

lemma bij_betw_mult_totatives:
  fixes a n :: nat
  assumes n: "n > 1" and a: "coprime a n"
  shows "bij_betw (\<lambda>x. a * x mod n) (totatives n) (totatives n)"
proof (rule bij_betw_imageI)
  show inj: "inj_on (\<lambda>x. a * x mod n) (totatives n)"
  proof (rule inj_onI)
    fix x y assume xy: "x \<in> totatives n" "y \<in> totatives n" and eq: "a * x mod n = a * y mod n"
    from eq have "[a * x = a * y] (mod n)" by (simp add: cong_def)
    then have "[x = y] (mod n)" using a by (simp add: cong_mult_lcancel_nat)
    moreover have "x < n" and "y < n" using totatives_less [OF _ n] xy by blast+
    ultimately show "x = y" by (simp add: cong_def)
  qed
  show "(\<lambda>x. a * x mod n) ` totatives n = totatives n"
  proof (rule endo_inj_surj)
    show "finite (totatives n)" by simp
    show "(\<lambda>x. a * x mod n) ` totatives n \<subseteq> totatives n"
      using mult_in_totatives [OF n a] by blast
  qed (rule inj)
qed

theorem euler_theorem:
  fixes a n :: nat
  assumes a: "coprime a n"
  shows "[a ^ totient n = 1] (mod n)"
proof (cases "n \<le> 1")
  case True
  then consider "n = 0" | "n = 1" by linarith
  then show ?thesis by cases (auto simp: cong_def totient_def totatives_def)
next
  case False
  then have n: "n > 1" by simp
  define P where "P = (\<Prod>x\<in>totatives n. x)"
  have copP: "coprime P n"
    unfolding P_def by (rule prod_coprime_left) (simp add: in_totatives_iff)
  have "[(\<Prod>x\<in>totatives n. a * x) = (\<Prod>x\<in>totatives n. a * x mod n)] (mod n)"
    by (intro cong_prod) (simp add: cong_def)
  moreover have "(\<Prod>x\<in>totatives n. a * x mod n) = P"
    unfolding P_def
    by (rule prod.reindex_bij_betw [OF bij_betw_mult_totatives [OF n a], of id, simplified])
  moreover have "(\<Prod>x\<in>totatives n. a * x) = a ^ totient n * P"
    by (simp add: P_def prod.distrib prod_constant totient_def)
  ultimately have "[a ^ totient n * P = 1 * P] (mod n)" by simp
  then show ?thesis by (simp only: cong_mult_rcancel_nat [OF copP])
qed

theorem fermat_theorem:
  fixes p a :: nat
  assumes p: "prime p" and a: "\<not> p dvd a"
  shows "[a ^ (p - 1) = 1] (mod p)"
proof -
  have "coprime p a" using p a by (rule prime_imp_coprime)
  then have "coprime a p" by (simp add: coprime_commute)
  then have "[a ^ totient p = 1] (mod p)" by (rule euler_theorem)
  with p show ?thesis by (simp add: totient_prime)
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

subsection \<open>The multiplicative order\<close>

definition "ord n a = (if coprime n a then Least (\<lambda>d. d > 0 \<and> [a ^ d = 1] (mod n)) else 0)"

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

subsection \<open>A primitive root modulo a prime\<close>

lemma card_coprime_lessThan:
  fixes d :: nat
  assumes d: "d > 0"
  shows "card {i \<in> {..<d}. coprime i d} = totient d"
proof (cases "d = 1")
  case True
  then have "{i \<in> {..<d}. coprime i d} = {0}" by auto
  moreover have "totatives 1 = {1}" by (auto simp: totatives_def)
  ultimately show ?thesis using True by (simp add: totient_def)
next
  case False
  with d have d1: "d > 1" by simp
  have "{i \<in> {..<d}. coprime i d} = totatives d"
  proof (intro set_eqI iffI)
    fix i assume "i \<in> {i \<in> {..<d}. coprime i d}"
    then have i: "i < d" and cop: "coprime i d" by auto
    have "i \<noteq> 0"
    proof
      assume "i = 0"
      with cop have "is_unit d" by simp
      with d1 show False by simp
    qed
    with i cop show "i \<in> totatives d" by (simp add: in_totatives_iff)
  next
    fix k assume "k \<in> totatives d"
    then have k: "0 < k" "k \<le> d" and cop: "coprime k d" by (auto simp: in_totatives_iff)
    have "k \<noteq> d" using cop d1 by auto
    with k cop show "k \<in> {i \<in> {..<d}. coprime i d}" by simp
  qed
  then show ?thesis by (simp add: totient_def)
qed

text \<open>If some element has order exactly \<open>d\<close> then its powers exhaust the solutions of \<open>y\<^sup>d = 1\<close> ---
  that is where the root bound enters --- and among those powers only the ones with exponent coprime
  to \<open>d\<close> can have order \<open>d\<close>.  So there are at most \<open>totient d\<close> elements of order \<open>d\<close>.\<close>

lemma card_order_eq_le_totient:
  fixes p d :: nat
  assumes p: "prime p" and d: "d > 0"
  shows "card {y \<in> {1..<p}. ord p y = d} \<le> totient d"
proof (cases "{y \<in> {1..<p}. ord p y = d} = {}")
  case True
  show ?thesis unfolding True by simp
next
  case False
  have p1: "p > 1" by (rule prime_gt_1_nat [OF p])
  have cop: "coprime y p" if "y \<in> {1..<p}" for y
  proof -
    have "\<not> p dvd y" using that by (auto dest: dvd_imp_le)
    with p have "coprime p y" by (rule prime_imp_coprime)
    then show ?thesis by (simp add: coprime_commute)
  qed
  from False obtain x where x: "x \<in> {1..<p}" and ox: "ord p x = d" by blast
  define pw where "pw i = x ^ i mod p" for i
  have copx: "coprime x p" using x by (rule cop)
  have xd: "[x ^ d = 1] (mod p)"
    using ord ox by blast
  \<comment> \<open>The powers are \<open>d\<close> distinct solutions.\<close>
  have pw_cop: "coprime (pw i) p" for i
  proof -
    have "coprime (x ^ i) p" using copx by simp
    then show ?thesis unfolding pw_def using p1 by (simp add: coprime_mod_left_iff)
  qed
  have pw_in: "pw i \<in> {1..<p}" for i
  proof -
    have "pw i \<noteq> 0"
    proof
      assume "pw i = 0"
      with pw_cop [of i] have "is_unit p" by simp
      with p1 show False by simp
    qed
    moreover have "pw i < p" using p1 by (simp add: pw_def)
    ultimately show ?thesis by simp
  qed
  have pw_inj: "inj_on pw {..<d}"
  proof (rule inj_onI)
    fix i j assume ij: "i \<in> {..<d}" "j \<in> {..<d}" and eq: "pw i = pw j"
    show "i = j"
    proof (rule ccontr)
      assume "i \<noteq> j"
      then consider "i < j" | "j < i" by linarith
      then show False
      proof cases
        case 1
        have "[x ^ i * 1 = x ^ i * x ^ (j - i)] (mod p)"
          using eq 1 by (simp add: pw_def cong_def power_add [symmetric])
        moreover have "coprime (x ^ i) p" using copx by simp
        ultimately have "[1 = x ^ (j - i)] (mod p)"
          by (simp only: cong_mult_lcancel_nat)
        then have "ord p x dvd (j - i)"
          using cong_sym ord_divides by blast
        with ox 1 ij show False by (auto dest: dvd_imp_le)
      next
        case 2
        have "[x ^ j * 1 = x ^ j * x ^ (i - j)] (mod p)"
          using eq 2 by (simp add: pw_def cong_def power_add [symmetric])
        moreover have "coprime (x ^ j) p" using copx by simp
        ultimately have "[1 = x ^ (i - j)] (mod p)"
          by (simp only: cong_mult_lcancel_nat)
        then have "ord p x dvd (i - j)"
          using cong_sym ord_divides by blast
        with ox 2 ij show False by (auto dest: dvd_imp_le)
      qed
    qed
  qed
  define R where "R = {y \<in> {..<p}. [y ^ d = 1] (mod p)}"
  have finR: "finite R" unfolding R_def by simp
  have pwR: "pw ` {..<d} \<subseteq> R"
  proof
    fix y assume "y \<in> pw ` {..<d}"
    then obtain i where y: "y = pw i" by blast
    have "(x ^ i) ^ d = (x ^ d) ^ i"
      by (simp add: power_mult [symmetric] mult.commute)
    moreover have "[(x ^ d) ^ i = 1 ^ i] (mod p)" using xd by (rule cong_pow)
    ultimately have "[(x ^ i) ^ d = 1] (mod p)" by simp
    then have "[pw i ^ d = 1] (mod p)"
      unfolding pw_def by (metis cong_def power_mod)
    with y pw_in [of i] show "y \<in> R" by (auto simp: R_def)
  qed
  have cardR: "card R \<le> d"
    unfolding R_def using roots_mod_prime_bound [OF p d, of 1] by simp
  have Req: "R = pw ` {..<d}"
  proof (rule card_subset_eq [symmetric])
    show "finite R" by (rule finR)
    show "pw ` {..<d} \<subseteq> R" by (rule pwR)
    show "card (pw ` {..<d}) = card R"
      using cardR card_mono [OF finR pwR] pw_inj by (simp add: card_image)
  qed
  \<comment> \<open>Only exponents coprime to \<open>d\<close> give order \<open>d\<close>.\<close>
  have coprime_exp: "coprime i d" if i: "i < d" and o: "ord p (pw i) = d" for i
  proof -
    define g where "g = gcd i d"
    have g0: "g > 0" using d by (simp add: g_def)
    have gi: "g dvd i" and gd: "g dvd d" by (simp_all add: g_def)
    have "i * (d div g) = (i div g) * d"
    proof -
      have "i * (d div g) = (i div g * g) * (d div g)" using gi by (simp add: dvd_div_mult_self)
      also have "\<dots> = (i div g) * (g * (d div g))" by (simp add: mult.assoc)
      also have "\<dots> = (i div g) * d" using gd by (simp add: dvd_div_mult_self mult.commute)
      finally show ?thesis .
    qed
    then have "(x ^ i) ^ (d div g) = (x ^ d) ^ (i div g)"
    proof -
      assume eqd: "i * (d div g) = (i div g) * d"
      have "(x ^ i) ^ (d div g) = x ^ (i * (d div g))" by (simp add: power_mult)
      also have "\<dots> = x ^ ((i div g) * d)" using eqd by simp
      also have "\<dots> = (x ^ d) ^ (i div g)" by (simp add: power_mult mult.commute)
      finally show ?thesis .
    qed
    moreover have "[(x ^ d) ^ (i div g) = 1 ^ (i div g)] (mod p)" using xd by (rule cong_pow)
    ultimately have "[(x ^ i) ^ (d div g) = 1] (mod p)" by simp
    then have "[pw i ^ (d div g) = 1] (mod p)"
      unfolding pw_def by (metis cong_def power_mod)
    then have "ord p (pw i) dvd (d div g)"
      using cong_sym ord_divides by blast
    with o have dvd_dg: "d dvd d div g" by simp
    have gdg: "g * (d div g) = d" using gd by (simp add: dvd_mult_div_cancel)
    have pos: "0 < d div g" using d gdg by (cases "d div g = 0") auto
    have "d \<le> d div g" using dvd_dg pos by (rule dvd_imp_le)
    moreover have "d div g \<le> d" using g0 by simp
    ultimately have "d div g = d" by simp
    with gdg have "g * d = d" by simp
    with d have "g = 1" by simp
    then show ?thesis by (simp add: g_def coprime_iff_gcd_eq_1)
  qed
  \<comment> \<open>Hence the elements of order \<open>d\<close> are among those powers.\<close>
  have "{y \<in> {1..<p}. ord p y = d} \<subseteq> pw ` {i \<in> {..<d}. coprime i d}"
  proof
    fix y assume y: "y \<in> {y \<in> {1..<p}. ord p y = d}"
    then have yp: "y \<in> {1..<p}" and oy: "ord p y = d" by auto
    have "[y ^ d = 1] (mod p)"
      using ord oy by blast
    with yp have "y \<in> R" by (auto simp: R_def)
    then obtain i where i: "i < d" and yi: "y = pw i" using Req by blast
    with oy have "ord p (pw i) = d" by simp
    with i have "coprime i d" by (rule coprime_exp)
    with i yi show "y \<in> pw ` {i \<in> {..<d}. coprime i d}" by blast
  qed
  then have "card {y \<in> {1..<p}. ord p y = d} \<le> card (pw ` {i \<in> {..<d}. coprime i d})"
    by (intro card_mono) auto
  also have "\<dots> \<le> card {i \<in> {..<d}. coprime i d}" by (rule card_image_le) simp
  also have "\<dots> = totient d" by (rule card_coprime_lessThan [OF d])
  finally show ?thesis .
qed


text \<open>Every nonzero residue has some order dividing \<open>p - 1\<close>, so the classes partition \<open>{1..<p}\<close>.
  Since each class has at most \<open>totient d\<close> members and @{thm [source] totient_divisor_sum} says those
  bounds already sum to \<open>p - 1\<close>, none of them can fall short: in particular there is an element of
  order \<open>p - 1\<close>.\<close>

lemma exists_primitive_root:
  fixes p :: nat
  assumes p: "prime p"
  shows "\<exists>x \<in> {1..<p}. ord p x = p - 1"
proof -
  have p1: "p > 1" by (rule prime_gt_1_nat [OF p])
  then have p0: "p - 1 > 0" by simp
  have cop: "coprime y p" if "y \<in> {1..<p}" for y
  proof -
    have "\<not> p dvd y" using that by (auto dest: dvd_imp_le)
    with p have "coprime p y" by (rule prime_imp_coprime)
    then show ?thesis by (simp add: coprime_commute)
  qed
  define S where "S d = {y \<in> {1..<p}. ord p y = d}" for d
  have ord_dvd: "ord p y dvd p - 1" if "y \<in> {1..<p}" for y
  proof -
    have "\<not> p dvd y" using that by (auto dest: dvd_imp_le)
    with p have "[y ^ (p - 1) = 1] (mod p)" by (rule fermat_theorem)
    then show ?thesis
      using ord_divides by blast
  qed
  \<comment> \<open>The order classes partition the nonzero residues.\<close>
  have part: "{1..<p} = (\<Union>d \<in> {d. d dvd p - 1}. S d)"
    using ord_dvd by (auto simp: S_def)
  have finD: "finite {d. d dvd p - 1}" using p0 by (simp add: finite_divisors_nat)
  have "p - 1 = card {1..<p}" using p1 by simp
  also have "\<dots> = (\<Sum>d | d dvd p - 1. card (S d))"
    unfolding part
    by (rule card_UN_disjoint) (use finD in \<open>auto simp: S_def\<close>)
  finally have sum_eq: "p - 1 = (\<Sum>d | d dvd p - 1. card (S d))" .
  have le: "card (S d) \<le> totient d" if "d dvd p - 1" for d
  proof (cases "d = 0")
    case True
    with that p0 show ?thesis by (simp add: S_def)
  next
    case False
    then show ?thesis
      unfolding S_def by (intro card_order_eq_le_totient [OF p]) simp
  qed
  have "(\<Sum>d | d dvd p - 1. card (S d)) \<le> (\<Sum>d | d dvd p - 1. totient d)"
    using finD le by (intro sum_mono) simp
  moreover have "(\<Sum>d | d dvd p - 1. totient d) = p - 1"
    by (rule totient_divisor_sum)
  ultimately have "(\<Sum>d | d dvd p - 1. card (S d)) = (\<Sum>d | d dvd p - 1. totient d)"
    using sum_eq by simp
  then have "card (S (p - 1)) = totient (p - 1)"
  proof (rule sum_mono_inv)
    show "\<And>i. i \<in> {d. d dvd p - 1} \<Longrightarrow> card (S i) \<le> totient i"
      using le by simp
    show "p - 1 \<in> {d. d dvd p - 1}" by simp
    show "finite {d. d dvd p - 1}" by (rule finD)
  qed
  moreover have "totient (p - 1) > 0" using p0 by simp
  ultimately have "S (p - 1) \<noteq> {}" by auto
  then show ?thesis by (auto simp: S_def)
qed


theorem residue_prime_mult_group_has_gen:
 fixes p :: nat
 assumes prime_p : "prime p"
 shows "\<exists>a \<in> {1 .. p - 1}. {1 .. p - 1} = {a^i mod p|i . i \<in> UNIV}"
proof -
  have "p \<ge> 2"
    using prime_gt_1_nat[OF prime_p] by simp
  obtain a where a: "a \<in> {1..p-1}" "ord p a = p-1"
    using exists_primitive_root[OF assms] by fastforce
  then have nz: "a^i mod p \<noteq> 0" for i
    using prime_p
    by (metis diff_is_0_eq less_eq_Suc_le less_one mod_by_0 mod_mult_self1_is_0 not_less_eq_eq
        ord_0_right_nat ord_mod ord_power_aux prime_gt_1_nat)
  have "\<not> [a ^ i = 1] (mod p)" if "i \<in> {1..<p-1}" for i
    using a(2) ord_minimal that by auto
  have range: "range(\<lambda>i. a ^ i mod p) \<subseteq> {0<..<p}"
    using nz by (auto simp: prime_gt_0_nat prime_p)
  moreover have "inj_on (\<lambda>i. a ^ i mod p) {0<..<p}"
  proof -
    { fix i :: nat and j :: nat
      assume "a ^ i mod p = a ^ j mod p"
        and "0 < i"
        and "i < p"
        and "0 < j"
        and "j < p"
        and "i < j"
      then have "[a ^ (j-i) = 1] (mod p)"
        using a(2) prime_p
        by (metis cong_altdef_nat cong_mod_left cong_refl diff_is_0_eq' nle_le ord_divides ord_gt_0_iff
            order_divides_expdiff prime_gt_1_nat zero_less_diff)
      then have False
        using \<open>0 < i\<close> \<open>i < j\<close> \<open>j < p\<close> a(2) ord_minimal by fastforce
    } then show ?thesis
      by (meson greaterThanLessThan_iff linorder_inj_onI')
  qed
  ultimately
  have "card (range(\<lambda>i. a ^ i mod p)) = card {0<..<p}"
    by (metis (mono_tags, lifting) card.infinite card_inj_on_le card_seteq finite_imageD image_mono
        rev_finite_subset top.extremum)
  with range have "{0<..<p} = range(\<lambda>i. a ^ i mod p)"
    by (metis Set_Interval.finite_greaterThanLessThan card_seteq dual_order.refl)
  moreover have "{0<..<p} = {1..p - 1}"
    by force
  ultimately show ?thesis
    using a(1) by (metis Setcompr_eq_image)
qed

lemma residue_prime_has_primroot:
  fixes p :: nat
  assumes "prime p"
  shows "\<exists>a\<in>totatives p. ord p a = p - 1"
  using assms exists_primitive_root[OF assms] 
  apply (clarsimp simp: totatives_def)
  by (metis One_nat_def coprime_commute less_eq_Suc_le ord_gt_0_iff order_less_le prime_nat_iff
      zero_less_diff)

subsection \<open>The nonzero residues are the powers of a primitive root\<close>

lemma inj_on_powers_primitive_root:
  fixes p x :: nat
  assumes p: "prime p" and x: "x \<in> {1..<p}" and ox: "ord p x = p - 1"
  shows "inj_on (\<lambda>i. x ^ i mod p) {..<p - 1}"
proof -
  have p1: "p > 1" by (rule prime_gt_1_nat [OF p])
  have "\<not> p dvd x" using x by (auto dest: dvd_imp_le)
  with p have "coprime p x" by (rule prime_imp_coprime)
  then have copx: "coprime x p" by (simp add: coprime_commute)
  show ?thesis
  proof (rule inj_onI)
    fix i j assume ij: "i \<in> {..<p-1}" "j \<in> {..<p-1}" and eq: "x ^ i mod p = x ^ j mod p"
    show "i = j"
    proof (rule ccontr)
      assume "i \<noteq> j"
      then consider "i < j" | "j < i" by linarith
      then show False
      proof cases
        case 1
        have "[x ^ i * 1 = x ^ i * x ^ (j - i)] (mod p)"
          using eq 1 by (simp add: cong_def power_add [symmetric])
        moreover have "coprime (x ^ i) p" using copx by simp
        ultimately have "[1 = x ^ (j - i)] (mod p)" by (simp only: cong_mult_lcancel_nat)
        then have "ord p x dvd (j - i)"
          using cong_sym ord_divides by blast
        with ox 1 ij show False by (auto dest: dvd_imp_le)
      next
        case 2
        have "[x ^ j * 1 = x ^ j * x ^ (i - j)] (mod p)"
          using eq 2 by (simp add: cong_def power_add [symmetric])
        moreover have "coprime (x ^ j) p" using copx by simp
        ultimately have "[1 = x ^ (i - j)] (mod p)" by (simp only: cong_mult_lcancel_nat)
        then have "ord p x dvd (i - j)"
          using cong_sym ord_divides by blast
        with ox 2 ij show False by (auto dest: dvd_imp_le)
      qed
    qed
  qed
qed

lemma powers_of_primitive_root:
  fixes p x :: nat
  assumes p: "prime p" and x: "x \<in> {1..<p}" and ox: "ord p x = p - 1"
  shows "{1..<p} = (\<lambda>i. x ^ i mod p) ` {..<p - 1}"
proof -
  have p1: "p > 1" by (rule prime_gt_1_nat [OF p])
  have "\<not> p dvd x" using x by (auto dest: dvd_imp_le)
  with p have "coprime p x" by (rule prime_imp_coprime)
  then have copx: "coprime x p" by (simp add: coprime_commute)
  have pw_cop: "coprime (x ^ i mod p) p" for i
  proof -
    have "coprime (x ^ i) p" using copx by simp
    then show ?thesis using p1 by (simp add: coprime_mod_left_iff)
  qed
  have sub: "(\<lambda>i. x ^ i mod p) ` {..<p - 1} \<subseteq> {1..<p}"
  proof
    fix y assume "y \<in> (\<lambda>i. x ^ i mod p) ` {..<p - 1}"
    then obtain i where y: "y = x ^ i mod p" by blast
    have "y \<noteq> 0"
    proof
      assume "y = 0"
      with y pw_cop [of i] have "is_unit p" by simp
      with p1 show False by simp
    qed
    moreover have "y < p" using y p1 by simp
    ultimately show "y \<in> {1..<p}" by simp
  qed
  have inj: "inj_on (\<lambda>i. x ^ i mod p) {..<p - 1}"
    by (rule inj_on_powers_primitive_root [OF p x ox])
  have "card ((\<lambda>i. x ^ i mod p) ` {..<p - 1}) = p - 1" using inj by (simp add: card_image)
  moreover have "card {1..<p} = p - 1" using p1 by simp
  ultimately show ?thesis using sub by (intro card_subset_eq [symmetric]) auto
qed


subsection \<open>Wilson's theorem\<close>

lemma sum_lessThan_double:
  fixes t :: nat
  shows "(\<Sum>i<2*t. i) = t * (2*t - 1)"
proof (induct t)
  case 0
  show ?case by simp
next
  case (Suc t)
  have "(\<Sum>i<2 * Suc t. i) = (\<Sum>i<2*t. i) + 2*t + (2*t+1)"
    by (simp add: lessThan_Suc)
  also have "\<dots> = t * (2*t - 1) + 2*t + (2*t+1)" using Suc by simp
  also have "\<dots> = Suc t * (2 * Suc t - 1)" by (cases t) (auto simp: algebra_simps)
  finally show ?case .
qed

text \<open>A square root of one modulo a prime is \<open>\<plusminus>1\<close>: the prime divides \<open>(x-1)(x+1)\<close>.\<close>

lemma sqrt_one_mod_prime:
  fixes p x :: nat
  assumes p: "prime p" and sq: "[x ^ 2 = 1] (mod p)"
  shows "[x = 1] (mod p) \<or> [x + 1 = 0] (mod p)"
proof -
  have "int p dvd (int x - 1) * (int x + 1)"
  proof -
    have "[int x ^ 2 = 1] (mod int p)" using sq by (simp add: cong_int_iff [symmetric])
    then have "int p dvd int x ^ 2 - 1" by (simp add: cong_iff_dvd_diff)
    then show ?thesis by (simp add: power2_eq_square algebra_simps)
  qed
  moreover have "prime (int p)" using p by (simp add: prime_int_nat_transfer)
  ultimately have "int p dvd (int x - 1) \<or> int p dvd (int x + 1)"
    by (simp add: prime_dvd_mult_iff)
  then show ?thesis
  proof
    assume "int p dvd int x - 1"
    then have "[int x = int 1] (mod int p)" by (simp add: cong_iff_dvd_diff)
    then have "[x = 1] (mod p)" using cong_int_iff by blast
    then show ?thesis by simp
  next
    assume "int p dvd int x + 1"
    then have "[int x + 1 = 0] (mod int p)" by (simp add: cong_iff_dvd_diff)
    then have "[int (x + 1) = int 0] (mod int p)" by (simp add: add.commute)
    then have "[x + 1 = 0] (mod p)" using cong_int_iff by blast
    then show ?thesis by simp
  qed
qed

text \<open>The product of the nonzero residues modulo an odd prime is \<open>-1\<close>.  Written as powers of a
  primitive root the product is that root raised to the sum of the exponents below its order; for
  order \<open>2t\<close> that sum is \<open>t(2t-1)\<close>, so the product is \<open>(g\<^sup>t)\<^sup>2\<^sup>t\<^sup>-\<^sup>1\<close>, and \<open>g\<^sup>t\<close> squares to one without
  being one.\<close>

lemma prod_nonzero_residues:
  fixes p :: nat
  assumes p: "prime p" and p2: "2 < p"
  shows "[int (\<Prod>y\<in>{1..<p}. y) = - 1] (mod int p)"
proof -
  have p1: "p > 1" by (rule prime_gt_1_nat [OF p])
  obtain g where g: "g \<in> {1..<p}" and og: "ord p g = p - 1"
    using exists_primitive_root [OF p] by blast
  have "\<not> p dvd g" using g by (auto dest: dvd_imp_le)
  with p have "coprime p g" by (rule prime_imp_coprime)
  then have copg: "coprime g p" by (simp add: coprime_commute)
  \<comment> \<open>The modulus is odd, so the order is even.\<close>
  have "odd p" using p p2 by (simp add: prime_odd_nat)
  then obtain t where pt: "p = 2 * t + 1" by (auto elim: oddE)
  then have m: "p - 1 = 2 * t" by simp
  have t0: "t > 0" using m p2 by auto
  \<comment> \<open>Write the product as a power of the root.\<close>
  have "(\<Prod>y\<in>{1..<p}. y) = (\<Prod>y\<in>(\<lambda>i. g ^ i mod p) ` {..<p-1}. y)"
    using powers_of_primitive_root [OF p g og] by simp
  also have "\<dots> = (\<Prod>i<p-1. g ^ i mod p)"
    using inj_on_powers_primitive_root [OF p g og] by (simp add: prod.reindex)
  also have "[(\<Prod>i<p-1. g ^ i mod p) = (\<Prod>i<p-1. g ^ i)] (mod p)"
    by (intro cong_prod) (simp add: cong_def)
  finally have base: "[(\<Prod>y\<in>{1..<p}. y) = g ^ (\<Sum>i<p-1. i)] (mod p)"
    by (simp add: power_sum)
  have sumeq: "(\<Sum>i<p-1. i) = t * (2*t - 1)"
    using m sum_lessThan_double [of t] by simp
  have "g ^ (\<Sum>i<p-1. i) = (g ^ t) ^ (2*t - 1)"
    by (simp only: sumeq power_mult)
  with base have prodg: "[(\<Prod>y\<in>{1..<p}. y) = (g ^ t) ^ (2*t - 1)] (mod p)" by simp
  \<comment> \<open>The half-power is a square root of one, and not one.\<close>
  have sq: "[(g ^ t) ^ 2 = 1] (mod p)"
    using m og by (metis mult.commute ord_works power_mult)
  have not1: "\<not> [g ^ t = 1] (mod p)"
    using m og ord_divides t0 by force
  from sqrt_one_mod_prime [OF p sq] not1 have "[g ^ t + 1 = 0] (mod p)" by blast
  \<comment> \<open>An odd power of \<open>-1\<close> is \<open>-1\<close>.\<close>
  then have "p dvd (g ^ t + 1)" by (simp add: cong_0_iff)
  then have "int p dvd int (g ^ t + 1)" by (simp only: of_nat_dvd_iff)
  then have "[int (g ^ t) = - 1] (mod int p)"
    by (simp add: cong_iff_dvd_diff algebra_simps)
  then have "[int ((g ^ t) ^ (2*t - 1)) = (- 1) ^ (2*t - 1)] (mod int p)"
    by (simp add: cong_pow)
  moreover have "odd (2*t - 1)" using t0 by simp
  ultimately have c2: "[int ((g ^ t) ^ (2*t - 1)) = - 1] (mod int p)" by simp
  have c1: "[int (\<Prod>y\<in>{1..<p}. y) = int ((g ^ t) ^ (2*t - 1))] (mod int p)"
    using prodg by (simp only: cong_int_iff)
  from c1 c2 show ?thesis by (rule cong_trans)
qed

theorem wilson_theorem:
  fixes p :: nat
  assumes p: "prime p"
  shows "[fact (p - 1) = (- 1 :: int)] (mod int p)"
proof (cases "p = 2")
  case True
  then show ?thesis by (simp add: cong_def)
next
  case False
  with p have p2: "2 < p" by (simp add: prime_ge_2_nat le_neq_implies_less)
  have "(fact (p - 1) :: nat) = (\<Prod>y\<in>{1..<p}. y)"
    using p2 by (simp add: fact_prod atLeastLessThanSuc_atLeastAtMost [symmetric])
  then have "(fact (p - 1) :: int) = int (\<Prod>y\<in>{1..<p}. y)"
    by (metis of_nat_fact)
  moreover have "[int (\<Prod>y\<in>{1..<p}. y) = - 1] (mod int p)"
    by (rule prod_nonzero_residues [OF p p2])
  ultimately show ?thesis by simp
qed


subsection \<open>Quadratic residues and the Legendre symbol\<close>

definition QuadRes :: "int \<Rightarrow> int \<Rightarrow> bool"
  where "QuadRes p a = (\<exists>y. ([y^2 = a] (mod p)))"

definition Legendre :: "int \<Rightarrow> int \<Rightarrow> int"
  where "Legendre a p =
    (if ([a = 0] (mod p)) then 0
     else if QuadRes p a then 1
     else -1)"

end
