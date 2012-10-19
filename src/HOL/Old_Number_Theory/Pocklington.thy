(*  Title:      HOL/Old_Number_Theory/Pocklington.thy
    Author:     Amine Chaieb
*)

header {* Pocklington's Theorem for Primes *}

theory Pocklington
imports Primes
begin

definition modeq:: "nat => nat => nat => bool"    ("(1[_ = _] '(mod _'))")
  where "[a = b] (mod p) == ((a mod p) = (b mod p))"

definition modneq:: "nat => nat => nat => bool"    ("(1[_ \<noteq> _] '(mod _'))")
  where "[a \<noteq> b] (mod p) == ((a mod p) \<noteq> (b mod p))"

lemma modeq_trans:
  "\<lbrakk> [a = b] (mod p); [b = c] (mod p) \<rbrakk> \<Longrightarrow> [a = c] (mod p)"
  by (simp add:modeq_def)


lemma nat_mod_lemma: assumes xyn: "[x = y] (mod n)" and xy:"y \<le> x"
  shows "\<exists>q. x = y + n * q"
using xyn xy unfolding modeq_def using nat_mod_eq_lemma by blast

lemma nat_mod[algebra]: "[x = y] (mod n) \<longleftrightarrow> (\<exists>q1 q2. x + n * q1 = y + n * q2)"
unfolding modeq_def nat_mod_eq_iff ..

(* Lemmas about previously defined terms.                                    *)

lemma prime: "prime p \<longleftrightarrow> p \<noteq> 0 \<and> p\<noteq>1 \<and> (\<forall>m. 0 < m \<and> m < p \<longrightarrow> coprime p m)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume "p=0 \<or> p=1" hence ?thesis using prime_0 prime_1 by (cases "p=0", simp_all)}
  moreover
  {assume p0: "p\<noteq>0" "p\<noteq>1"
    {assume H: "?lhs"
      {fix m assume m: "m > 0" "m < p"
        {assume "m=1" hence "coprime p m" by simp}
        moreover
        {assume "p dvd m" hence "p \<le> m" using dvd_imp_le m by blast with m(2)
          have "coprime p m" by simp}
        ultimately have "coprime p m" using prime_coprime[OF H, of m] by blast}
      hence ?rhs using p0 by auto}
    moreover
    { assume H: "\<forall>m. 0 < m \<and> m < p \<longrightarrow> coprime p m"
      from prime_factor[OF p0(2)] obtain q where q: "prime q" "q dvd p" by blast
      from prime_ge_2[OF q(1)] have q0: "q > 0" by arith
      from dvd_imp_le[OF q(2)] p0 have qp: "q \<le> p" by arith
      {assume "q = p" hence ?lhs using q(1) by blast}
      moreover
      {assume "q\<noteq>p" with qp have qplt: "q < p" by arith
        from H[rule_format, of q] qplt q0 have "coprime p q" by arith
        with coprime_prime[of p q q] q have False by simp hence ?lhs by blast}
      ultimately have ?lhs by blast}
    ultimately have ?thesis by blast}
  ultimately show ?thesis  by (cases"p=0 \<or> p=1", auto)
qed

lemma finite_number_segment: "card { m. 0 < m \<and> m < n } = n - 1"
proof-
  have "{ m. 0 < m \<and> m < n } = {1..<n}" by auto
  thus ?thesis by simp
qed

lemma coprime_mod: assumes n: "n \<noteq> 0" shows "coprime (a mod n) n \<longleftrightarrow> coprime a n"
  using n dvd_mod_iff[of _ n a] by (auto simp add: coprime)

(* Congruences.                                                              *)

lemma cong_mod_01[simp,presburger]:
  "[x = y] (mod 0) \<longleftrightarrow> x = y" "[x = y] (mod 1)" "[x = 0] (mod n) \<longleftrightarrow> n dvd x"
  by (simp_all add: modeq_def, presburger)

lemma cong_sub_cases:
  "[x = y] (mod n) \<longleftrightarrow> (if x <= y then [y - x = 0] (mod n) else [x - y = 0] (mod n))"
apply (auto simp add: nat_mod)
apply (rule_tac x="q2" in exI)
apply (rule_tac x="q1" in exI, simp)
apply (rule_tac x="q2" in exI)
apply (rule_tac x="q1" in exI, simp)
apply (rule_tac x="q1" in exI)
apply (rule_tac x="q2" in exI, simp)
apply (rule_tac x="q1" in exI)
apply (rule_tac x="q2" in exI, simp)
done

lemma cong_mult_lcancel: assumes an: "coprime a n" and axy:"[a * x = a * y] (mod n)"
  shows "[x = y] (mod n)"
proof-
  {assume "a = 0" with an axy coprime_0'[of n] have ?thesis by (simp add: modeq_def) }
  moreover
  {assume az: "a\<noteq>0"
    {assume xy: "x \<le> y" hence axy': "a*x \<le> a*y" by simp
      with axy cong_sub_cases[of "a*x" "a*y" n]  have "[a*(y - x) = 0] (mod n)"
        by (simp only: if_True diff_mult_distrib2)
      hence th: "n dvd a*(y -x)" by simp
      from coprime_divprod[OF th] an have "n dvd y - x"
        by (simp add: coprime_commute)
      hence ?thesis using xy cong_sub_cases[of x y n] by simp}
    moreover
    {assume H: "\<not>x \<le> y" hence xy: "y \<le> x"  by arith
      from H az have axy': "\<not> a*x \<le> a*y" by auto
      with axy H cong_sub_cases[of "a*x" "a*y" n]  have "[a*(x - y) = 0] (mod n)"
        by (simp only: if_False diff_mult_distrib2)
      hence th: "n dvd a*(x - y)" by simp
      from coprime_divprod[OF th] an have "n dvd x - y"
        by (simp add: coprime_commute)
      hence ?thesis using xy cong_sub_cases[of x y n] by simp}
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma cong_mult_rcancel: assumes an: "coprime a n" and axy:"[x*a = y*a] (mod n)"
  shows "[x = y] (mod n)"
  using cong_mult_lcancel[OF an axy[unfolded mult_commute[of _a]]] .

lemma cong_refl: "[x = x] (mod n)" by (simp add: modeq_def)

lemma eq_imp_cong: "a = b \<Longrightarrow> [a = b] (mod n)" by (simp add: cong_refl)

lemma cong_commute: "[x = y] (mod n) \<longleftrightarrow> [y = x] (mod n)"
  by (auto simp add: modeq_def)

lemma cong_trans[trans]: "[x = y] (mod n) \<Longrightarrow> [y = z] (mod n) \<Longrightarrow> [x = z] (mod n)"
  by (simp add: modeq_def)

lemma cong_add: assumes xx': "[x = x'] (mod n)" and yy':"[y = y'] (mod n)"
  shows "[x + y = x' + y'] (mod n)"
proof-
  have "(x + y) mod n = (x mod n + y mod n) mod n"
    by (simp add: mod_add_left_eq[of x y n] mod_add_right_eq[of "x mod n" y n])
  also have "\<dots> = (x' mod n + y' mod n) mod n" using xx' yy' modeq_def by simp
  also have "\<dots> = (x' + y') mod n"
    by (simp add: mod_add_left_eq[of x' y' n] mod_add_right_eq[of "x' mod n" y' n])
  finally show ?thesis unfolding modeq_def .
qed

lemma cong_mult: assumes xx': "[x = x'] (mod n)" and yy':"[y = y'] (mod n)"
  shows "[x * y = x' * y'] (mod n)"
proof-
  have "(x * y) mod n = (x mod n) * (y mod n) mod n"
    by (simp add: mod_mult_left_eq[of x y n] mod_mult_right_eq[of "x mod n" y n])
  also have "\<dots> = (x' mod n) * (y' mod n) mod n" using xx'[unfolded modeq_def] yy'[unfolded modeq_def] by simp
  also have "\<dots> = (x' * y') mod n"
    by (simp add: mod_mult_left_eq[of x' y' n] mod_mult_right_eq[of "x' mod n" y' n])
  finally show ?thesis unfolding modeq_def .
qed

lemma cong_exp: "[x = y] (mod n) \<Longrightarrow> [x^k = y^k] (mod n)"
  by (induct k, auto simp add: cong_refl cong_mult)
lemma cong_sub: assumes xx': "[x = x'] (mod n)" and yy': "[y = y'] (mod n)"
  and yx: "y <= x" and yx': "y' <= x'"
  shows "[x - y = x' - y'] (mod n)"
proof-
  { fix x a x' a' y b y' b'
    have "(x::nat) + a = x' + a' \<Longrightarrow> y + b = y' + b' \<Longrightarrow> y <= x \<Longrightarrow> y' <= x'
      \<Longrightarrow> (x - y) + (a + b') = (x' - y') + (a' + b)" by arith}
  note th = this
  from xx' yy' obtain q1 q2 q1' q2' where q12: "x + n*q1 = x'+n*q2"
    and q12': "y + n*q1' = y'+n*q2'" unfolding nat_mod by blast+
  from th[OF q12 q12' yx yx']
  have "(x - y) + n*(q1 + q2') = (x' - y') + n*(q2 + q1')"
    by (simp add: distrib_left)
  thus ?thesis unfolding nat_mod by blast
qed

lemma cong_mult_lcancel_eq: assumes an: "coprime a n"
  shows "[a * x = a * y] (mod n) \<longleftrightarrow> [x = y] (mod n)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume H: "?rhs" from cong_mult[OF cong_refl[of a n] H] show ?lhs .
next
  assume H: "?lhs" hence H': "[x*a = y*a] (mod n)" by (simp add: mult_commute)
  from cong_mult_rcancel[OF an H'] show ?rhs  .
qed

lemma cong_mult_rcancel_eq: assumes an: "coprime a n"
  shows "[x * a = y * a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
using cong_mult_lcancel_eq[OF an, of x y] by (simp add: mult_commute)

lemma cong_add_lcancel_eq: "[a + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: nat_mod)

lemma cong_add_rcancel_eq: "[x + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: nat_mod)

lemma cong_add_rcancel: "[x + a = y + a] (mod n) \<Longrightarrow> [x = y] (mod n)"
  by (simp add: nat_mod)

lemma cong_add_lcancel: "[a + x = a + y] (mod n) \<Longrightarrow> [x = y] (mod n)"
  by (simp add: nat_mod)

lemma cong_add_lcancel_eq_0: "[a + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by (simp add: nat_mod)

lemma cong_add_rcancel_eq_0: "[x + a = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by (simp add: nat_mod)

lemma cong_imp_eq: assumes xn: "x < n" and yn: "y < n" and xy: "[x = y] (mod n)"
  shows "x = y"
  using xy[unfolded modeq_def mod_less[OF xn] mod_less[OF yn]] .

lemma cong_divides_modulus: "[x = y] (mod m) \<Longrightarrow> n dvd m ==> [x = y] (mod n)"
  apply (auto simp add: nat_mod dvd_def)
  apply (rule_tac x="k*q1" in exI)
  apply (rule_tac x="k*q2" in exI)
  by simp

lemma cong_0_divides: "[x = 0] (mod n) \<longleftrightarrow> n dvd x" by simp

lemma cong_1_divides:"[x = 1] (mod n) ==> n dvd x - 1"
  apply (cases "x\<le>1", simp_all)
  using cong_sub_cases[of x 1 n] by auto

lemma cong_divides: "[x = y] (mod n) \<Longrightarrow> n dvd x \<longleftrightarrow> n dvd y"
apply (auto simp add: nat_mod dvd_def)
apply (rule_tac x="k + q1 - q2" in exI, simp add: add_mult_distrib2 diff_mult_distrib2)
apply (rule_tac x="k + q2 - q1" in exI, simp add: add_mult_distrib2 diff_mult_distrib2)
done

lemma cong_coprime: assumes xy: "[x = y] (mod n)"
  shows "coprime n x \<longleftrightarrow> coprime n y"
proof-
  {assume "n=0" hence ?thesis using xy by simp}
  moreover
  {assume nz: "n \<noteq> 0"
  have "coprime n x \<longleftrightarrow> coprime (x mod n) n"
    by (simp add: coprime_mod[OF nz, of x] coprime_commute[of n x])
  also have "\<dots> \<longleftrightarrow> coprime (y mod n) n" using xy[unfolded modeq_def] by simp
  also have "\<dots> \<longleftrightarrow> coprime y n" by (simp add: coprime_mod[OF nz, of y])
  finally have ?thesis by (simp add: coprime_commute) }
ultimately show ?thesis by blast
qed

lemma cong_mod: "~(n = 0) \<Longrightarrow> [a mod n = a] (mod n)" by (simp add: modeq_def)

lemma mod_mult_cong: "~(a = 0) \<Longrightarrow> ~(b = 0)
  \<Longrightarrow> [x mod (a * b) = y] (mod a) \<longleftrightarrow> [x = y] (mod a)"
  by (simp add: modeq_def mod_mult2_eq mod_add_left_eq)

lemma cong_mod_mult: "[x = y] (mod n) \<Longrightarrow> m dvd n \<Longrightarrow> [x = y] (mod m)"
  apply (auto simp add: nat_mod dvd_def)
  apply (rule_tac x="k*q1" in exI)
  apply (rule_tac x="k*q2" in exI, simp)
  done

(* Some things when we know more about the order.                            *)

lemma cong_le: "y <= x \<Longrightarrow> [x = y] (mod n) \<longleftrightarrow> (\<exists>q. x = q * n + y)"
  using nat_mod_lemma[of x y n]
  apply auto
  apply (simp add: nat_mod)
  apply (rule_tac x="q" in exI)
  apply (rule_tac x="q + q" in exI)
  by (auto simp: algebra_simps)

lemma cong_to_1: "[a = 1] (mod n) \<longleftrightarrow> a = 0 \<and> n = 1 \<or> (\<exists>m. a = 1 + m * n)"
proof-
  {assume "n = 0 \<or> n = 1\<or> a = 0 \<or> a = 1" hence ?thesis
      apply (cases "n=0", simp_all add: cong_commute)
      apply (cases "n=1", simp_all add: cong_commute modeq_def)
      apply arith
      apply (cases "a=1")
      apply (simp_all add: modeq_def cong_commute)
      done }
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1" and a:"a\<noteq>0" "a \<noteq> 1" hence a': "a \<ge> 1" by simp
    hence ?thesis using cong_le[OF a', of n] by auto }
  ultimately show ?thesis by auto
qed

(* Some basic theorems about solving congruences.                            *)


lemma cong_solve: assumes an: "coprime a n" shows "\<exists>x. [a * x = b] (mod n)"
proof-
  {assume "a=0" hence ?thesis using an by (simp add: modeq_def)}
  moreover
  {assume az: "a\<noteq>0"
  from bezout_add_strong[OF az, of n]
  obtain d x y where dxy: "d dvd a" "d dvd n" "a*x = n*y + d" by blast
  from an[unfolded coprime, rule_format, of d] dxy(1,2) have d1: "d = 1" by blast
  hence "a*x*b = (n*y + 1)*b" using dxy(3) by simp
  hence "a*(x*b) = n*(y*b) + b" by algebra
  hence "a*(x*b) mod n = (n*(y*b) + b) mod n" by simp
  hence "a*(x*b) mod n = b mod n" by (simp add: mod_add_left_eq)
  hence "[a*(x*b) = b] (mod n)" unfolding modeq_def .
  hence ?thesis by blast}
ultimately  show ?thesis by blast
qed

lemma cong_solve_unique: assumes an: "coprime a n" and nz: "n \<noteq> 0"
  shows "\<exists>!x. x < n \<and> [a * x = b] (mod n)"
proof-
  let ?P = "\<lambda>x. x < n \<and> [a * x = b] (mod n)"
  from cong_solve[OF an] obtain x where x: "[a*x = b] (mod n)" by blast
  let ?x = "x mod n"
  from x have th: "[a * ?x = b] (mod n)"
    by (simp add: modeq_def mod_mult_right_eq[of a x n])
  from mod_less_divisor[ of n x] nz th have Px: "?P ?x" by simp
  {fix y assume Py: "y < n" "[a * y = b] (mod n)"
    from Py(2) th have "[a * y = a*?x] (mod n)" by (simp add: modeq_def)
    hence "[y = ?x] (mod n)" by (simp add: cong_mult_lcancel_eq[OF an])
    with mod_less[OF Py(1)] mod_less_divisor[ of n x] nz
    have "y = ?x" by (simp add: modeq_def)}
  with Px show ?thesis by blast
qed

lemma cong_solve_unique_nontrivial:
  assumes p: "prime p" and pa: "coprime p a" and x0: "0 < x" and xp: "x < p"
  shows "\<exists>!y. 0 < y \<and> y < p \<and> [x * y = a] (mod p)"
proof-
  from p have p1: "p > 1" using prime_ge_2[OF p] by arith
  hence p01: "p \<noteq> 0" "p \<noteq> 1" by arith+
  from pa have ap: "coprime a p" by (simp add: coprime_commute)
  from prime_coprime[OF p, of x] dvd_imp_le[of p x] x0 xp have px:"coprime x p"
    by (auto simp add: coprime_commute)
  from cong_solve_unique[OF px p01(1)]
  obtain y where y: "y < p" "[x * y = a] (mod p)" "\<forall>z. z < p \<and> [x * z = a] (mod p) \<longrightarrow> z = y" by blast
  {assume y0: "y = 0"
    with y(2) have th: "p dvd a" by (simp add: cong_commute[of 0 a p])
    with p coprime_prime[OF pa, of p] have False by simp}
  with y show ?thesis unfolding Ex1_def using neq0_conv by blast
qed
lemma cong_unique_inverse_prime:
  assumes p: "prime p" and x0: "0 < x" and xp: "x < p"
  shows "\<exists>!y. 0 < y \<and> y < p \<and> [x * y = 1] (mod p)"
  using cong_solve_unique_nontrivial[OF p coprime_1[of p] x0 xp] .

(* Forms of the Chinese remainder theorem.                                   *)

lemma cong_chinese:
  assumes ab: "coprime a b" and  xya: "[x = y] (mod a)"
  and xyb: "[x = y] (mod b)"
  shows "[x = y] (mod a*b)"
  using ab xya xyb
  by (simp add: cong_sub_cases[of x y a] cong_sub_cases[of x y b]
    cong_sub_cases[of x y "a*b"])
(cases "x \<le> y", simp_all add: divides_mul[of a _ b])

lemma chinese_remainder_unique:
  assumes ab: "coprime a b" and az: "a \<noteq> 0" and bz: "b\<noteq>0"
  shows "\<exists>!x. x < a * b \<and> [x = m] (mod a) \<and> [x = n] (mod b)"
proof-
  from az bz have abpos: "a*b > 0" by simp
  from chinese_remainder[OF ab az bz] obtain x q1 q2 where
    xq12: "x = m + q1 * a" "x = n + q2 * b" by blast
  let ?w = "x mod (a*b)"
  have wab: "?w < a*b" by (simp add: mod_less_divisor[OF abpos])
  from xq12(1) have "?w mod a = ((m + q1 * a) mod (a*b)) mod a" by simp
  also have "\<dots> = m mod a" apply (simp add: mod_mult2_eq)
    apply (subst mod_add_left_eq)
    by simp
  finally have th1: "[?w = m] (mod a)" by (simp add: modeq_def)
  from xq12(2) have "?w mod b = ((n + q2 * b) mod (a*b)) mod b" by simp
  also have "\<dots> = ((n + q2 * b) mod (b*a)) mod b" by (simp add: mult_commute)
  also have "\<dots> = n mod b" apply (simp add: mod_mult2_eq)
    apply (subst mod_add_left_eq)
    by simp
  finally have th2: "[?w = n] (mod b)" by (simp add: modeq_def)
  {fix y assume H: "y < a*b" "[y = m] (mod a)" "[y = n] (mod b)"
    with th1 th2 have H': "[y = ?w] (mod a)" "[y = ?w] (mod b)"
      by (simp_all add: modeq_def)
    from cong_chinese[OF ab H'] mod_less[OF H(1)] mod_less[OF wab]
    have "y = ?w" by (simp add: modeq_def)}
  with th1 th2 wab show ?thesis by blast
qed

lemma chinese_remainder_coprime_unique:
  assumes ab: "coprime a b" and az: "a \<noteq> 0" and bz: "b \<noteq> 0"
  and ma: "coprime m a" and nb: "coprime n b"
  shows "\<exists>!x. coprime x (a * b) \<and> x < a * b \<and> [x = m] (mod a) \<and> [x = n] (mod b)"
proof-
  let ?P = "\<lambda>x. x < a * b \<and> [x = m] (mod a) \<and> [x = n] (mod b)"
  from chinese_remainder_unique[OF ab az bz]
  obtain x where x: "x < a * b" "[x = m] (mod a)" "[x = n] (mod b)"
    "\<forall>y. ?P y \<longrightarrow> y = x" by blast
  from ma nb cong_coprime[OF x(2)] cong_coprime[OF x(3)]
  have "coprime x a" "coprime x b" by (simp_all add: coprime_commute)
  with coprime_mul[of x a b] have "coprime x (a*b)" by simp
  with x show ?thesis by blast
qed

(* Euler totient function.                                                   *)

definition phi_def: "\<phi> n = card { m. 0 < m \<and> m <= n \<and> coprime m n }"

lemma phi_0[simp]: "\<phi> 0 = 0"
  unfolding phi_def by auto

lemma phi_finite[simp]: "finite ({ m. 0 < m \<and> m <= n \<and> coprime m n })"
proof-
  have "{ m. 0 < m \<and> m <= n \<and> coprime m n } \<subseteq> {0..n}" by auto
  thus ?thesis by (auto intro: finite_subset)
qed

declare coprime_1[presburger]
lemma phi_1[simp]: "\<phi> 1 = 1"
proof-
  {fix m
    have "0 < m \<and> m <= 1 \<and> coprime m 1 \<longleftrightarrow> m = 1" by presburger }
  thus ?thesis by (simp add: phi_def)
qed

lemma [simp]: "\<phi> (Suc 0) = Suc 0" using phi_1 by simp

lemma phi_alt: "\<phi>(n) = card { m. coprime m n \<and> m < n}"
proof-
  {assume "n=0 \<or> n=1" hence ?thesis by (cases "n=0", simp_all)}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    {fix m
      from n have "0 < m \<and> m <= n \<and> coprime m n \<longleftrightarrow> coprime m n \<and> m < n"
        apply (cases "m = 0", simp_all)
        apply (cases "m = 1", simp_all)
        apply (cases "m = n", auto)
        done }
    hence ?thesis unfolding phi_def by simp}
  ultimately show ?thesis by auto
qed

lemma phi_finite_lemma[simp]: "finite {m. coprime m n \<and>  m < n}" (is "finite ?S")
  by (rule finite_subset[of "?S" "{0..n}"], auto)

lemma phi_another: assumes n: "n\<noteq>1"
  shows "\<phi> n = card {m. 0 < m \<and> m < n \<and> coprime m n }"
proof-
  {fix m
    from n have "0 < m \<and> m < n \<and> coprime m n \<longleftrightarrow> coprime m n \<and> m < n"
      by (cases "m=0", auto)}
  thus ?thesis unfolding phi_alt by auto
qed

lemma phi_limit: "\<phi> n \<le> n"
proof-
  have "{ m. coprime m n \<and> m < n} \<subseteq> {0 ..<n}" by auto
  with card_mono[of "{0 ..<n}" "{ m. coprime m n \<and> m < n}"]
  show ?thesis unfolding phi_alt by auto
qed

lemma stupid[simp]: "{m. (0::nat) < m \<and> m < n} = {1..<n}"
  by auto

lemma phi_limit_strong: assumes n: "n\<noteq>1"
  shows "\<phi>(n) \<le> n - 1"
proof-
  show ?thesis
    unfolding phi_another[OF n] finite_number_segment[of n, symmetric]
    by (rule card_mono[of "{m. 0 < m \<and> m < n}" "{m. 0 < m \<and> m < n \<and> coprime m n}"], auto)
qed

lemma phi_lowerbound_1_strong: assumes n: "n \<ge> 1"
  shows "\<phi>(n) \<ge> 1"
proof-
  let ?S = "{ m. 0 < m \<and> m <= n \<and> coprime m n }"
  from card_0_eq[of ?S] n have "\<phi> n \<noteq> 0" unfolding phi_alt
    apply auto
    apply (cases "n=1", simp_all)
    apply (rule exI[where x=1], simp)
    done
  thus ?thesis by arith
qed

lemma phi_lowerbound_1: "2 <= n ==> 1 <= \<phi>(n)"
  using phi_lowerbound_1_strong[of n] by auto

lemma phi_lowerbound_2: assumes n: "3 <= n" shows "2 <= \<phi> (n)"
proof-
  let ?S = "{ m. 0 < m \<and> m <= n \<and> coprime m n }"
  have inS: "{1, n - 1} \<subseteq> ?S" using n coprime_plus1[of "n - 1"]
    by (auto simp add: coprime_commute)
  from n have c2: "card {1, n - 1} = 2" by (auto simp add: card_insert_if)
  from card_mono[of ?S "{1, n - 1}", simplified inS c2] show ?thesis
    unfolding phi_def by auto
qed

lemma phi_prime: "\<phi> n = n - 1 \<and> n\<noteq>0 \<and> n\<noteq>1 \<longleftrightarrow> prime n"
proof-
  {assume "n=0 \<or> n=1" hence ?thesis by (cases "n=1", simp_all)}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    let ?S = "{m. 0 < m \<and> m < n}"
    have fS: "finite ?S" by simp
    let ?S' = "{m. 0 < m \<and> m < n \<and> coprime m n}"
    have fS':"finite ?S'" apply (rule finite_subset[of ?S' ?S]) by auto
    {assume H: "\<phi> n = n - 1 \<and> n\<noteq>0 \<and> n\<noteq>1"
      hence ceq: "card ?S' = card ?S"
      using n finite_number_segment[of n] phi_another[OF n(2)] by simp
      {fix m assume m: "0 < m" "m < n" "\<not> coprime m n"
        hence mS': "m \<notin> ?S'" by auto
        have "insert m ?S' \<le> ?S" using m by auto
        from m have "card (insert m ?S') \<le> card ?S"
          by - (rule card_mono[of ?S "insert m ?S'"], auto)
        hence False
          unfolding card_insert_disjoint[of "?S'" m, OF fS' mS'] ceq
          by simp }
      hence "\<forall>m. 0 <m \<and> m < n \<longrightarrow> coprime m n" by blast
      hence "prime n" unfolding prime using n by (simp add: coprime_commute)}
    moreover
    {assume H: "prime n"
      hence "?S = ?S'" unfolding prime using n
        by (auto simp add: coprime_commute)
      hence "card ?S = card ?S'" by simp
      hence "\<phi> n = n - 1" unfolding phi_another[OF n(2)] by simp}
    ultimately have ?thesis using n by blast}
  ultimately show ?thesis by (cases "n=0") blast+
qed

(* Multiplicativity property.                                                *)

lemma phi_multiplicative: assumes ab: "coprime a b"
  shows "\<phi> (a * b) = \<phi> a * \<phi> b"
proof-
  {assume "a = 0 \<or> b = 0 \<or> a = 1 \<or> b = 1"
    hence ?thesis
      by (cases "a=0", simp, cases "b=0", simp, cases"a=1", simp_all) }
  moreover
  {assume a: "a\<noteq>0" "a\<noteq>1" and b: "b\<noteq>0" "b\<noteq>1"
    hence ab0: "a*b \<noteq> 0" by simp
    let ?S = "\<lambda>k. {m. coprime m k \<and> m < k}"
    let ?f = "\<lambda>x. (x mod a, x mod b)"
    have eq: "?f ` (?S (a*b)) = (?S a \<times> ?S b)"
    proof-
      {fix x assume x:"x \<in> ?S (a*b)"
        hence x': "coprime x (a*b)" "x < a*b" by simp_all
        hence xab: "coprime x a" "coprime x b" by (simp_all add: coprime_mul_eq)
        from mod_less_divisor a b have xab':"x mod a < a" "x mod b < b" by auto
        from xab xab' have "?f x \<in> (?S a \<times> ?S b)"
          by (simp add: coprime_mod[OF a(1)] coprime_mod[OF b(1)])}
      moreover
      {fix x y assume x: "x \<in> ?S a" and y: "y \<in> ?S b"
        hence x': "coprime x a" "x < a" and y': "coprime y b" "y < b" by simp_all
        from chinese_remainder_coprime_unique[OF ab a(1) b(1) x'(1) y'(1)]
        obtain z where z: "coprime z (a * b)" "z < a * b" "[z = x] (mod a)"
          "[z = y] (mod b)" by blast
        hence "(x,y) \<in> ?f ` (?S (a*b))"
          using y'(2) mod_less_divisor[of b y] x'(2) mod_less_divisor[of a x]
          by (auto simp add: image_iff modeq_def)}
      ultimately show ?thesis by auto
    qed
    have finj: "inj_on ?f (?S (a*b))"
      unfolding inj_on_def
    proof(clarify)
      fix x y assume H: "coprime x (a * b)" "x < a * b" "coprime y (a * b)"
        "y < a * b" "x mod a = y mod a" "x mod b = y mod b"
      hence cp: "coprime x a" "coprime x b" "coprime y a" "coprime y b"
        by (simp_all add: coprime_mul_eq)
      from chinese_remainder_coprime_unique[OF ab a(1) b(1) cp(3,4)] H
      show "x = y" unfolding modeq_def by blast
    qed
    from card_image[OF finj, unfolded eq] have ?thesis
      unfolding phi_alt by simp }
  ultimately show ?thesis by auto
qed

(* Fermat's Little theorem / Fermat-Euler theorem.                           *)


lemma nproduct_mod:
  assumes fS: "finite S" and n0: "n \<noteq> 0"
  shows "[setprod (\<lambda>m. a(m) mod n) S = setprod a S] (mod n)"
proof-
  have th1:"[1 = 1] (mod n)" by (simp add: modeq_def)
  from cong_mult
  have th3:"\<forall>x1 y1 x2 y2.
    [x1 = x2] (mod n) \<and> [y1 = y2] (mod n) \<longrightarrow> [x1 * y1 = x2 * y2] (mod n)"
    by blast
  have th4:"\<forall>x\<in>S. [a x mod n = a x] (mod n)" by (simp add: modeq_def)
  from fold_image_related[where h="(\<lambda>m. a(m) mod n)" and g=a, OF th1 th3 fS, OF th4] show ?thesis unfolding setprod_def by (simp add: fS)
qed

lemma nproduct_cmul:
  assumes fS:"finite S"
  shows "setprod (\<lambda>m. (c::'a::{comm_monoid_mult})* a(m)) S = c ^ (card S) * setprod a S"
unfolding setprod_timesf setprod_constant[OF fS, of c] ..

lemma coprime_nproduct:
  assumes fS: "finite S" and Sn: "\<forall>x\<in>S. coprime n (a x)"
  shows "coprime n (setprod a S)"
  using fS unfolding setprod_def by (rule finite_subset_induct)
    (insert Sn, auto simp add: coprime_mul)

lemma fermat_little: assumes an: "coprime a n"
  shows "[a ^ (\<phi> n) = 1] (mod n)"
proof-
  {assume "n=0" hence ?thesis by simp}
  moreover
  {assume "n=1" hence ?thesis by (simp add: modeq_def)}
  moreover
  {assume nz: "n \<noteq> 0" and n1: "n \<noteq> 1"
    let ?S = "{m. coprime m n \<and> m < n}"
    let ?P = "\<Prod> ?S"
    have fS: "finite ?S" by simp
    have cardfS: "\<phi> n = card ?S" unfolding phi_alt ..
    {fix m assume m: "m \<in> ?S"
      hence "coprime m n" by simp
      with coprime_mul[of n a m] an have "coprime (a*m) n"
        by (simp add: coprime_commute)}
    hence Sn: "\<forall>m\<in> ?S. coprime (a*m) n " by blast
    from coprime_nproduct[OF fS, of n "\<lambda>m. m"] have nP:"coprime ?P n"
      by (simp add: coprime_commute)
    have Paphi: "[?P*a^ (\<phi> n) = ?P*1] (mod n)"
    proof-
      let ?h = "\<lambda>m. m mod n"
      {fix m assume mS: "m\<in> ?S"
        hence "?h m \<in> ?S" by simp}
      hence hS: "?h ` ?S = ?S"by (auto simp add: image_iff)
      have "a\<noteq>0" using an n1 nz apply- apply (rule ccontr) by simp
      hence inj: "inj_on (op * a) ?S" unfolding inj_on_def by simp

      have eq0: "fold_image op * (?h \<circ> op * a) 1 {m. coprime m n \<and> m < n} =
     fold_image op * (\<lambda>m. m) 1 {m. coprime m n \<and> m < n}"
      proof (rule fold_image_eq_general[where h="?h o (op * a)"])
        show "finite ?S" using fS .
      next
        {fix y assume yS: "y \<in> ?S" hence y: "coprime y n" "y < n" by simp_all
          from cong_solve_unique[OF an nz, of y]
          obtain x where x:"x < n" "[a * x = y] (mod n)" "\<forall>z. z < n \<and> [a * z = y] (mod n) \<longrightarrow> z=x" by blast
          from cong_coprime[OF x(2)] y(1)
          have xm: "coprime x n" by (simp add: coprime_mul_eq coprime_commute)
          {fix z assume "z \<in> ?S" "(?h \<circ> op * a) z = y"
            hence z: "coprime z n" "z < n" "(?h \<circ> op * a) z = y" by simp_all
            from x(3)[rule_format, of z] z(2,3) have "z=x"
              unfolding modeq_def mod_less[OF y(2)] by simp}
          with xm x(1,2) have "\<exists>!x. x \<in> ?S \<and> (?h \<circ> op * a) x = y"
            unfolding modeq_def mod_less[OF y(2)] by auto }
        thus "\<forall>y\<in>{m. coprime m n \<and> m < n}.
       \<exists>!x. x \<in> {m. coprime m n \<and> m < n} \<and> ((\<lambda>m. m mod n) \<circ> op * a) x = y" by blast
      next
        {fix x assume xS: "x\<in> ?S"
          hence x: "coprime x n" "x < n" by simp_all
          with an have "coprime (a*x) n"
            by (simp add: coprime_mul_eq[of n a x] coprime_commute)
          hence "?h (a*x) \<in> ?S" using nz
            by (simp add: coprime_mod[OF nz])}
        thus " \<forall>x\<in>{m. coprime m n \<and> m < n}.
       ((\<lambda>m. m mod n) \<circ> op * a) x \<in> {m. coprime m n \<and> m < n} \<and>
       ((\<lambda>m. m mod n) \<circ> op * a) x = ((\<lambda>m. m mod n) \<circ> op * a) x" by simp
      qed
      from nproduct_mod[OF fS nz, of "op * a"]
      have "[(setprod (op *a) ?S) = (setprod (?h o (op * a)) ?S)] (mod n)"
        unfolding o_def
        by (simp add: cong_commute)
      also have "[setprod (?h o (op * a)) ?S = ?P ] (mod n)"
        using eq0 fS an by (simp add: setprod_def modeq_def o_def)
      finally show "[?P*a^ (\<phi> n) = ?P*1] (mod n)"
        unfolding cardfS mult_commute[of ?P "a^ (card ?S)"]
          nproduct_cmul[OF fS, symmetric] mult_1_right by simp
    qed
    from cong_mult_lcancel[OF nP Paphi] have ?thesis . }
  ultimately show ?thesis by blast
qed

lemma fermat_little_prime: assumes p: "prime p" and ap: "coprime a p"
  shows "[a^ (p - 1) = 1] (mod p)"
  using fermat_little[OF ap] p[unfolded phi_prime[symmetric]]
by simp


(* Lucas's theorem.                                                          *)

lemma lucas_coprime_lemma:
  assumes m: "m\<noteq>0" and am: "[a^m = 1] (mod n)"
  shows "coprime a n"
proof-
  {assume "n=1" hence ?thesis by simp}
  moreover
  {assume "n = 0" hence ?thesis using am m exp_eq_1[of a m] by simp}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    from m obtain m' where m': "m = Suc m'" by (cases m, blast+)
    {fix d
      assume d: "d dvd a" "d dvd n"
      from n have n1: "1 < n" by arith
      from am mod_less[OF n1] have am1: "a^m mod n = 1" unfolding modeq_def by simp
      from dvd_mult2[OF d(1), of "a^m'"] have dam:"d dvd a^m" by (simp add: m')
      from dvd_mod_iff[OF d(2), of "a^m"] dam am1
      have "d = 1" by simp }
    hence ?thesis unfolding coprime by auto
  }
  ultimately show ?thesis by blast
qed

lemma lucas_weak:
  assumes n: "n \<ge> 2" and an:"[a^(n - 1) = 1] (mod n)"
  and nm: "\<forall>m. 0 <m \<and> m < n - 1 \<longrightarrow> \<not> [a^m = 1] (mod n)"
  shows "prime n"
proof-
  from n have n1: "n \<noteq> 1" "n\<noteq>0" "n - 1 \<noteq> 0" "n - 1 > 0" "n - 1 < n" by arith+
  from lucas_coprime_lemma[OF n1(3) an] have can: "coprime a n" .
  from fermat_little[OF can] have afn: "[a ^ \<phi> n = 1] (mod n)" .
  {assume "\<phi> n \<noteq> n - 1"
    with phi_limit_strong[OF n1(1)] phi_lowerbound_1[OF n]
    have c:"\<phi> n > 0 \<and> \<phi> n < n - 1" by arith
    from nm[rule_format, OF c] afn have False ..}
  hence "\<phi> n = n - 1" by blast
  with phi_prime[of n] n1(1,2) show ?thesis by simp
qed

lemma nat_exists_least_iff: "(\<exists>(n::nat). P n) \<longleftrightarrow> (\<exists>n. P n \<and> (\<forall>m < n. \<not> P m))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs thus ?lhs by blast
next
  assume H: ?lhs then obtain n where n: "P n" by blast
  let ?x = "Least P"
  {fix m assume m: "m < ?x"
    from not_less_Least[OF m] have "\<not> P m" .}
  with LeastI_ex[OF H] show ?rhs by blast
qed

lemma nat_exists_least_iff': "(\<exists>(n::nat). P n) \<longleftrightarrow> (P (Least P) \<and> (\<forall>m < (Least P). \<not> P m))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume ?rhs hence ?lhs by blast}
  moreover
  { assume H: ?lhs then obtain n where n: "P n" by blast
    let ?x = "Least P"
    {fix m assume m: "m < ?x"
      from not_less_Least[OF m] have "\<not> P m" .}
    with LeastI_ex[OF H] have ?rhs by blast}
  ultimately show ?thesis by blast
qed

lemma power_mod: "((x::nat) mod m)^n mod m = x^n mod m"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "(x mod m)^(Suc n) mod m = ((x mod m) * (((x mod m) ^ n) mod m)) mod m"
    by (simp add: mod_mult_right_eq[symmetric])
  also have "\<dots> = ((x mod m) * (x^n mod m)) mod m" using Suc.hyps by simp
  also have "\<dots> = x^(Suc n) mod m"
    by (simp add: mod_mult_left_eq[symmetric] mod_mult_right_eq[symmetric])
  finally show ?case .
qed

lemma lucas:
  assumes n2: "n \<ge> 2" and an1: "[a^(n - 1) = 1] (mod n)"
  and pn: "\<forall>p. prime p \<and> p dvd n - 1 \<longrightarrow> \<not> [a^((n - 1) div p) = 1] (mod n)"
  shows "prime n"
proof-
  from n2 have n01: "n\<noteq>0" "n\<noteq>1" "n - 1 \<noteq> 0" by arith+
  from mod_less_divisor[of n 1] n01 have onen: "1 mod n = 1" by simp
  from lucas_coprime_lemma[OF n01(3) an1] cong_coprime[OF an1]
  have an: "coprime a n" "coprime (a^(n - 1)) n" by (simp_all add: coprime_commute)
  {assume H0: "\<exists>m. 0 < m \<and> m < n - 1 \<and> [a ^ m = 1] (mod n)" (is "EX m. ?P m")
    from H0[unfolded nat_exists_least_iff[of ?P]] obtain m where
      m: "0 < m" "m < n - 1" "[a ^ m = 1] (mod n)" "\<forall>k <m. \<not>?P k" by blast
    {assume nm1: "(n - 1) mod m > 0"
      from mod_less_divisor[OF m(1)] have th0:"(n - 1) mod m < m" by blast
      let ?y = "a^ ((n - 1) div m * m)"
      note mdeq = mod_div_equality[of "(n - 1)" m]
      from coprime_exp[OF an(1)[unfolded coprime_commute[of a n]],
        of "(n - 1) div m * m"]
      have yn: "coprime ?y n" by (simp add: coprime_commute)
      have "?y mod n = (a^m)^((n - 1) div m) mod n"
        by (simp add: algebra_simps power_mult)
      also have "\<dots> = (a^m mod n)^((n - 1) div m) mod n"
        using power_mod[of "a^m" n "(n - 1) div m"] by simp
      also have "\<dots> = 1" using m(3)[unfolded modeq_def onen] onen
        by (simp add: power_Suc0)
      finally have th3: "?y mod n = 1"  .
      have th2: "[?y * a ^ ((n - 1) mod m) = ?y* 1] (mod n)"
        using an1[unfolded modeq_def onen] onen
          mod_div_equality[of "(n - 1)" m, symmetric]
        by (simp add:power_add[symmetric] modeq_def th3 del: One_nat_def)
      from cong_mult_lcancel[of ?y n "a^((n - 1) mod m)" 1, OF yn th2]
      have th1: "[a ^ ((n - 1) mod m) = 1] (mod n)"  .
      from m(4)[rule_format, OF th0] nm1
        less_trans[OF mod_less_divisor[OF m(1), of "n - 1"] m(2)] th1
      have False by blast }
    hence "(n - 1) mod m = 0" by auto
    then have mn: "m dvd n - 1" by presburger
    then obtain r where r: "n - 1 = m*r" unfolding dvd_def by blast
    from n01 r m(2) have r01: "r\<noteq>0" "r\<noteq>1" by - (rule ccontr, simp)+
    from prime_factor[OF r01(2)] obtain p where p: "prime p" "p dvd r" by blast
    hence th: "prime p \<and> p dvd n - 1" unfolding r by (auto intro: dvd_mult)
    have "(a ^ ((n - 1) div p)) mod n = (a^(m*r div p)) mod n" using r
      by (simp add: power_mult)
    also have "\<dots> = (a^(m*(r div p))) mod n" using div_mult1_eq[of m r p] p(2)[unfolded dvd_eq_mod_eq_0] by simp
    also have "\<dots> = ((a^m)^(r div p)) mod n" by (simp add: power_mult)
    also have "\<dots> = ((a^m mod n)^(r div p)) mod n" using power_mod[of "a^m" "n" "r div p" ] ..
    also have "\<dots> = 1" using m(3) onen by (simp add: modeq_def power_Suc0)
    finally have "[(a ^ ((n - 1) div p))= 1] (mod n)"
      using onen by (simp add: modeq_def)
    with pn[rule_format, OF th] have False by blast}
  hence th: "\<forall>m. 0 < m \<and> m < n - 1 \<longrightarrow> \<not> [a ^ m = 1] (mod n)" by blast
  from lucas_weak[OF n2 an1 th] show ?thesis .
qed

(* Definition of the order of a number mod n (0 in non-coprime case).        *)

definition "ord n a = (if coprime n a then Least (\<lambda>d. d > 0 \<and> [a ^d = 1] (mod n)) else 0)"

(* This has the expected properties.                                         *)

lemma coprime_ord:
  assumes na: "coprime n a"
  shows "ord n a > 0 \<and> [a ^(ord n a) = 1] (mod n) \<and> (\<forall>m. 0 < m \<and> m < ord n a \<longrightarrow> \<not> [a^ m = 1] (mod n))"
proof-
  let ?P = "\<lambda>d. 0 < d \<and> [a ^ d = 1] (mod n)"
  from euclid[of a] obtain p where p: "prime p" "a < p" by blast
  from na have o: "ord n a = Least ?P" by (simp add: ord_def)
  {assume "n=0 \<or> n=1" with na have "\<exists>m>0. ?P m" apply auto apply (rule exI[where x=1]) by (simp  add: modeq_def)}
  moreover
  {assume "n\<noteq>0 \<and> n\<noteq>1" hence n2:"n \<ge> 2" by arith
    from na have na': "coprime a n" by (simp add: coprime_commute)
    from phi_lowerbound_1[OF n2] fermat_little[OF na']
    have ex: "\<exists>m>0. ?P m" by - (rule exI[where x="\<phi> n"], auto) }
  ultimately have ex: "\<exists>m>0. ?P m" by blast
  from nat_exists_least_iff'[of ?P] ex na show ?thesis
    unfolding o[symmetric] by auto
qed
(* With the special value 0 for non-coprime case, it's more convenient.      *)
lemma ord_works:
 "[a ^ (ord n a) = 1] (mod n) \<and> (\<forall>m. 0 < m \<and> m < ord n a \<longrightarrow> ~[a^ m = 1] (mod n))"
apply (cases "coprime n a")
using coprime_ord[of n a]
by (blast, simp add: ord_def modeq_def)

lemma ord: "[a^(ord n a) = 1] (mod n)" using ord_works by blast
lemma ord_minimal: "0 < m \<Longrightarrow> m < ord n a \<Longrightarrow> ~[a^m = 1] (mod n)"
  using ord_works by blast
lemma ord_eq_0: "ord n a = 0 \<longleftrightarrow> ~coprime n a"
by (cases "coprime n a", simp add: coprime_ord, simp add: ord_def)

lemma ord_divides:
 "[a ^ d = 1] (mod n) \<longleftrightarrow> ord n a dvd d" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume rh: ?rhs
  then obtain k where "d = ord n a * k" unfolding dvd_def by blast
  hence "[a ^ d = (a ^ (ord n a) mod n)^k] (mod n)"
    by (simp add : modeq_def power_mult power_mod)
  also have "[(a ^ (ord n a) mod n)^k = 1] (mod n)"
    using ord[of a n, unfolded modeq_def]
    by (simp add: modeq_def power_mod power_Suc0)
  finally  show ?lhs .
next
  assume lh: ?lhs
  { assume H: "\<not> coprime n a"
    hence o: "ord n a = 0" by (simp add: ord_def)
    {assume d: "d=0" with o H have ?rhs by (simp add: modeq_def)}
    moreover
    {assume d0: "d\<noteq>0" then obtain d' where d': "d = Suc d'" by (cases d, auto)
      from H[unfolded coprime]
      obtain p where p: "p dvd n" "p dvd a" "p \<noteq> 1" by auto
      from lh[unfolded nat_mod]
      obtain q1 q2 where q12:"a ^ d + n * q1 = 1 + n * q2" by blast
      hence "a ^ d + n * q1 - n * q2 = 1" by simp
      with dvd_diff_nat [OF dvd_add [OF divides_rexp[OF p(2), of d'] dvd_mult2[OF p(1), of q1]] dvd_mult2[OF p(1), of q2]] d' have "p dvd 1" by simp
      with p(3) have False by simp
      hence ?rhs ..}
    ultimately have ?rhs by blast}
  moreover
  {assume H: "coprime n a"
    let ?o = "ord n a"
    let ?q = "d div ord n a"
    let ?r = "d mod ord n a"
    from cong_exp[OF ord[of a n], of ?q]
    have eqo: "[(a^?o)^?q = 1] (mod n)"  by (simp add: modeq_def power_Suc0)
    from H have onz: "?o \<noteq> 0" by (simp add: ord_eq_0)
    hence op: "?o > 0" by simp
    from mod_div_equality[of d "ord n a"] lh
    have "[a^(?o*?q + ?r) = 1] (mod n)" by (simp add: modeq_def mult_commute)
    hence "[(a^?o)^?q * (a^?r) = 1] (mod n)"
      by (simp add: modeq_def power_mult[symmetric] power_add[symmetric])
    hence th: "[a^?r = 1] (mod n)"
      using eqo mod_mult_left_eq[of "(a^?o)^?q" "a^?r" n]
      apply (simp add: modeq_def del: One_nat_def)
      by (simp add: mod_mult_left_eq[symmetric])
    {assume r: "?r = 0" hence ?rhs by (simp add: dvd_eq_mod_eq_0)}
    moreover
    {assume r: "?r \<noteq> 0"
      with mod_less_divisor[OF op, of d] have r0o:"?r >0 \<and> ?r < ?o" by simp
      from conjunct2[OF ord_works[of a n], rule_format, OF r0o] th
      have ?rhs by blast}
    ultimately have ?rhs by blast}
  ultimately  show ?rhs by blast
qed

lemma order_divides_phi: "coprime n a \<Longrightarrow> ord n a dvd \<phi> n"
using ord_divides fermat_little coprime_commute by simp
lemma order_divides_expdiff:
  assumes na: "coprime n a"
  shows "[a^d = a^e] (mod n) \<longleftrightarrow> [d = e] (mod (ord n a))"
proof-
  {fix n a d e
    assume na: "coprime n a" and ed: "(e::nat) \<le> d"
    hence "\<exists>c. d = e + c" by arith
    then obtain c where c: "d = e + c" by arith
    from na have an: "coprime a n" by (simp add: coprime_commute)
    from coprime_exp[OF na, of e]
    have aen: "coprime (a^e) n" by (simp add: coprime_commute)
    from coprime_exp[OF na, of c]
    have acn: "coprime (a^c) n" by (simp add: coprime_commute)
    have "[a^d = a^e] (mod n) \<longleftrightarrow> [a^(e + c) = a^(e + 0)] (mod n)"
      using c by simp
    also have "\<dots> \<longleftrightarrow> [a^e* a^c = a^e *a^0] (mod n)" by (simp add: power_add)
    also have  "\<dots> \<longleftrightarrow> [a ^ c = 1] (mod n)"
      using cong_mult_lcancel_eq[OF aen, of "a^c" "a^0"] by simp
    also  have "\<dots> \<longleftrightarrow> ord n a dvd c" by (simp only: ord_divides)
    also have "\<dots> \<longleftrightarrow> [e + c = e + 0] (mod ord n a)"
      using cong_add_lcancel_eq[of e c 0 "ord n a", simplified cong_0_divides]
      by simp
    finally have "[a^d = a^e] (mod n) \<longleftrightarrow> [d = e] (mod (ord n a))"
      using c by simp }
  note th = this
  have "e \<le> d \<or> d \<le> e" by arith
  moreover
  {assume ed: "e \<le> d" from th[OF na ed] have ?thesis .}
  moreover
  {assume de: "d \<le> e"
    from th[OF na de] have ?thesis by (simp add: cong_commute) }
  ultimately show ?thesis by blast
qed

(* Another trivial primality characterization.                               *)

lemma prime_prime_factor:
  "prime n \<longleftrightarrow> n \<noteq> 1\<and> (\<forall>p. prime p \<and> p dvd n \<longrightarrow> p = n)"
proof-
  {assume n: "n=0 \<or> n=1" hence ?thesis using prime_0 two_is_prime by auto}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    {assume pn: "prime n"

      from pn[unfolded prime_def] have "\<forall>p. prime p \<and> p dvd n \<longrightarrow> p = n"
        using n
        apply (cases "n = 0 \<or> n=1",simp)
        by (clarsimp, erule_tac x="p" in allE, auto)}
    moreover
    {assume H: "\<forall>p. prime p \<and> p dvd n \<longrightarrow> p = n"
      from n have n1: "n > 1" by arith
      {fix m assume m: "m dvd n" "m\<noteq>1"
        from prime_factor[OF m(2)] obtain p where
          p: "prime p" "p dvd m" by blast
        from dvd_trans[OF p(2) m(1)] p(1) H have "p = n" by blast
        with p(2) have "n dvd m"  by simp
        hence "m=n"  using dvd_antisym[OF m(1)] by simp }
      with n1 have "prime n"  unfolding prime_def by auto }
    ultimately have ?thesis using n by blast}
  ultimately       show ?thesis by auto
qed

lemma prime_divisor_sqrt:
  "prime n \<longleftrightarrow> n \<noteq> 1 \<and> (\<forall>d. d dvd n \<and> d^2 \<le> n \<longrightarrow> d = 1)"
proof-
  {assume "n=0 \<or> n=1" hence ?thesis using prime_0 prime_1
    by (auto simp add: nat_power_eq_0_iff)}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    hence np: "n > 1" by arith
    {fix d assume d: "d dvd n" "d^2 \<le> n" and H: "\<forall>m. m dvd n \<longrightarrow> m=1 \<or> m=n"
      from H d have d1n: "d = 1 \<or> d=n" by blast
      {assume dn: "d=n"
        have "n^2 > n*1" using n by (simp add: power2_eq_square)
        with dn d(2) have "d=1" by simp}
      with d1n have "d = 1" by blast  }
    moreover
    {fix d assume d: "d dvd n" and H: "\<forall>d'. d' dvd n \<and> d'^2 \<le> n \<longrightarrow> d' = 1"
      from d n have "d \<noteq> 0" apply - apply (rule ccontr) by simp
      hence dp: "d > 0" by simp
      from d[unfolded dvd_def] obtain e where e: "n= d*e" by blast
      from n dp e have ep:"e > 0" by simp
      have "d^2 \<le> n \<or> e^2 \<le> n" using dp ep
        by (auto simp add: e power2_eq_square mult_le_cancel_left)
      moreover
      {assume h: "d^2 \<le> n"
        from H[rule_format, of d] h d have "d = 1" by blast}
      moreover
      {assume h: "e^2 \<le> n"
        from e have "e dvd n" unfolding dvd_def by (simp add: mult_commute)
        with H[rule_format, of e] h have "e=1" by simp
        with e have "d = n" by simp}
      ultimately have "d=1 \<or> d=n"  by blast}
    ultimately have ?thesis unfolding prime_def using np n(2) by blast}
  ultimately show ?thesis by auto
qed
lemma prime_prime_factor_sqrt:
  "prime n \<longleftrightarrow> n \<noteq> 0 \<and> n \<noteq> 1 \<and> \<not> (\<exists>p. prime p \<and> p dvd n \<and> p^2 \<le> n)"
  (is "?lhs \<longleftrightarrow>?rhs")
proof-
  {assume "n=0 \<or> n=1" hence ?thesis using prime_0 prime_1 by auto}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    {assume H: ?lhs
      from H[unfolded prime_divisor_sqrt] n
      have ?rhs
        apply clarsimp
        apply (erule_tac x="p" in allE)
        apply simp
        done
    }
    moreover
    {assume H: ?rhs
      {fix d assume d: "d dvd n" "d^2 \<le> n" "d\<noteq>1"
        from prime_factor[OF d(3)]
        obtain p where p: "prime p" "p dvd d" by blast
        from n have np: "n > 0" by arith
        from d(1) n have "d \<noteq> 0" by - (rule ccontr, auto)
        hence dp: "d > 0" by arith
        from mult_mono[OF dvd_imp_le[OF p(2) dp] dvd_imp_le[OF p(2) dp]] d(2)
        have "p^2 \<le> n" unfolding power2_eq_square by arith
        with H n p(1) dvd_trans[OF p(2) d(1)] have False  by blast}
      with n prime_divisor_sqrt  have ?lhs by auto}
    ultimately have ?thesis by blast }
  ultimately show ?thesis by (cases "n=0 \<or> n=1", auto)
qed
(* Pocklington theorem. *)

lemma pocklington_lemma:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q*r" and an: "[a^ (n - 1) = 1] (mod n)"
  and aq:"\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a^ ((n - 1) div p) - 1) n"
  and pp: "prime p" and pn: "p dvd n"
  shows "[p = 1] (mod q)"
proof-
  from pp prime_0 prime_1 have p01: "p \<noteq> 0" "p \<noteq> 1" by - (rule ccontr, simp)+
  from cong_1_divides[OF an, unfolded nqr, unfolded dvd_def]
  obtain k where k: "a ^ (q * r) - 1 = n*k" by blast
  from pn[unfolded dvd_def] obtain l where l: "n = p*l" by blast
  {assume a0: "a = 0"
    hence "a^ (n - 1) = 0" using n by (simp add: power_0_left)
    with n an mod_less[of 1 n]  have False by (simp add: power_0_left modeq_def)}
  hence a0: "a\<noteq>0" ..
  from n nqr have aqr0: "a ^ (q * r) \<noteq> 0" using a0 by simp
  hence "(a ^ (q * r) - 1) + 1  = a ^ (q * r)" by simp
  with k l have "a ^ (q * r) = p*l*k + 1" by simp
  hence "a ^ (r * q) + p * 0 = 1 + p * (l*k)" by (simp add: mult_ac)
  hence odq: "ord p (a^r) dvd q"
    unfolding ord_divides[symmetric] power_mult[symmetric] nat_mod  by blast
  from odq[unfolded dvd_def] obtain d where d: "q = ord p (a^r) * d" by blast
  {assume d1: "d \<noteq> 1"
    from prime_factor[OF d1] obtain P where P: "prime P" "P dvd d" by blast
    from d dvd_mult[OF P(2), of "ord p (a^r)"] have Pq: "P dvd q" by simp
    from aq P(1) Pq have caP:"coprime (a^ ((n - 1) div P) - 1) n" by blast
    from Pq obtain s where s: "q = P*s" unfolding dvd_def by blast
    have P0: "P \<noteq> 0" using P(1) prime_0 by - (rule ccontr, simp)
    from P(2) obtain t where t: "d = P*t" unfolding dvd_def by blast
    from d s t P0  have s': "ord p (a^r) * t = s" by algebra
    have "ord p (a^r) * t*r = r * ord p (a^r) * t" by algebra
    hence exps: "a^(ord p (a^r) * t*r) = ((a ^ r) ^ ord p (a^r)) ^ t"
      by (simp only: power_mult)
    have "[((a ^ r) ^ ord p (a^r)) ^ t= 1^t] (mod p)"
      by (rule cong_exp, rule ord)
    then have th: "[((a ^ r) ^ ord p (a^r)) ^ t= 1] (mod p)"
      by (simp add: power_Suc0)
    from cong_1_divides[OF th] exps have pd0: "p dvd a^(ord p (a^r) * t*r) - 1" by simp
    from nqr s s' have "(n - 1) div P = ord p (a^r) * t*r" using P0 by simp
    with caP have "coprime (a^(ord p (a^r) * t*r) - 1) n" by simp
    with p01 pn pd0 have False unfolding coprime by auto}
  hence d1: "d = 1" by blast
  hence o: "ord p (a^r) = q" using d by simp
  from pp phi_prime[of p] have phip: " \<phi> p = p - 1" by simp
  {fix d assume d: "d dvd p" "d dvd a" "d \<noteq> 1"
    from pp[unfolded prime_def] d have dp: "d = p" by blast
    from n have n12:"Suc (n - 2) = n - 1" by arith
    with divides_rexp[OF d(2)[unfolded dp], of "n - 2"]
    have th0: "p dvd a ^ (n - 1)" by simp
    from n have n0: "n \<noteq> 0" by simp
    from d(2) an n12[symmetric] have a0: "a \<noteq> 0"
      by - (rule ccontr, simp add: modeq_def)
    have th1: "a^ (n - 1) \<noteq> 0" using n d(2) dp a0 by auto
    from coprime_minus1[OF th1, unfolded coprime]
      dvd_trans[OF pn cong_1_divides[OF an]] th0 d(3) dp
    have False by auto}
  hence cpa: "coprime p a" using coprime by auto
  from coprime_exp[OF cpa, of r] coprime_commute
  have arp: "coprime (a^r) p" by blast
  from fermat_little[OF arp, simplified ord_divides] o phip
  have "q dvd (p - 1)" by simp
  then obtain d where d:"p - 1 = q * d" unfolding dvd_def by blast
  from prime_0 pp have p0:"p \<noteq> 0" by -  (rule ccontr, auto)
  from p0 d have "p + q * 0 = 1 + q * d" by simp
  with nat_mod[of p 1 q, symmetric]
  show ?thesis by blast
qed

lemma pocklington:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q*r" and sqr: "n \<le> q^2"
  and an: "[a^ (n - 1) = 1] (mod n)"
  and aq:"\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a^ ((n - 1) div p) - 1) n"
  shows "prime n"
unfolding prime_prime_factor_sqrt[of n]
proof-
  let ?ths = "n \<noteq> 0 \<and> n \<noteq> 1 \<and> \<not> (\<exists>p. prime p \<and> p dvd n \<and> p\<twosuperior> \<le> n)"
  from n have n01: "n\<noteq>0" "n\<noteq>1" by arith+
  {fix p assume p: "prime p" "p dvd n" "p^2 \<le> n"
    from p(3) sqr have "p^(Suc 1) \<le> q^(Suc 1)" by (simp add: power2_eq_square)
    hence pq: "p \<le> q" unfolding exp_mono_le .
    from pocklington_lemma[OF n nqr an aq p(1,2)]  cong_1_divides
    have th: "q dvd p - 1" by blast
    have "p - 1 \<noteq> 0"using prime_ge_2[OF p(1)] by arith
    with divides_ge[OF th] pq have False by arith }
  with n01 show ?ths by blast
qed

(* Variant for application, to separate the exponentiation.                  *)
lemma pocklington_alt:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q*r" and sqr: "n \<le> q^2"
  and an: "[a^ (n - 1) = 1] (mod n)"
  and aq:"\<forall>p. prime p \<and> p dvd q \<longrightarrow> (\<exists>b. [a^((n - 1) div p) = b] (mod n) \<and> coprime (b - 1) n)"
  shows "prime n"
proof-
  {fix p assume p: "prime p" "p dvd q"
    from aq[rule_format] p obtain b where
      b: "[a^((n - 1) div p) = b] (mod n)" "coprime (b - 1) n" by blast
    {assume a0: "a=0"
      from n an have "[0 = 1] (mod n)" unfolding a0 power_0_left by auto
      hence False using n by (simp add: modeq_def dvd_eq_mod_eq_0[symmetric])}
    hence a0: "a\<noteq> 0" ..
    hence a1: "a \<ge> 1" by arith
    from one_le_power[OF a1] have ath: "1 \<le> a ^ ((n - 1) div p)" .
    {assume b0: "b = 0"
      from p(2) nqr have "(n - 1) mod p = 0"
        apply (simp only: dvd_eq_mod_eq_0[symmetric]) by (rule dvd_mult2, simp)
      with mod_div_equality[of "n - 1" p]
      have "(n - 1) div p * p= n - 1" by auto
      hence eq: "(a^((n - 1) div p))^p = a^(n - 1)"
        by (simp only: power_mult[symmetric])
      from prime_ge_2[OF p(1)] have pS: "Suc (p - 1) = p" by arith
      from b(1) have d: "n dvd a^((n - 1) div p)" unfolding b0 cong_0_divides .
      from divides_rexp[OF d, of "p - 1"] pS eq cong_divides[OF an] n
      have False by simp}
    then have b0: "b \<noteq> 0" ..
    hence b1: "b \<ge> 1" by arith
    from cong_coprime[OF cong_sub[OF b(1) cong_refl[of 1] ath b1]] b(2) nqr
    have "coprime (a ^ ((n - 1) div p) - 1) n" by (simp add: coprime_commute)}
  hence th: "\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a ^ ((n - 1) div p) - 1) n "
    by blast
  from pocklington[OF n nqr sqr an th] show ?thesis .
qed

(* Prime factorizations.                                                     *)

definition "primefact ps n = (foldr op * ps  1 = n \<and> (\<forall>p\<in> set ps. prime p))"

lemma primefact: assumes n: "n \<noteq> 0"
  shows "\<exists>ps. primefact ps n"
using n
proof(induct n rule: nat_less_induct)
  fix n assume H: "\<forall>m<n. m \<noteq> 0 \<longrightarrow> (\<exists>ps. primefact ps m)" and n: "n\<noteq>0"
  let ?ths = "\<exists>ps. primefact ps n"
  {assume "n = 1"
    hence "primefact [] n" by (simp add: primefact_def)
    hence ?ths by blast }
  moreover
  {assume n1: "n \<noteq> 1"
    with n have n2: "n \<ge> 2" by arith
    from prime_factor[OF n1] obtain p where p: "prime p" "p dvd n" by blast
    from p(2) obtain m where m: "n = p*m" unfolding dvd_def by blast
    from n m have m0: "m > 0" "m\<noteq>0" by auto
    from prime_ge_2[OF p(1)] have "1 < p" by arith
    with m0 m have mn: "m < n" by auto
    from H[rule_format, OF mn m0(2)] obtain ps where ps: "primefact ps m" ..
    from ps m p(1) have "primefact (p#ps) n" by (simp add: primefact_def)
    hence ?ths by blast}
  ultimately show ?ths by blast
qed

lemma primefact_contains:
  assumes pf: "primefact ps n" and p: "prime p" and pn: "p dvd n"
  shows "p \<in> set ps"
  using pf p pn
proof(induct ps arbitrary: p n)
  case Nil thus ?case by (auto simp add: primefact_def)
next
  case (Cons q qs p n)
  from Cons.prems[unfolded primefact_def]
  have q: "prime q" "q * foldr op * qs 1 = n" "\<forall>p \<in>set qs. prime p"  and p: "prime p" "p dvd q * foldr op * qs 1" by simp_all
  {assume "p dvd q"
    with p(1) q(1) have "p = q" unfolding prime_def by auto
    hence ?case by simp}
  moreover
  { assume h: "p dvd foldr op * qs 1"
    from q(3) have pqs: "primefact qs (foldr op * qs 1)"
      by (simp add: primefact_def)
    from Cons.hyps[OF pqs p(1) h] have ?case by simp}
  ultimately show ?case using prime_divprod[OF p] by blast
qed

lemma primefact_variant: "primefact ps n \<longleftrightarrow> foldr op * ps 1 = n \<and> list_all prime ps"
  by (auto simp add: primefact_def list_all_iff)

(* Variant of Lucas theorem.                                                 *)

lemma lucas_primefact:
  assumes n: "n \<ge> 2" and an: "[a^(n - 1) = 1] (mod n)"
  and psn: "foldr op * ps 1 = n - 1"
  and psp: "list_all (\<lambda>p. prime p \<and> \<not> [a^((n - 1) div p) = 1] (mod n)) ps"
  shows "prime n"
proof-
  {fix p assume p: "prime p" "p dvd n - 1" "[a ^ ((n - 1) div p) = 1] (mod n)"
    from psn psp have psn1: "primefact ps (n - 1)"
      by (auto simp add: list_all_iff primefact_variant)
    from p(3) primefact_contains[OF psn1 p(1,2)] psp
    have False by (induct ps, auto)}
  with lucas[OF n an] show ?thesis by blast
qed

(* Variant of Pocklington theorem.                                           *)

lemma mod_le: assumes n: "n \<noteq> (0::nat)" shows "m mod n \<le> m"
proof-
    from mod_div_equality[of m n]
    have "\<exists>x. x + m mod n = m" by blast
    then show ?thesis by auto
qed


lemma pocklington_primefact:
  assumes n: "n \<ge> 2" and qrn: "q*r = n - 1" and nq2: "n \<le> q^2"
  and arnb: "(a^r) mod n = b" and psq: "foldr op * ps 1 = q"
  and bqn: "(b^q) mod n = 1"
  and psp: "list_all (\<lambda>p. prime p \<and> coprime ((b^(q div p)) mod n - 1) n) ps"
  shows "prime n"
proof-
  from bqn psp qrn
  have bqn: "a ^ (n - 1) mod n = 1"
    and psp: "list_all (\<lambda>p. prime p \<and> coprime (a^(r *(q div p)) mod n - 1) n) ps"  unfolding arnb[symmetric] power_mod
    by (simp_all add: power_mult[symmetric] algebra_simps)
  from n  have n0: "n > 0" by arith
  from mod_div_equality[of "a^(n - 1)" n]
    mod_less_divisor[OF n0, of "a^(n - 1)"]
  have an1: "[a ^ (n - 1) = 1] (mod n)"
    unfolding nat_mod bqn
    apply -
    apply (rule exI[where x="0"])
    apply (rule exI[where x="a^(n - 1) div n"])
    by (simp add: algebra_simps)
  {fix p assume p: "prime p" "p dvd q"
    from psp psq have pfpsq: "primefact ps q"
      by (auto simp add: primefact_variant list_all_iff)
    from psp primefact_contains[OF pfpsq p]
    have p': "coprime (a ^ (r * (q div p)) mod n - 1) n"
      by (simp add: list_all_iff)
    from prime_ge_2[OF p(1)] have p01: "p \<noteq> 0" "p \<noteq> 1" "p =Suc(p - 1)" by arith+
    from div_mult1_eq[of r q p] p(2)
    have eq1: "r* (q div p) = (n - 1) div p"
      unfolding qrn[symmetric] dvd_eq_mod_eq_0 by (simp add: mult_commute)
    have ath: "\<And>a (b::nat). a <= b \<Longrightarrow> a \<noteq> 0 ==> 1 <= a \<and> 1 <= b" by arith
    from n0 have n00: "n \<noteq> 0" by arith
    from mod_le[OF n00]
    have th10: "a ^ ((n - 1) div p) mod n \<le> a ^ ((n - 1) div p)" .
    {assume "a ^ ((n - 1) div p) mod n = 0"
      then obtain s where s: "a ^ ((n - 1) div p) = n*s"
        unfolding mod_eq_0_iff by blast
      hence eq0: "(a^((n - 1) div p))^p = (n*s)^p" by simp
      from qrn[symmetric] have qn1: "q dvd n - 1" unfolding dvd_def by auto
      from dvd_trans[OF p(2) qn1] div_mod_equality'[of "n - 1" p]
      have npp: "(n - 1) div p * p = n - 1" by (simp add: dvd_eq_mod_eq_0)
      with eq0 have "a^ (n - 1) = (n*s)^p"
        by (simp add: power_mult[symmetric])
      hence "1 = (n*s)^(Suc (p - 1)) mod n" using bqn p01 by simp
      also have "\<dots> = 0" by (simp add: mult_assoc)
      finally have False by simp }
      then have th11: "a ^ ((n - 1) div p) mod n \<noteq> 0" by auto
    have th1: "[a ^ ((n - 1) div p) mod n = a ^ ((n - 1) div p)] (mod n)"
      unfolding modeq_def by simp
    from cong_sub[OF th1 cong_refl[of 1]]  ath[OF th10 th11]
    have th: "[a ^ ((n - 1) div p) mod n - 1 = a ^ ((n - 1) div p) - 1] (mod n)"
      by blast
    from cong_coprime[OF th] p'[unfolded eq1]
    have "coprime (a ^ ((n - 1) div p) - 1) n" by (simp add: coprime_commute) }
  with pocklington[OF n qrn[symmetric] nq2 an1]
  show ?thesis by blast
qed

end
