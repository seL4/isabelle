(*  Title:      HOL/Library/Primes.thy
    Author:     Amine Chaieb, Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

header {* Primality on nat *}

theory Primes
imports Plain "~~/src/HOL/ATP_Linkup" "~~/src/HOL/GCD" "~~/src/HOL/Parity"
begin

definition
  coprime :: "nat => nat => bool" where
  "coprime m n \<longleftrightarrow> gcd m n = 1"

definition
  prime :: "nat \<Rightarrow> bool" where
  [code del]: "prime p \<longleftrightarrow> (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"


lemma two_is_prime: "prime 2"
  apply (auto simp add: prime_def)
  apply (case_tac m)
   apply (auto dest!: dvd_imp_le)
  done

lemma prime_imp_relprime: "prime p ==> \<not> p dvd n ==> gcd p n = 1"
  apply (auto simp add: prime_def)
  apply (metis One_nat_def gcd_dvd1 gcd_dvd2)
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


lemma exp_eq_1:"(x::nat)^n = 1 \<longleftrightarrow> x = 1 \<or> n = 0"
by (induct n, auto)

lemma exp_mono_lt: "(x::nat) ^ (Suc n) < y ^ (Suc n) \<longleftrightarrow> x < y"
by(metis linorder_not_less not_less0 power_le_imp_le_base power_less_imp_less_base)

lemma exp_mono_le: "(x::nat) ^ (Suc n) \<le> y ^ (Suc n) \<longleftrightarrow> x \<le> y"
by (simp only: linorder_not_less[symmetric] exp_mono_lt)

lemma exp_mono_eq: "(x::nat) ^ Suc n = y ^ Suc n \<longleftrightarrow> x = y"
using power_inject_base[of x n y] by auto


lemma even_square: assumes e: "even (n::nat)" shows "\<exists>x. n ^ 2 = 4*x"
proof-
  from e have "2 dvd n" by presburger
  then obtain k where k: "n = 2*k" using dvd_def by auto
  hence "n^2 = 4* (k^2)" by (simp add: power2_eq_square)
  thus ?thesis by blast
qed

lemma odd_square: assumes e: "odd (n::nat)" shows "\<exists>x. n ^ 2 = 4*x + 1"
proof-
  from e have np: "n > 0" by presburger
  from e have "2 dvd (n - 1)" by presburger
  then obtain k where "n - 1 = 2*k" using dvd_def by auto
  hence k: "n = 2*k + 1"  using e by presburger 
  hence "n^2 = 4* (k^2 + k) + 1" by algebra   
  thus ?thesis by blast
qed

lemma diff_square: "(x::nat)^2 - y^2 = (x+y)*(x - y)" 
proof-
  have "x \<le> y \<or> y \<le> x" by (rule nat_le_linear)
  moreover
  {assume le: "x \<le> y"
    hence "x ^2 \<le> y^2" by (simp only: numeral_2_eq_2 exp_mono_le Let_def)
    with le have ?thesis by simp }
  moreover
  {assume le: "y \<le> x"
    hence le2: "y ^2 \<le> x^2" by (simp only: numeral_2_eq_2 exp_mono_le Let_def)
    from le have "\<exists>z. y + z = x" by presburger
    then obtain z where z: "x = y + z" by blast 
    from le2 have "\<exists>z. x^2 = y^2 + z" by presburger
    then obtain z2 where z2: "x^2 = y^2 + z2"  by blast
    from z z2 have ?thesis apply simp by algebra }
  ultimately show ?thesis by blast  
qed

text {* Elementary theory of divisibility *}
lemma divides_ge: "(a::nat) dvd b \<Longrightarrow> b = 0 \<or> a \<le> b" unfolding dvd_def by auto
lemma divides_antisym: "(x::nat) dvd y \<and> y dvd x \<longleftrightarrow> x = y"
  using dvd_anti_sym[of x y] by auto

lemma divides_add_revr: assumes da: "(d::nat) dvd a" and dab:"d dvd (a + b)"
  shows "d dvd b"
proof-
  from da obtain k where k:"a = d*k" by (auto simp add: dvd_def)
  from dab obtain k' where k': "a + b = d*k'" by (auto simp add: dvd_def)
  from k k' have "b = d *(k' - k)" by (simp add : diff_mult_distrib2)
  thus ?thesis unfolding dvd_def by blast
qed

declare nat_mult_dvd_cancel_disj[presburger]
lemma nat_mult_dvd_cancel_disj'[presburger]: 
  "(m\<Colon>nat)*k dvd n*k \<longleftrightarrow> k = 0 \<or> m dvd n" unfolding mult_commute[of m k] mult_commute[of n k] by presburger 

lemma divides_mul_l: "(a::nat) dvd b ==> (c * a) dvd (c * b)"
  by presburger

lemma divides_mul_r: "(a::nat) dvd b ==> (a * c) dvd (b * c)" by presburger
lemma divides_cases: "(n::nat) dvd m ==> m = 0 \<or> m = n \<or> 2 * n <= m" 
  by (auto simp add: dvd_def)

lemma divides_div_not: "(x::nat) = (q * n) + r \<Longrightarrow> 0 < r \<Longrightarrow> r < n ==> ~(n dvd x)"
proof(auto simp add: dvd_def)
  fix k assume H: "0 < r" "r < n" "q * n + r = n * k"
  from H(3) have r: "r = n* (k -q)" by(simp add: diff_mult_distrib2 mult_commute)
  {assume "k - q = 0" with r H(1) have False by simp}
  moreover
  {assume "k - q \<noteq> 0" with r have "r \<ge> n" by auto
    with H(2) have False by simp}
  ultimately show False by blast
qed
lemma divides_exp: "(x::nat) dvd y ==> x ^ n dvd y ^ n"
  by (auto simp add: power_mult_distrib dvd_def)

lemma divides_exp2: "n \<noteq> 0 \<Longrightarrow> (x::nat) ^ n dvd y \<Longrightarrow> x dvd y" 
  by (induct n ,auto simp add: dvd_def)

fun fact :: "nat \<Rightarrow> nat" where
  "fact 0 = 1"
| "fact (Suc n) = Suc n * fact n"	

lemma fact_lt: "0 < fact n" by(induct n, simp_all)
lemma fact_le: "fact n \<ge> 1" using fact_lt[of n] by simp 
lemma fact_mono: assumes le: "m \<le> n" shows "fact m \<le> fact n"
proof-
  from le have "\<exists>i. n = m+i" by presburger
  then obtain i where i: "n = m+i" by blast 
  have "fact m \<le> fact (m + i)"
  proof(induct m)
    case 0 thus ?case using fact_le[of i] by simp
  next
    case (Suc m)
    have "fact (Suc m) = Suc m * fact m" by simp
    have th1: "Suc m \<le> Suc (m + i)" by simp
    from mult_le_mono[of "Suc m" "Suc (m+i)" "fact m" "fact (m+i)", OF th1 Suc.hyps]
    show ?case by simp
  qed
  thus ?thesis using i by simp
qed

lemma divides_fact: "1 <= p \<Longrightarrow> p <= n ==> p dvd fact n"
proof(induct n arbitrary: p)
  case 0 thus ?case by simp
next
  case (Suc n p)
  from Suc.prems have "p = Suc n \<or> p \<le> n" by presburger 
  moreover
  {assume "p = Suc n" hence ?case  by (simp only: fact.simps dvd_triv_left)}
  moreover
  {assume "p \<le> n"
    with Suc.prems(1) Suc.hyps have th: "p dvd fact n" by simp
    from dvd_mult[OF th] have ?case by (simp only: fact.simps) }
  ultimately show ?case by blast
qed

declare dvd_triv_left[presburger]
declare dvd_triv_right[presburger]
lemma divides_rexp: 
  "x dvd y \<Longrightarrow> (x::nat) dvd (y^(Suc n))" by (simp add: dvd_mult2[of x y])

text {* Coprimality *}

lemma coprime: "coprime a b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
using gcd_unique[of 1 a b, simplified] by (auto simp add: coprime_def)
lemma coprime_commute: "coprime a b \<longleftrightarrow> coprime b a" by (simp add: coprime_def gcd_commute)

lemma coprime_bezout: "coprime a b \<longleftrightarrow> (\<exists>x y. a * x - b * y = 1 \<or> b * x - a * y = 1)"
using coprime_def gcd_bezout by auto

lemma coprime_divprod: "d dvd a * b  \<Longrightarrow> coprime d a \<Longrightarrow> d dvd b"
  using relprime_dvd_mult_iff[of d a b] by (auto simp add: coprime_def mult_commute)

lemma coprime_1[simp]: "coprime a 1" by (simp add: coprime_def)
lemma coprime_1'[simp]: "coprime 1 a" by (simp add: coprime_def)
lemma coprime_Suc0[simp]: "coprime a (Suc 0)" by (simp add: coprime_def)
lemma coprime_Suc0'[simp]: "coprime (Suc 0) a" by (simp add: coprime_def)

lemma gcd_coprime: 
  assumes z: "gcd a b \<noteq> 0" and a: "a = a' * gcd a b" and b: "b = b' * gcd a b" 
  shows    "coprime a' b'"
proof-
  let ?g = "gcd a b"
  {assume bz: "a = 0" from b bz z a have ?thesis by (simp add: gcd_zero coprime_def)}
  moreover 
  {assume az: "a\<noteq> 0" 
    from z have z': "?g > 0" by simp
    from bezout_gcd_strong[OF az, of b] 
    obtain x y where xy: "a*x = b*y + ?g" by blast
    from xy a b have "?g * a'*x = ?g * (b'*y + 1)" by (simp add: algebra_simps)
    hence "?g * (a'*x) = ?g * (b'*y + 1)" by (simp add: mult_assoc)
    hence "a'*x = (b'*y + 1)"
      by (simp only: nat_mult_eq_cancel1[OF z']) 
    hence "a'*x - b'*y = 1" by simp
    with coprime_bezout[of a' b'] have ?thesis by auto}
  ultimately show ?thesis by blast
qed
lemma coprime_0: "coprime d 0 \<longleftrightarrow> d = 1" by (simp add: coprime_def)
lemma coprime_mul: assumes da: "coprime d a" and db: "coprime d b"
  shows "coprime d (a * b)"
proof-
  from da have th: "gcd a d = 1" by (simp add: coprime_def gcd_commute)
  from gcd_mult_cancel[of a d b, OF th] db[unfolded coprime_def] have "gcd d (a*b) = 1"
    by (simp add: gcd_commute)
  thus ?thesis unfolding coprime_def .
qed
lemma coprime_lmul2: assumes dab: "coprime d (a * b)" shows "coprime d b"
using prems unfolding coprime_bezout
apply clarsimp
apply (case_tac "d * x - a * b * y = Suc 0 ", simp_all)
apply (rule_tac x="x" in exI)
apply (rule_tac x="a*y" in exI)
apply (simp add: mult_ac)
apply (rule_tac x="a*x" in exI)
apply (rule_tac x="y" in exI)
apply (simp add: mult_ac)
done

lemma coprime_rmul2: "coprime d (a * b) \<Longrightarrow> coprime d a"
unfolding coprime_bezout
apply clarsimp
apply (case_tac "d * x - a * b * y = Suc 0 ", simp_all)
apply (rule_tac x="x" in exI)
apply (rule_tac x="b*y" in exI)
apply (simp add: mult_ac)
apply (rule_tac x="b*x" in exI)
apply (rule_tac x="y" in exI)
apply (simp add: mult_ac)
done
lemma coprime_mul_eq: "coprime d (a * b) \<longleftrightarrow> coprime d a \<and>  coprime d b"
  using coprime_rmul2[of d a b] coprime_lmul2[of d a b] coprime_mul[of d a b] 
  by blast

lemma gcd_coprime_exists:
  assumes nz: "gcd a b \<noteq> 0" 
  shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> coprime a' b'"
proof-
  let ?g = "gcd a b"
  from gcd_dvd1[of a b] gcd_dvd2[of a b] 
  obtain a' b' where "a = ?g*a'"  "b = ?g*b'" unfolding dvd_def by blast
  hence ab': "a = a'*?g" "b = b'*?g" by algebra+
  from ab' gcd_coprime[OF nz ab'] show ?thesis by blast
qed

lemma coprime_exp: "coprime d a ==> coprime d (a^n)" 
  by(induct n, simp_all add: coprime_mul)

lemma coprime_exp_imp: "coprime a b ==> coprime (a ^n) (b ^n)"
  by (induct n, simp_all add: coprime_mul_eq coprime_commute coprime_exp)
lemma coprime_refl[simp]: "coprime n n \<longleftrightarrow> n = 1" by (simp add: coprime_def)
lemma coprime_plus1[simp]: "coprime (n + 1) n"
  apply (simp add: coprime_bezout)
  apply (rule exI[where x=1])
  apply (rule exI[where x=1])
  apply simp
  done
lemma coprime_minus1: "n \<noteq> 0 ==> coprime (n - 1) n"
  using coprime_plus1[of "n - 1"] coprime_commute[of "n - 1" n] by auto

lemma bezout_gcd_pow: "\<exists>x y. a ^n * x - b ^ n * y = gcd a b ^ n \<or> b ^ n * x - a ^ n * y = gcd a b ^ n"
proof-
  let ?g = "gcd a b"
  {assume z: "?g = 0" hence ?thesis 
      apply (cases n, simp)
      apply arith
      apply (simp only: z power_0_Suc)
      apply (rule exI[where x=0])
      apply (rule exI[where x=0])
      by simp}
  moreover
  {assume z: "?g \<noteq> 0"
    from gcd_dvd1[of a b] gcd_dvd2[of a b] obtain a' b' where
      ab': "a = a'*?g" "b = b'*?g" unfolding dvd_def by (auto simp add: mult_ac)
    hence ab'': "?g*a' = a" "?g * b' = b" by algebra+
    from coprime_exp_imp[OF gcd_coprime[OF z ab'], unfolded coprime_bezout, of n]
    obtain x y where "a'^n * x - b'^n * y = 1 \<or> b'^n * x - a'^n * y = 1"  by blast
    hence "?g^n * (a'^n * x - b'^n * y) = ?g^n \<or> ?g^n*(b'^n * x - a'^n * y) = ?g^n"
      using z by auto 
    then have "a^n * x - b^n * y = ?g^n \<or> b^n * x - a^n * y = ?g^n"
      using z ab'' by (simp only: power_mult_distrib[symmetric] 
	diff_mult_distrib2 mult_assoc[symmetric])
    hence  ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma gcd_exp: "gcd (a^n) (b^n) = gcd a b^n"
proof-
  let ?g = "gcd (a^n) (b^n)"
  let ?gn = "gcd a b^n"
  {fix e assume H: "e dvd a^n" "e dvd b^n"
    from bezout_gcd_pow[of a n b] obtain x y 
      where xy: "a ^ n * x - b ^ n * y = ?gn \<or> b ^ n * x - a ^ n * y = ?gn" by blast
    from nat_dvd_diff [OF dvd_mult2[OF H(1), of x] dvd_mult2[OF H(2), of y]]
      nat_dvd_diff [OF dvd_mult2[OF H(2), of x] dvd_mult2[OF H(1), of y]] xy
    have "e dvd ?gn" by (cases "a ^ n * x - b ^ n * y = gcd a b ^ n", simp_all)}
  hence th:  "\<forall>e. e dvd a^n \<and> e dvd b^n \<longrightarrow> e dvd ?gn" by blast
  from divides_exp[OF gcd_dvd1[of a b], of n] divides_exp[OF gcd_dvd2[of a b], of n] th
    gcd_unique have "?gn = ?g" by blast thus ?thesis by simp 
qed

lemma coprime_exp2:  "coprime (a ^ Suc n) (b^ Suc n) \<longleftrightarrow> coprime a b"
by (simp only: coprime_def gcd_exp exp_eq_1) simp

lemma division_decomp: assumes dc: "(a::nat) dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof-
  let ?g = "gcd a b"
  {assume "?g = 0" with dc have ?thesis apply (simp add: gcd_zero)
      apply (rule exI[where x="0"])
      by (rule exI[where x="c"], simp)}
  moreover
  {assume z: "?g \<noteq> 0"
    from gcd_coprime_exists[OF z]
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'" by blast
    from gcd_dvd2[of a b] have thb: "?g dvd b" .
    from ab'(1) have "a' dvd a"  unfolding dvd_def by blast  
    with dc have th0: "a' dvd b*c" using dvd_trans[of a' a "b*c"] by simp
    from dc ab'(1,2) have "a'*?g dvd (b'*?g) *c" by auto
    hence "?g*a' dvd ?g * (b' * c)" by (simp add: mult_assoc)
    with z have th_1: "a' dvd b'*c" by simp
    from coprime_divprod[OF th_1 ab'(3)] have thc: "a' dvd c" . 
    from ab' have "a = ?g*a'" by algebra
    with thb thc have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma nat_power_eq_0_iff: "(m::nat) ^ n = 0 \<longleftrightarrow> n \<noteq> 0 \<and> m = 0" by (induct n, auto)

lemma divides_rev: assumes ab: "(a::nat) ^ n dvd b ^n" and n:"n \<noteq> 0" shows "a dvd b"
proof-
  let ?g = "gcd a b"
  from n obtain m where m: "n = Suc m" by (cases n, simp_all)
  {assume "?g = 0" with ab n have ?thesis by (simp add: gcd_zero)}
  moreover
  {assume z: "?g \<noteq> 0"
    hence zn: "?g ^ n \<noteq> 0" using n by (simp add: neq0_conv)
    from gcd_coprime_exists[OF z] 
    obtain a' b' where ab': "a = a' * ?g" "b = b' * ?g" "coprime a' b'" by blast
    from ab have "(a' * ?g) ^ n dvd (b' * ?g)^n" by (simp add: ab'(1,2)[symmetric])
    hence "?g^n*a'^n dvd ?g^n *b'^n" by (simp only: power_mult_distrib mult_commute)
    with zn z n have th0:"a'^n dvd b'^n" by (auto simp add: nat_power_eq_0_iff)
    have "a' dvd a'^n" by (simp add: m)
    with th0 have "a' dvd b'^n" using dvd_trans[of a' "a'^n" "b'^n"] by simp
    hence th1: "a' dvd b'^m * b'" by (simp add: m mult_commute)
    from coprime_divprod[OF th1 coprime_exp[OF ab'(3), of m]]
    have "a' dvd b'" .
    hence "a'*?g dvd b'*?g" by simp
    with ab'(1,2)  have ?thesis by simp }
  ultimately show ?thesis by blast
qed

lemma divides_mul: assumes mr: "m dvd r" and nr: "n dvd r" and mn:"coprime m n" 
  shows "m * n dvd r"
proof-
  from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
    unfolding dvd_def by blast
  from mr n' have "m dvd n'*n" by (simp add: mult_commute)
  hence "m dvd n'" using relprime_dvd_mult_iff[OF mn[unfolded coprime_def]] by simp
  then obtain k where k: "n' = m*k" unfolding dvd_def by blast
  from n' k show ?thesis unfolding dvd_def by auto
qed


text {* A binary form of the Chinese Remainder Theorem. *}

lemma chinese_remainder: assumes ab: "coprime a b" and a:"a \<noteq> 0" and b:"b \<noteq> 0"
  shows "\<exists>x q1 q2. x = u + q1 * a \<and> x = v + q2 * b"
proof-
  from bezout_add_strong[OF a, of b] bezout_add_strong[OF b, of a]
  obtain d1 x1 y1 d2 x2 y2 where dxy1: "d1 dvd a" "d1 dvd b" "a * x1 = b * y1 + d1" 
    and dxy2: "d2 dvd b" "d2 dvd a" "b * x2 = a * y2 + d2" by blast
  from gcd_unique[of 1 a b, simplified ab[unfolded coprime_def], simplified] 
    dxy1(1,2) dxy2(1,2) have d12: "d1 = 1" "d2 =1" by auto
  let ?x = "v * a * x1 + u * b * x2"
  let ?q1 = "v * x1 + u * y2"
  let ?q2 = "v * y1 + u * x2"
  from dxy2(3)[simplified d12] dxy1(3)[simplified d12] 
  have "?x = u + ?q1 * a" "?x = v + ?q2 * b" by algebra+ 
  thus ?thesis by blast
qed

text {* Primality *}

text {* A few useful theorems about primes *}

lemma prime_0[simp]: "~prime 0" by (simp add: prime_def)
lemma prime_1[simp]: "~ prime 1"  by (simp add: prime_def)
lemma prime_Suc0[simp]: "~ prime (Suc 0)"  by (simp add: prime_def)

lemma prime_ge_2: "prime p ==> p \<ge> 2" by (simp add: prime_def)
lemma prime_factor: assumes n: "n \<noteq> 1" shows "\<exists> p. prime p \<and> p dvd n"
using n
proof(induct n rule: nat_less_induct)
  fix n
  assume H: "\<forall>m<n. m \<noteq> 1 \<longrightarrow> (\<exists>p. prime p \<and> p dvd m)" "n \<noteq> 1"
  let ?ths = "\<exists>p. prime p \<and> p dvd n"
  {assume "n=0" hence ?ths using two_is_prime by auto}
  moreover
  {assume nz: "n\<noteq>0" 
    {assume "prime n" hence ?ths by - (rule exI[where x="n"], simp)}
    moreover
    {assume n: "\<not> prime n"
      with nz H(2) 
      obtain k where k:"k dvd n" "k \<noteq> 1" "k \<noteq> n" by (auto simp add: prime_def) 
      from dvd_imp_le[OF k(1)] nz k(3) have kn: "k < n" by simp
      from H(1)[rule_format, OF kn k(2)] obtain p where p: "prime p" "p dvd k" by blast
      from dvd_trans[OF p(2) k(1)] p(1) have ?ths by blast}
    ultimately have ?ths by blast}
  ultimately show ?ths by blast
qed

lemma prime_factor_lt: assumes p: "prime p" and n: "n \<noteq> 0" and npm:"n = p * m"
  shows "m < n"
proof-
  {assume "m=0" with n have ?thesis by simp}
  moreover
  {assume m: "m \<noteq> 0"
    from npm have mn: "m dvd n" unfolding dvd_def by auto
    from npm m have "n \<noteq> m" using p by auto
    with dvd_imp_le[OF mn] n have ?thesis by simp}
  ultimately show ?thesis by blast
qed

lemma euclid_bound: "\<exists>p. prime p \<and> n < p \<and>  p <= Suc (fact n)"
proof-
  have f1: "fact n + 1 \<noteq> 1" using fact_le[of n] by arith 
  from prime_factor[OF f1] obtain p where p: "prime p" "p dvd fact n + 1" by blast
  from dvd_imp_le[OF p(2)] have pfn: "p \<le> fact n + 1" by simp
  {assume np: "p \<le> n"
    from p(1) have p1: "p \<ge> 1" by (cases p, simp_all)
    from divides_fact[OF p1 np] have pfn': "p dvd fact n" .
    from divides_add_revr[OF pfn' p(2)] p(1) have False by simp}
  hence "n < p" by arith
  with p(1) pfn show ?thesis by auto
qed

lemma euclid: "\<exists>p. prime p \<and> p > n" using euclid_bound by auto
lemma primes_infinite: "\<not> (finite {p. prime p})"
proof (auto simp add: finite_conv_nat_seg_image)
  fix n f 
  assume H: "Collect prime = f ` {i. i < (n::nat)}"
  let ?P = "Collect prime"
  let ?m = "Max ?P"
  have P0: "?P \<noteq> {}" using two_is_prime by auto
  from H have fP: "finite ?P" using finite_conv_nat_seg_image by blast 
  from Max_in [OF fP P0] have "?m \<in> ?P" . 
  from Max_ge [OF fP] have contr: "\<forall> p. prime p \<longrightarrow> p \<le> ?m" by blast
  from euclid [of ?m] obtain q where q: "prime q" "q > ?m" by blast
  with contr show False by auto
qed

lemma coprime_prime: assumes ab: "coprime a b"
  shows "~(prime p \<and> p dvd a \<and> p dvd b)"
proof
  assume "prime p \<and> p dvd a \<and> p dvd b"
  thus False using ab gcd_greatest[of p a b] by (simp add: coprime_def)
qed
lemma coprime_prime_eq: "coprime a b \<longleftrightarrow> (\<forall>p. ~(prime p \<and> p dvd a \<and> p dvd b))" 
  (is "?lhs = ?rhs")
proof-
  {assume "?lhs" with coprime_prime  have ?rhs by blast}
  moreover
  {assume r: "?rhs" and c: "\<not> ?lhs"
    then obtain g where g: "g\<noteq>1" "g dvd a" "g dvd b" unfolding coprime_def by blast
    from prime_factor[OF g(1)] obtain p where p: "prime p" "p dvd g" by blast
    from dvd_trans [OF p(2) g(2)] dvd_trans [OF p(2) g(3)] 
    have "p dvd a" "p dvd b" . with p(1) r have False by blast}
  ultimately show ?thesis by blast
qed

lemma prime_coprime: assumes p: "prime p" 
  shows "n = 1 \<or> p dvd n \<or> coprime p n"
using p prime_imp_relprime[of p n] by (auto simp add: coprime_def)

lemma prime_coprime_strong: "prime p \<Longrightarrow> p dvd n \<or> coprime p n"
  using prime_coprime[of p n] by auto

declare  coprime_0[simp]

lemma coprime_0'[simp]: "coprime 0 d \<longleftrightarrow> d = 1" by (simp add: coprime_commute[of 0 d])
lemma coprime_bezout_strong: assumes ab: "coprime a b" and b: "b \<noteq> 1"
  shows "\<exists>x y. a * x = b * y + 1"
proof-
  from ab b have az: "a \<noteq> 0" by - (rule ccontr, auto)
  from bezout_gcd_strong[OF az, of b] ab[unfolded coprime_def]
  show ?thesis by auto
qed

lemma bezout_prime: assumes p: "prime p"  and pa: "\<not> p dvd a"
  shows "\<exists>x y. a*x = p*y + 1"
proof-
  from p have p1: "p \<noteq> 1" using prime_1 by blast 
  from prime_coprime[OF p, of a] p1 pa have ap: "coprime a p" 
    by (auto simp add: coprime_commute)
  from coprime_bezout_strong[OF ap p1] show ?thesis . 
qed
lemma prime_divprod: assumes p: "prime p" and pab: "p dvd a*b"
  shows "p dvd a \<or> p dvd b"
proof-
  {assume "a=1" hence ?thesis using pab by simp }
  moreover
  {assume "p dvd a" hence ?thesis by blast}
  moreover
  {assume pa: "coprime p a" from coprime_divprod[OF pab pa]  have ?thesis .. }
  ultimately show ?thesis using prime_coprime[OF p, of a] by blast
qed

lemma prime_divprod_eq: assumes p: "prime p"
  shows "p dvd a*b \<longleftrightarrow> p dvd a \<or> p dvd b"
using p prime_divprod dvd_mult dvd_mult2 by auto

lemma prime_divexp: assumes p:"prime p" and px: "p dvd x^n"
  shows "p dvd x"
using px
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n) 
  hence th: "p dvd x*x^n" by simp
  {assume H: "p dvd x^n"
    from Suc.hyps[OF H] have ?case .}
  with prime_divprod[OF p th] show ?case by blast
qed

lemma prime_divexp_n: "prime p \<Longrightarrow> p dvd x^n \<Longrightarrow> p^n dvd x^n"
  using prime_divexp[of p x n] divides_exp[of p x n] by blast

lemma coprime_prime_dvd_ex: assumes xy: "\<not>coprime x y"
  shows "\<exists>p. prime p \<and> p dvd x \<and> p dvd y"
proof-
  from xy[unfolded coprime_def] obtain g where g: "g \<noteq> 1" "g dvd x" "g dvd y" 
    by blast
  from prime_factor[OF g(1)] obtain p where p: "prime p" "p dvd g" by blast
  from g(2,3) dvd_trans[OF p(2)] p(1) show ?thesis by auto
qed
lemma coprime_sos: assumes xy: "coprime x y" 
  shows "coprime (x * y) (x^2 + y^2)"
proof-
  {assume c: "\<not> coprime (x * y) (x^2 + y^2)"
    from coprime_prime_dvd_ex[OF c] obtain p 
      where p: "prime p" "p dvd x*y" "p dvd x^2 + y^2" by blast
    {assume px: "p dvd x"
      from dvd_mult[OF px, of x] p(3) 
        obtain r s where "x * x = p * r" and "x^2 + y^2 = p * s"
          by (auto elim!: dvdE)
        then have "y^2 = p * (s - r)" 
          by (auto simp add: power2_eq_square diff_mult_distrib2)
        then have "p dvd y^2" ..
      with prime_divexp[OF p(1), of y 2] have py: "p dvd y" .
      from p(1) px py xy[unfolded coprime, rule_format, of p] prime_1  
      have False by simp }
    moreover
    {assume py: "p dvd y"
      from dvd_mult[OF py, of y] p(3)
        obtain r s where "y * y = p * r" and "x^2 + y^2 = p * s"
          by (auto elim!: dvdE)
        then have "x^2 = p * (s - r)" 
          by (auto simp add: power2_eq_square diff_mult_distrib2)
        then have "p dvd x^2" ..
      with prime_divexp[OF p(1), of x 2] have px: "p dvd x" .
      from p(1) px py xy[unfolded coprime, rule_format, of p] prime_1  
      have False by simp }
    ultimately have False using prime_divprod[OF p(1,2)] by blast}
  thus ?thesis by blast
qed

lemma distinct_prime_coprime: "prime p \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  unfolding prime_def coprime_prime_eq by blast

lemma prime_coprime_lt: assumes p: "prime p" and x: "0 < x" and xp: "x < p"
  shows "coprime x p"
proof-
  {assume c: "\<not> coprime x p"
    then obtain g where g: "g \<noteq> 1" "g dvd x" "g dvd p" unfolding coprime_def by blast
  from dvd_imp_le[OF g(2)] x xp have gp: "g < p" by arith
  from g(2) x have "g \<noteq> 0" by - (rule ccontr, simp)
  with g gp p[unfolded prime_def] have False by blast}
thus ?thesis by blast
qed

lemma even_dvd[simp]: "even (n::nat) \<longleftrightarrow> 2 dvd n" by presburger
lemma prime_odd: "prime p \<Longrightarrow> p = 2 \<or> odd p" unfolding prime_def by auto


text {* One property of coprimality is easier to prove via prime factors. *}

lemma prime_divprod_pow: 
  assumes p: "prime p" and ab: "coprime a b" and pab: "p^n dvd a * b"
  shows "p^n dvd a \<or> p^n dvd b"
proof-
  {assume "n = 0 \<or> a = 1 \<or> b = 1" with pab have ?thesis 
      apply (cases "n=0", simp_all)
      apply (cases "a=1", simp_all) done}
  moreover
  {assume n: "n \<noteq> 0" and a: "a\<noteq>1" and b: "b\<noteq>1" 
    then obtain m where m: "n = Suc m" by (cases n, auto)
    from divides_exp2[OF n pab] have pab': "p dvd a*b" .
    from prime_divprod[OF p pab'] 
    have "p dvd a \<or> p dvd b" .
    moreover
    {assume pa: "p dvd a"
      have pnba: "p^n dvd b*a" using pab by (simp add: mult_commute)
      from coprime_prime[OF ab, of p] p pa have "\<not> p dvd b" by blast
      with prime_coprime[OF p, of b] b 
      have cpb: "coprime b p" using coprime_commute by blast 
      from coprime_exp[OF cpb] have pnb: "coprime (p^n) b" 
	by (simp add: coprime_commute)
      from coprime_divprod[OF pnba pnb] have ?thesis by blast }
    moreover
    {assume pb: "p dvd b"
      have pnba: "p^n dvd b*a" using pab by (simp add: mult_commute)
      from coprime_prime[OF ab, of p] p pb have "\<not> p dvd a" by blast
      with prime_coprime[OF p, of a] a
      have cpb: "coprime a p" using coprime_commute by blast 
      from coprime_exp[OF cpb] have pnb: "coprime (p^n) a" 
	by (simp add: coprime_commute)
      from coprime_divprod[OF pab pnb] have ?thesis by blast }
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma nat_mult_eq_one: "(n::nat) * m = 1 \<longleftrightarrow> n = 1 \<and> m = 1" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume H: "?lhs"
  hence "n dvd 1" "m dvd 1" unfolding dvd_def by (auto simp add: mult_commute)
  thus ?rhs by auto
next
  assume ?rhs then show ?lhs by auto
qed
  
lemma power_Suc0[simp]: "Suc 0 ^ n = Suc 0" 
  unfolding One_nat_def[symmetric] power_one ..
lemma coprime_pow: assumes ab: "coprime a b" and abcn: "a * b = c ^n"
  shows "\<exists>r s. a = r^n  \<and> b = s ^n"
  using ab abcn
proof(induct c arbitrary: a b rule: nat_less_induct)
  fix c a b
  assume H: "\<forall>m<c. \<forall>a b. coprime a b \<longrightarrow> a * b = m ^ n \<longrightarrow> (\<exists>r s. a = r ^ n \<and> b = s ^ n)" "coprime a b" "a * b = c ^ n" 
  let ?ths = "\<exists>r s. a = r^n  \<and> b = s ^n"
  {assume n: "n = 0"
    with H(3) power_one have "a*b = 1" by simp
    hence "a = 1 \<and> b = 1" by simp
    hence ?ths 
      apply -
      apply (rule exI[where x=1])
      apply (rule exI[where x=1])
      using power_one[of  n]
      by simp}
  moreover
  {assume n: "n \<noteq> 0" then obtain m where m: "n = Suc m" by (cases n, auto)
    {assume c: "c = 0"
      with H(3) m H(2) have ?ths apply simp 
	apply (cases "a=0", simp_all) 
	apply (rule exI[where x="0"], simp)
	apply (rule exI[where x="0"], simp)
	done}
    moreover
    {assume "c=1" with H(3) power_one have "a*b = 1" by simp 
	hence "a = 1 \<and> b = 1" by simp
	hence ?ths 
      apply -
      apply (rule exI[where x=1])
      apply (rule exI[where x=1])
      using power_one[of  n]
      by simp}
  moreover
  {assume c: "c\<noteq>1" "c \<noteq> 0"
    from prime_factor[OF c(1)] obtain p where p: "prime p" "p dvd c" by blast
    from prime_divprod_pow[OF p(1) H(2), unfolded H(3), OF divides_exp[OF p(2), of n]] 
    have pnab: "p ^ n dvd a \<or> p^n dvd b" . 
    from p(2) obtain l where l: "c = p*l" unfolding dvd_def by blast
    have pn0: "p^n \<noteq> 0" using n prime_ge_2 [OF p(1)] by (simp add: neq0_conv)
    {assume pa: "p^n dvd a"
      then obtain k where k: "a = p^n * k" unfolding dvd_def by blast
      from l have "l dvd c" by auto
      with dvd_imp_le[of l c] c have "l \<le> c" by auto
      moreover {assume "l = c" with l c  have "p = 1" by simp with p have False by simp}
      ultimately have lc: "l < c" by arith
      from coprime_lmul2 [OF H(2)[unfolded k coprime_commute[of "p^n*k" b]]]
      have kb: "coprime k b" by (simp add: coprime_commute) 
      from H(3) l k pn0 have kbln: "k * b = l ^ n" 
	by (auto simp add: power_mult_distrib)
      from H(1)[rule_format, OF lc kb kbln]
      obtain r s where rs: "k = r ^n" "b = s^n" by blast
      from k rs(1) have "a = (p*r)^n" by (simp add: power_mult_distrib)
      with rs(2) have ?ths by blast }
    moreover
    {assume pb: "p^n dvd b"
      then obtain k where k: "b = p^n * k" unfolding dvd_def by blast
      from l have "l dvd c" by auto
      with dvd_imp_le[of l c] c have "l \<le> c" by auto
      moreover {assume "l = c" with l c  have "p = 1" by simp with p have False by simp}
      ultimately have lc: "l < c" by arith
      from coprime_lmul2 [OF H(2)[unfolded k coprime_commute[of "p^n*k" a]]]
      have kb: "coprime k a" by (simp add: coprime_commute) 
      from H(3) l k pn0 n have kbln: "k * a = l ^ n" 
	by (simp add: power_mult_distrib mult_commute)
      from H(1)[rule_format, OF lc kb kbln]
      obtain r s where rs: "k = r ^n" "a = s^n" by blast
      from k rs(1) have "b = (p*r)^n" by (simp add: power_mult_distrib)
      with rs(2) have ?ths by blast }
    ultimately have ?ths using pnab by blast}
  ultimately have ?ths by blast}
ultimately show ?ths by blast
qed

text {* More useful lemmas. *}
lemma prime_product: 
  assumes "prime (p * q)"
  shows "p = 1 \<or> q = 1"
proof -
  from assms have 
    "1 < p * q" and P: "\<And>m. m dvd p * q \<Longrightarrow> m = 1 \<or> m = p * q"
    unfolding prime_def by auto
  from `1 < p * q` have "p \<noteq> 0" by (cases p) auto
  then have Q: "p = p * q \<longleftrightarrow> q = 1" by auto
  have "p dvd p * q" by simp
  then have "p = 1 \<or> p = p * q" by (rule P)
  then show ?thesis by (simp add: Q)
qed

lemma prime_exp: "prime (p^n) \<longleftrightarrow> prime p \<and> n = 1"
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
	by (simp only: exp_eq_1 ) simp
      with pp have "prime p \<and> Suc n = 1" by simp}
    moreover
    {assume n: "prime p \<and> Suc n = 1" hence "prime (p^Suc n)" by simp}
    ultimately have ?case by blast}
  ultimately show ?case by blast
qed

lemma prime_power_mult: 
  assumes p: "prime p" and xy: "x * y = p ^ k"
  shows "\<exists>i j. x = p ^i \<and> y = p^ j"
  using xy
proof(induct k arbitrary: x y)
  case 0 thus ?case apply simp by (rule exI[where x="0"], simp)
next
  case (Suc k x y)
  from Suc.prems have pxy: "p dvd x*y" by auto
  from prime_divprod[OF p pxy] have pxyc: "p dvd x \<or> p dvd y" .
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
    from Suc.prems d  have "p*d*x = p^Suc k" by (simp add: mult_commute)
    hence th: "d*x = p^k" using p0 by simp
    from Suc.hyps[OF th] obtain i j where ij: "d = p^i" "x = p^j" by blast
    with d have "y = p^Suc i" by simp 
    with ij(2) have ?case by blast}
  ultimately show ?case  using pxyc by blast
qed

lemma prime_power_exp: assumes p: "prime p" and n:"n \<noteq> 0" 
  and xn: "x^n = p^k" shows "\<exists>i. x = p^i"
  using n xn
proof(induct n arbitrary: k)
  case 0 thus ?case by simp
next
  case (Suc n k) hence th: "x*x^n = p^k" by simp
  {assume "n = 0" with prems have ?case apply simp 
      by (rule exI[where x="k"],simp)}
  moreover
  {assume n: "n \<noteq> 0"
    from prime_power_mult[OF p th] 
    obtain i j where ij: "x = p^i" "x^n = p^j"by blast
    from Suc.hyps[OF n ij(2)] have ?case .}
  ultimately show ?case by blast
qed

lemma divides_primepow: assumes p: "prime p" 
  shows "d dvd p^k \<longleftrightarrow> (\<exists> i. i \<le> k \<and> d = p ^i)"
proof
  assume H: "d dvd p^k" then obtain e where e: "d*e = p^k" 
    unfolding dvd_def  apply (auto simp add: mult_commute) by blast
  from prime_power_mult[OF p e] obtain i j where ij: "d = p^i" "e=p^j" by blast
  from prime_ge_2[OF p] have p1: "p > 1" by arith
  from e ij have "p^(i + j) = p^k" by (simp add: power_add)
  hence "i + j = k" using power_inject_exp[of p "i+j" k, OF p1] by simp 
  hence "i \<le> k" by arith
  with ij(1) show "\<exists>i\<le>k. d = p ^ i" by blast
next
  {fix i assume H: "i \<le> k" "d = p^i"
    hence "\<exists>j. k = i + j" by arith
    then obtain j where j: "k = i + j" by blast
    hence "p^k = p^j*d" using H(2) by (simp add: power_add)
    hence "d dvd p^k" unfolding dvd_def by auto}
  thus "\<exists>i\<le>k. d = p ^ i \<Longrightarrow> d dvd p ^ k" by blast
qed

lemma coprime_divisors: "d dvd a \<Longrightarrow> e dvd b \<Longrightarrow> coprime a b \<Longrightarrow> coprime d e"
  by (auto simp add: dvd_def coprime)

declare power_Suc0[simp del]
declare even_dvd[simp del]

end
