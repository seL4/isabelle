(*  Title:      HOL/Number_Theory/Pocklington.thy
    Author:     Amine Chaieb
*)

header {* Pocklington's Theorem for Primes *}

theory Pocklington
imports Residues
begin

subsection{*Lemmas about previously defined terms*}

lemma prime: 
  "prime p \<longleftrightarrow> p \<noteq> 0 \<and> p\<noteq>1 \<and> (\<forall>m. 0 < m \<and> m < p \<longrightarrow> coprime p m)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume "p=0 \<or> p=1" hence ?thesis
    by (metis one_not_prime_nat zero_not_prime_nat)}
  moreover
  {assume p0: "p\<noteq>0" "p\<noteq>1"
    {assume H: "?lhs"
      {fix m assume m: "m > 0" "m < p"
        {assume "m=1" hence "coprime p m" by simp}
        moreover
        {assume "p dvd m" hence "p \<le> m" using dvd_imp_le m by blast with m(2)
          have "coprime p m" by simp}
        ultimately have "coprime p m" 
          by (metis H prime_imp_coprime_nat)}
      hence ?rhs using p0 by auto}
    moreover
    { assume H: "\<forall>m. 0 < m \<and> m < p \<longrightarrow> coprime p m"
      obtain q where q: "prime q" "q dvd p"
        by (metis p0(2) prime_factor_nat) 
      have q0: "q > 0"
        by (metis prime_gt_0_nat q(1))
      from dvd_imp_le[OF q(2)] p0 have qp: "q \<le> p" by arith
      {assume "q = p" hence ?lhs using q(1) by blast}
      moreover
      {assume "q\<noteq>p" with qp have qplt: "q < p" by arith
        from H[rule_format, of q] qplt q0 have "coprime p q" by arith
       hence ?lhs
         by (metis gcd_semilattice_nat.inf_absorb2 one_not_prime_nat q(1) q(2))}
      ultimately have ?lhs by blast}
    ultimately have ?thesis by blast}
  ultimately show ?thesis  by (cases"p=0 \<or> p=1", auto)
qed

lemma finite_number_segment: "card { m. 0 < m \<and> m < n } = n - 1"
proof-
  have "{ m. 0 < m \<and> m < n } = {1..<n}" by auto
  thus ?thesis by simp
qed


subsection{*Some basic theorems about solving congruences*}

lemma cong_solve: 
  fixes n::nat assumes an: "coprime a n" shows "\<exists>x. [a * x = b] (mod n)"
proof-
  {assume "a=0" hence ?thesis using an by (simp add: cong_nat_def)}
  moreover
  {assume az: "a\<noteq>0"
  from bezout_add_strong_nat[OF az, of n]
  obtain d x y where dxy: "d dvd a" "d dvd n" "a*x = n*y + d" by blast
  from dxy(1,2) have d1: "d = 1"
    by (metis assms coprime_nat) 
  hence "a*x*b = (n*y + 1)*b" using dxy(3) by simp
  hence "a*(x*b) = n*(y*b) + b"
    by (auto simp add: algebra_simps)
  hence "a*(x*b) mod n = (n*(y*b) + b) mod n" by simp
  hence "a*(x*b) mod n = b mod n" by (simp add: mod_add_left_eq)
  hence "[a*(x*b) = b] (mod n)" unfolding cong_nat_def .
  hence ?thesis by blast}
ultimately  show ?thesis by blast
qed

lemma cong_solve_unique: 
  fixes n::nat assumes an: "coprime a n" and nz: "n \<noteq> 0"
  shows "\<exists>!x. x < n \<and> [a * x = b] (mod n)"
proof-
  let ?P = "\<lambda>x. x < n \<and> [a * x = b] (mod n)"
  from cong_solve[OF an] obtain x where x: "[a*x = b] (mod n)" by blast
  let ?x = "x mod n"
  from x have th: "[a * ?x = b] (mod n)"
    by (simp add: cong_nat_def mod_mult_right_eq[of a x n])
  from mod_less_divisor[ of n x] nz th have Px: "?P ?x" by simp
  {fix y assume Py: "y < n" "[a * y = b] (mod n)"
    from Py(2) th have "[a * y = a*?x] (mod n)" by (simp add: cong_nat_def)
    hence "[y = ?x] (mod n)"
      by (metis an cong_mult_lcancel_nat) 
    with mod_less[OF Py(1)] mod_less_divisor[ of n x] nz
    have "y = ?x" by (simp add: cong_nat_def)}
  with Px show ?thesis by blast
qed

lemma cong_solve_unique_nontrivial:
  assumes p: "prime p" and pa: "coprime p a" and x0: "0 < x" and xp: "x < p"
  shows "\<exists>!y. 0 < y \<and> y < p \<and> [x * y = a] (mod p)"
proof-
  from pa have ap: "coprime a p"
    by (metis gcd_nat.commute) 
  have px:"coprime x p"
    by (metis gcd_nat.commute p prime x0 xp)
  obtain y where y: "y < p" "[x * y = a] (mod p)" "\<forall>z. z < p \<and> [x * z = a] (mod p) \<longrightarrow> z = y"
    by (metis cong_solve_unique neq0_conv p prime_gt_0_nat px)
  {assume y0: "y = 0"
    with y(2) have th: "p dvd a"
      by (metis cong_dvd_eq_nat gcd_lcm_complete_lattice_nat.top_greatest mult_0_right) 
    have False
      by (metis gcd_nat.absorb1 one_not_prime_nat p pa th)}
  with y show ?thesis unfolding Ex1_def using neq0_conv by blast
qed

lemma cong_unique_inverse_prime:
  fixes p::nat 
  assumes p: "prime p" and x0: "0 < x" and xp: "x < p"
  shows "\<exists>!y. 0 < y \<and> y < p \<and> [x * y = 1] (mod p)"
by (metis cong_solve_unique_nontrivial gcd_lcm_complete_lattice_nat.inf_bot_left gcd_nat.commute assms) 

lemma chinese_remainder_coprime_unique:
  fixes a::nat 
  assumes ab: "coprime a b" and az: "a \<noteq> 0" and bz: "b \<noteq> 0"
  and ma: "coprime m a" and nb: "coprime n b"
  shows "\<exists>!x. coprime x (a * b) \<and> x < a * b \<and> [x = m] (mod a) \<and> [x = n] (mod b)"
proof-
  let ?P = "\<lambda>x. x < a * b \<and> [x = m] (mod a) \<and> [x = n] (mod b)"
  from binary_chinese_remainder_unique_nat[OF ab az bz]
  obtain x where x: "x < a * b" "[x = m] (mod a)" "[x = n] (mod b)"
    "\<forall>y. ?P y \<longrightarrow> y = x" by blast
  from ma nb x
  have "coprime x a" "coprime x b"
    by (metis cong_gcd_eq_nat)+
  then have "coprime x (a*b)"
    by (metis coprime_mul_eq_nat)
  with x show ?thesis by blast
qed


subsection{*Lucas's theorem*}

lemma phi_limit_strong: "phi(n) \<le> n - 1"
proof -
  have "phi n = card {x. 0 < x \<and> x < int n \<and> coprime x (int n)}"
    by (simp add: phi_def)
  also have "... \<le> card {0 <..< int n}"
    by (rule card_mono) auto
  also have "... = card {0 <..< n}"
    by (simp add: transfer_nat_int_set_functions)
  also have "... \<le> n - 1"
    by (metis card_greaterThanLessThan le_refl One_nat_def)
  finally show ?thesis .
qed

lemma phi_lowerbound_1: assumes n: "n \<ge> 2"
  shows "phi n \<ge> 1"
proof -
  have "1 \<le> card {0::int <.. 1}"
    by auto
  also have "... \<le> card {x. 0 < x \<and> x < n \<and> coprime x n}"
    apply (rule card_mono) using assms
    apply (auto simp add: )
    by (metis dual_order.antisym gcd_1_int gcd_int.commute int_one_le_iff_zero_less)
  also have "... = phi n"
    by (simp add: phi_def)
  finally show ?thesis .
qed

lemma phi_lowerbound_1_nat: assumes n: "n \<ge> 2"
  shows "phi(int n) \<ge> 1"
by (metis n nat_le_iff nat_numeral phi_lowerbound_1)

lemma euler_theorem_nat:
  fixes m::nat 
  assumes "coprime a m"
  shows "[a ^ phi m = 1] (mod m)"
by (metis assms le0 euler_theorem [transferred])

lemma lucas_coprime_lemma:
  fixes n::nat 
  assumes m: "m\<noteq>0" and am: "[a^m = 1] (mod n)"
  shows "coprime a n"
proof-
  {assume "n=1" hence ?thesis by simp}
  moreover
  {assume "n = 0" hence ?thesis using am m 
     by (metis am cong_0_nat gcd_nat.right_neutral power_eq_one_eq_nat)}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    from m obtain m' where m': "m = Suc m'" by (cases m, blast+)
    {fix d
      assume d: "d dvd a" "d dvd n"
      from n have n1: "1 < n" by arith
      from am mod_less[OF n1] have am1: "a^m mod n = 1" unfolding cong_nat_def by simp
      from dvd_mult2[OF d(1), of "a^m'"] have dam:"d dvd a^m" by (simp add: m')
      from dvd_mod_iff[OF d(2), of "a^m"] dam am1
      have "d = 1" by simp }
    hence ?thesis by auto
  }
  ultimately show ?thesis by blast
qed

lemma lucas_weak:
  fixes n::nat 
  assumes n: "n \<ge> 2" and an:"[a^(n - 1) = 1] (mod n)"
  and nm: "\<forall>m. 0 <m \<and> m < n - 1 \<longrightarrow> \<not> [a^m = 1] (mod n)"
  shows "prime n"
proof-
  from n have n1: "n \<noteq> 1" "n\<noteq>0" "n - 1 \<noteq> 0" "n - 1 > 0" "n - 1 < n" by arith+
  from lucas_coprime_lemma[OF n1(3) an] have can: "coprime a n" .
  from euler_theorem_nat[OF can] have afn: "[a ^ phi n = 1] (mod n)"
    by auto 
  {assume "phi n \<noteq> n - 1"
    with phi_limit_strong phi_lowerbound_1_nat [OF n]
    have c:"phi n > 0 \<and> phi n < n - 1"
      by (metis gr0I leD less_linear not_one_le_zero)
    from nm[rule_format, OF c] afn have False ..}
  hence "phi n = n - 1" by blast
  with prime_phi phi_prime n1(1,2) show ?thesis
    by auto
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

theorem lucas:
  assumes n2: "n \<ge> 2" and an1: "[a^(n - 1) = 1] (mod n)"
  and pn: "\<forall>p. prime p \<and> p dvd n - 1 \<longrightarrow> [a^((n - 1) div p) \<noteq> 1] (mod n)"
  shows "prime n"
proof-
  from n2 have n01: "n\<noteq>0" "n\<noteq>1" "n - 1 \<noteq> 0" by arith+
  from mod_less_divisor[of n 1] n01 have onen: "1 mod n = 1" by simp
  from lucas_coprime_lemma[OF n01(3) an1] cong_imp_coprime_nat an1
  have an: "coprime a n" "coprime (a^(n - 1)) n"
    by (auto simp add: coprime_exp_nat gcd_nat.commute)
  {assume H0: "\<exists>m. 0 < m \<and> m < n - 1 \<and> [a ^ m = 1] (mod n)" (is "EX m. ?P m")
    from H0[unfolded nat_exists_least_iff[of ?P]] obtain m where
      m: "0 < m" "m < n - 1" "[a ^ m = 1] (mod n)" "\<forall>k <m. \<not>?P k" by blast
    {assume nm1: "(n - 1) mod m > 0"
      from mod_less_divisor[OF m(1)] have th0:"(n - 1) mod m < m" by blast
      let ?y = "a^ ((n - 1) div m * m)"
      note mdeq = mod_div_equality[of "(n - 1)" m]
      have yn: "coprime ?y n"
        by (metis an(1) coprime_exp_nat gcd_nat.commute)
      have "?y mod n = (a^m)^((n - 1) div m) mod n"
        by (simp add: algebra_simps power_mult)
      also have "\<dots> = (a^m mod n)^((n - 1) div m) mod n"
        using power_mod[of "a^m" n "(n - 1) div m"] by simp
      also have "\<dots> = 1" using m(3)[unfolded cong_nat_def onen] onen
        by (metis power_one)
      finally have th3: "?y mod n = 1"  .
      have th2: "[?y * a ^ ((n - 1) mod m) = ?y* 1] (mod n)"
        using an1[unfolded cong_nat_def onen] onen
          mod_div_equality[of "(n - 1)" m, symmetric]
        by (simp add:power_add[symmetric] cong_nat_def th3 del: One_nat_def)
      have th1: "[a ^ ((n - 1) mod m) = 1] (mod n)"
        by (metis cong_mult_rcancel_nat nat_mult_commute th2 yn)
      from m(4)[rule_format, OF th0] nm1
        less_trans[OF mod_less_divisor[OF m(1), of "n - 1"] m(2)] th1
      have False by blast }
    hence "(n - 1) mod m = 0" by auto
    then have mn: "m dvd n - 1" by presburger
    then obtain r where r: "n - 1 = m*r" unfolding dvd_def by blast
    from n01 r m(2) have r01: "r\<noteq>0" "r\<noteq>1" by - (rule ccontr, simp)+
    obtain p where p: "prime p" "p dvd r"
      by (metis prime_factor_nat r01(2))
    hence th: "prime p \<and> p dvd n - 1" unfolding r by (auto intro: dvd_mult)
    have "(a ^ ((n - 1) div p)) mod n = (a^(m*r div p)) mod n" using r
      by (simp add: power_mult)
    also have "\<dots> = (a^(m*(r div p))) mod n" using div_mult1_eq[of m r p] p(2)[unfolded dvd_eq_mod_eq_0] by simp
    also have "\<dots> = ((a^m)^(r div p)) mod n" by (simp add: power_mult)
    also have "\<dots> = ((a^m mod n)^(r div p)) mod n" using power_mod[of "a^m" "n" "r div p" ] ..
    also have "\<dots> = 1" using m(3) onen by (simp add: cong_nat_def power_Suc_0)
    finally have "[(a ^ ((n - 1) div p))= 1] (mod n)"
      using onen by (simp add: cong_nat_def)
    with pn[rule_format, OF th] have False by blast}
  hence th: "\<forall>m. 0 < m \<and> m < n - 1 \<longrightarrow> \<not> [a ^ m = 1] (mod n)" by blast
  from lucas_weak[OF n2 an1 th] show ?thesis .
qed


subsection{*Definition of the order of a number mod n (0 in non-coprime case)*}

definition "ord n a = (if coprime n a then Least (\<lambda>d. d > 0 \<and> [a ^d = 1] (mod n)) else 0)"

(* This has the expected properties.                                         *)

lemma coprime_ord:
  fixes n::nat 
  assumes "coprime n a"
  shows "ord n a > 0 \<and> [a ^(ord n a) = 1] (mod n) \<and> (\<forall>m. 0 < m \<and> m < ord n a \<longrightarrow> [a^ m \<noteq> 1] (mod n))"
proof-
  let ?P = "\<lambda>d. 0 < d \<and> [a ^ d = 1] (mod n)"
  from bigger_prime[of a] obtain p where p: "prime p" "a < p" by blast
  from assms have o: "ord n a = Least ?P" by (simp add: ord_def)
  {assume "n=0 \<or> n=1" with assms have "\<exists>m>0. ?P m" 
      by auto}
  moreover
  {assume "n\<noteq>0 \<and> n\<noteq>1" hence n2:"n \<ge> 2" by arith
    from assms have na': "coprime a n"
      by (metis gcd_nat.commute)
    from phi_lowerbound_1_nat[OF n2] euler_theorem_nat [OF na']
    have ex: "\<exists>m>0. ?P m" by - (rule exI[where x="phi n"], auto) }
  ultimately have ex: "\<exists>m>0. ?P m" by blast
  from nat_exists_least_iff'[of ?P] ex assms show ?thesis
    unfolding o[symmetric] by auto
qed

(* With the special value 0 for non-coprime case, it's more convenient.      *)
lemma ord_works:
  fixes n::nat
  shows "[a ^ (ord n a) = 1] (mod n) \<and> (\<forall>m. 0 < m \<and> m < ord n a \<longrightarrow> ~[a^ m = 1] (mod n))"
apply (cases "coprime n a")
using coprime_ord[of n a]
by (blast, simp add: ord_def cong_nat_def)

lemma ord:
  fixes n::nat
  shows "[a^(ord n a) = 1] (mod n)" using ord_works by blast

lemma ord_minimal:
  fixes n::nat
  shows "0 < m \<Longrightarrow> m < ord n a \<Longrightarrow> ~[a^m = 1] (mod n)"
  using ord_works by blast

lemma ord_eq_0:
  fixes n::nat
  shows "ord n a = 0 \<longleftrightarrow> ~coprime n a"
by (cases "coprime n a", simp add: coprime_ord, simp add: ord_def)

lemma divides_rexp: 
  "x dvd y \<Longrightarrow> (x::nat) dvd (y^(Suc n))" 
  by (simp add: dvd_mult2[of x y])

lemma ord_divides:
  fixes n::nat
  shows "[a ^ d = 1] (mod n) \<longleftrightarrow> ord n a dvd d" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume rh: ?rhs
  then obtain k where "d = ord n a * k" unfolding dvd_def by blast
  hence "[a ^ d = (a ^ (ord n a) mod n)^k] (mod n)"
    by (simp add : cong_nat_def power_mult power_mod)
  also have "[(a ^ (ord n a) mod n)^k = 1] (mod n)"
    using ord[of a n, unfolded cong_nat_def]
    by (simp add: cong_nat_def power_mod)
  finally  show ?lhs .
next
  assume lh: ?lhs
  { assume H: "\<not> coprime n a"
    hence o: "ord n a = 0" by (simp add: ord_def)
    {assume d: "d=0" with o H have ?rhs by (simp add: cong_nat_def)}
    moreover
    {assume d0: "d\<noteq>0" then obtain d' where d': "d = Suc d'" by (cases d, auto)
      from H
      obtain p where p: "p dvd n" "p dvd a" "p \<noteq> 1" by auto
      from lh
      obtain q1 q2 where q12:"a ^ d + n * q1 = 1 + n * q2"
        by (metis H d0 gcd_nat.commute lucas_coprime_lemma) 
      hence "a ^ d + n * q1 - n * q2 = 1" by simp
      with dvd_diff_nat [OF dvd_add [OF divides_rexp[OF p(2), of d'] dvd_mult2[OF p(1), of q1]] dvd_mult2[OF p(1), of q2]] d' 
      have "p dvd 1" by simp
      with p(3) have False by simp
      hence ?rhs ..}
    ultimately have ?rhs by blast}
  moreover
  {assume H: "coprime n a"
    let ?o = "ord n a"
    let ?q = "d div ord n a"
    let ?r = "d mod ord n a"
    have eqo: "[(a^?o)^?q = 1] (mod n)"
      by (metis cong_exp_nat ord power_one)
    from H have onz: "?o \<noteq> 0" by (simp add: ord_eq_0)
    hence op: "?o > 0" by simp
    from mod_div_equality[of d "ord n a"] lh
    have "[a^(?o*?q + ?r) = 1] (mod n)" by (simp add: cong_nat_def mult_commute)
    hence "[(a^?o)^?q * (a^?r) = 1] (mod n)"
      by (simp add: cong_nat_def power_mult[symmetric] power_add[symmetric])
    hence th: "[a^?r = 1] (mod n)"
      using eqo mod_mult_left_eq[of "(a^?o)^?q" "a^?r" n]
      apply (simp add: cong_nat_def del: One_nat_def)
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

lemma order_divides_phi: 
  fixes n::nat shows "coprime n a \<Longrightarrow> ord n a dvd phi n"
  by (metis ord_divides euler_theorem_nat gcd_nat.commute)

lemma order_divides_expdiff:
  fixes n::nat and a::nat assumes na: "coprime n a"
  shows "[a^d = a^e] (mod n) \<longleftrightarrow> [d = e] (mod (ord n a))"
proof-
  {fix n::nat and a::nat and d::nat and e::nat
    assume na: "coprime n a" and ed: "(e::nat) \<le> d"
    hence "\<exists>c. d = e + c" by presburger
    then obtain c where c: "d = e + c" by presburger
    from na have an: "coprime a n"
      by (metis gcd_nat.commute)
    have aen: "coprime (a^e) n"
      by (metis coprime_exp_nat gcd_nat.commute na)      
    have acn: "coprime (a^c) n"
      by (metis coprime_exp_nat gcd_nat.commute na) 
    have "[a^d = a^e] (mod n) \<longleftrightarrow> [a^(e + c) = a^(e + 0)] (mod n)"
      using c by simp
    also have "\<dots> \<longleftrightarrow> [a^e* a^c = a^e *a^0] (mod n)" by (simp add: power_add)
    also have  "\<dots> \<longleftrightarrow> [a ^ c = 1] (mod n)"
      using cong_mult_lcancel_nat [OF aen, of "a^c" "a^0"] by simp
    also  have "\<dots> \<longleftrightarrow> ord n a dvd c" by (simp only: ord_divides)
    also have "\<dots> \<longleftrightarrow> [e + c = e + 0] (mod ord n a)"
      using cong_add_lcancel_nat 
      by (metis cong_dvd_eq_nat dvd_0_right cong_dvd_modulus_nat cong_mult_self_nat nat_mult_1)
    finally have "[a^d = a^e] (mod n) \<longleftrightarrow> [d = e] (mod (ord n a))"
      using c by simp }
  note th = this
  have "e \<le> d \<or> d \<le> e" by arith
  moreover
  {assume ed: "e \<le> d" from th[OF na ed] have ?thesis .}
  moreover
  {assume de: "d \<le> e"
    from th[OF na de] have ?thesis
    by (metis cong_sym_nat)}
  ultimately show ?thesis by blast
qed

subsection{*Another trivial primality characterization*}

lemma prime_prime_factor:
  "prime n \<longleftrightarrow> n \<noteq> 1\<and> (\<forall>p. prime p \<and> p dvd n \<longrightarrow> p = n)"
proof-
  {assume n: "n=0 \<or> n=1" 
   hence ?thesis
     by (metis bigger_prime dvd_0_right one_not_prime_nat zero_not_prime_nat) }
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
       then obtain p where p: "prime p" "p dvd m"
         by (metis prime_factor_nat) 
       from dvd_trans[OF p(2) m(1)] p(1) H have "p = n" by blast
       with p(2) have "n dvd m"  by simp
       hence "m=n"  using dvd_antisym[OF m(1)] by simp }
      with n1 have "prime n"  unfolding prime_def by auto }
    ultimately have ?thesis using n by blast}
  ultimately       show ?thesis by auto
qed

lemma prime_divisor_sqrt:
  "prime n \<longleftrightarrow> n \<noteq> 1 \<and> (\<forall>d. d dvd n \<and> d\<^sup>2 \<le> n \<longrightarrow> d = 1)"
proof -
  {assume "n=0 \<or> n=1" hence ?thesis
    by (metis dvd.order_refl le_refl one_not_prime_nat power_zero_numeral zero_not_prime_nat)}
  moreover
  {assume n: "n\<noteq>0" "n\<noteq>1"
    hence np: "n > 1" by arith
    {fix d assume d: "d dvd n" "d\<^sup>2 \<le> n" and H: "\<forall>m. m dvd n \<longrightarrow> m=1 \<or> m=n"
      from H d have d1n: "d = 1 \<or> d=n" by blast
      {assume dn: "d=n"
        have "n\<^sup>2 > n*1" using n by (simp add: power2_eq_square)
        with dn d(2) have "d=1" by simp}
      with d1n have "d = 1" by blast  }
    moreover
    {fix d assume d: "d dvd n" and H: "\<forall>d'. d' dvd n \<and> d'\<^sup>2 \<le> n \<longrightarrow> d' = 1"
      from d n have "d \<noteq> 0"
        by (metis dvd_0_left_iff)
      hence dp: "d > 0" by simp
      from d[unfolded dvd_def] obtain e where e: "n= d*e" by blast
      from n dp e have ep:"e > 0" by simp
      have "d\<^sup>2 \<le> n \<or> e\<^sup>2 \<le> n" using dp ep
        by (auto simp add: e power2_eq_square mult_le_cancel_left)
      moreover
      {assume h: "d\<^sup>2 \<le> n"
        from H[rule_format, of d] h d have "d = 1" by blast}
      moreover
      {assume h: "e\<^sup>2 \<le> n"
        from e have "e dvd n" unfolding dvd_def by (simp add: mult_commute)
        with H[rule_format, of e] h have "e=1" by simp
        with e have "d = n" by simp}
      ultimately have "d=1 \<or> d=n"  by blast}
    ultimately have ?thesis unfolding prime_def using np n(2) by blast}
  ultimately show ?thesis by auto
qed

lemma prime_prime_factor_sqrt:
  "prime n \<longleftrightarrow> n \<noteq> 0 \<and> n \<noteq> 1 \<and> \<not> (\<exists>p. prime p \<and> p dvd n \<and> p\<^sup>2 \<le> n)"
  (is "?lhs \<longleftrightarrow>?rhs")
proof-
  {assume "n=0 \<or> n=1" 
   hence ?thesis
     by (metis one_not_prime_nat zero_not_prime_nat)}
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
      {fix d assume d: "d dvd n" "d\<^sup>2 \<le> n" "d\<noteq>1"
        then obtain p where p: "prime p" "p dvd d"
          by (metis prime_factor_nat) 
        from n have np: "n > 0" by arith
        from d(1) n have "d \<noteq> 0" by - (rule ccontr, auto)
        hence dp: "d > 0" by arith
        from mult_mono[OF dvd_imp_le[OF p(2) dp] dvd_imp_le[OF p(2) dp]] d(2)
        have "p\<^sup>2 \<le> n" unfolding power2_eq_square by arith
        with H n p(1) dvd_trans[OF p(2) d(1)] have False  by blast}
      with n prime_divisor_sqrt  have ?lhs by auto}
    ultimately have ?thesis by blast }
  ultimately show ?thesis by (cases "n=0 \<or> n=1", auto)
qed


subsection{*Pocklington theorem*}

lemma pocklington_lemma:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q*r" and an: "[a^ (n - 1) = 1] (mod n)"
  and aq:"\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a^ ((n - 1) div p) - 1) n"
  and pp: "prime p" and pn: "p dvd n"
  shows "[p = 1] (mod q)"
proof -
  have p01: "p \<noteq> 0" "p \<noteq> 1" using pp one_not_prime_nat zero_not_prime_nat by auto
  obtain k where k: "a ^ (q * r) - 1 = n*k"
    by (metis an cong_to_1_nat dvd_def nqr)
  from pn[unfolded dvd_def] obtain l where l: "n = p*l" by blast
  {assume a0: "a = 0"
    hence "a^ (n - 1) = 0" using n by (simp add: power_0_left)
    with n an mod_less[of 1 n]  have False by (simp add: power_0_left cong_nat_def)}
  hence a0: "a\<noteq>0" ..
  from n nqr have aqr0: "a ^ (q * r) \<noteq> 0" using a0 by simp
  hence "(a ^ (q * r) - 1) + 1  = a ^ (q * r)" by simp
  with k l have "a ^ (q * r) = p*l*k + 1" by simp
  hence "a ^ (r * q) + p * 0 = 1 + p * (l*k)" by (simp add: mult_ac)
  hence odq: "ord p (a^r) dvd q"
    unfolding ord_divides[symmetric] power_mult[symmetric]
    by (metis an cong_dvd_modulus_nat mult_commute nqr pn) 
  from odq[unfolded dvd_def] obtain d where d: "q = ord p (a^r) * d" by blast
  {assume d1: "d \<noteq> 1"
    obtain P where P: "prime P" "P dvd d"
      by (metis d1 prime_factor_nat) 
    from d dvd_mult[OF P(2), of "ord p (a^r)"] have Pq: "P dvd q" by simp
    from aq P(1) Pq have caP:"coprime (a^ ((n - 1) div P) - 1) n" by blast
    from Pq obtain s where s: "q = P*s" unfolding dvd_def by blast
    have P0: "P \<noteq> 0" using P(1)
      by (metis zero_not_prime_nat) 
    from P(2) obtain t where t: "d = P*t" unfolding dvd_def by blast
    from d s t P0  have s': "ord p (a^r) * t = s"
      by (metis mult_commute mult_cancel1 nat_mult_assoc) 
    have "ord p (a^r) * t*r = r * ord p (a^r) * t"
      by (metis mult_assoc mult_commute)
    hence exps: "a^(ord p (a^r) * t*r) = ((a ^ r) ^ ord p (a^r)) ^ t"
      by (simp only: power_mult)
    have "[((a ^ r) ^ ord p (a^r)) ^ t= 1^t] (mod p)"
      by (metis cong_exp_nat ord)
    then have th: "[((a ^ r) ^ ord p (a^r)) ^ t= 1] (mod p)"
      by simp
    have pd0: "p dvd a^(ord p (a^r) * t*r) - 1"
      by (metis cong_to_1_nat exps th)
    from nqr s s' have "(n - 1) div P = ord p (a^r) * t*r" using P0 by simp
    with caP have "coprime (a^(ord p (a^r) * t*r) - 1) n" by simp
    with p01 pn pd0 coprime_common_divisor_nat have False 
      by auto}
  hence d1: "d = 1" by blast
  hence o: "ord p (a^r) = q" using d by simp
  from pp phi_prime[of p] have phip: "phi p = p - 1" by simp
  {fix d assume d: "d dvd p" "d dvd a" "d \<noteq> 1"
    from pp[unfolded prime_def] d have dp: "d = p" by blast
    from n have "n \<noteq> 0" by simp
    then have False using d
      by (metis coprime_minus_one_nat dp lucas_coprime_lemma an coprime_nat 
           gcd_lcm_complete_lattice_nat.top_greatest pn)} 
  hence cpa: "coprime p a" by auto
  have arp: "coprime (a^r) p"
    by (metis coprime_exp_nat cpa gcd_nat.commute) 
  from euler_theorem_nat[OF arp, simplified ord_divides] o phip
  have "q dvd (p - 1)" by simp
  then obtain d where d:"p - 1 = q * d" unfolding dvd_def by blast
  have p0:"p \<noteq> 0"
    by (metis p01(1)) 
  from p0 d have "p + q * 0 = 1 + q * d" by simp
  then show ?thesis
    by (metis cong_iff_lin_nat mult_commute)
qed

theorem pocklington:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q*r" and sqr: "n \<le> q\<^sup>2"
  and an: "[a^ (n - 1) = 1] (mod n)"
  and aq: "\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a^ ((n - 1) div p) - 1) n"
  shows "prime n"
unfolding prime_prime_factor_sqrt[of n]
proof-
  let ?ths = "n \<noteq> 0 \<and> n \<noteq> 1 \<and> \<not> (\<exists>p. prime p \<and> p dvd n \<and> p\<^sup>2 \<le> n)"
  from n have n01: "n\<noteq>0" "n\<noteq>1" by arith+
  {fix p assume p: "prime p" "p dvd n" "p\<^sup>2 \<le> n"
    from p(3) sqr have "p^(Suc 1) \<le> q^(Suc 1)" by (simp add: power2_eq_square)
    hence pq: "p \<le> q"
      by (metis le0 power_le_imp_le_base) 
    from pocklington_lemma[OF n nqr an aq p(1,2)] 
    have th: "q dvd p - 1"
      by (metis cong_to_1_nat) 
    have "p - 1 \<noteq> 0" using prime_ge_2_nat [OF p(1)] by arith
    with pq p have False
      by (metis Suc_diff_1 gcd_le2_nat gcd_semilattice_nat.inf_absorb1 not_less_eq_eq
            prime_gt_0_nat th) }
  with n01 show ?ths by blast
qed

(* Variant for application, to separate the exponentiation.                  *)
lemma pocklington_alt:
  assumes n: "n \<ge> 2" and nqr: "n - 1 = q*r" and sqr: "n \<le> q\<^sup>2"
  and an: "[a^ (n - 1) = 1] (mod n)"
  and aq:"\<forall>p. prime p \<and> p dvd q \<longrightarrow> (\<exists>b. [a^((n - 1) div p) = b] (mod n) \<and> coprime (b - 1) n)"
  shows "prime n"
proof-
  {fix p assume p: "prime p" "p dvd q"
    from aq[rule_format] p obtain b where
      b: "[a^((n - 1) div p) = b] (mod n)" "coprime (b - 1) n" by blast
    {assume a0: "a=0"
      from n an have "[0 = 1] (mod n)" unfolding a0 power_0_left by auto
      hence False using n by (simp add: cong_nat_def dvd_eq_mod_eq_0[symmetric])}
    hence a0: "a\<noteq> 0" ..
    hence a1: "a \<ge> 1" by arith
    from one_le_power[OF a1] have ath: "1 \<le> a ^ ((n - 1) div p)" .
    {assume b0: "b = 0"
      from p(2) nqr have "(n - 1) mod p = 0"
        by (metis mod_0 mod_mod_cancel mod_mult_self1_is_0)
      with mod_div_equality[of "n - 1" p]
      have "(n - 1) div p * p= n - 1" by auto
      hence eq: "(a^((n - 1) div p))^p = a^(n - 1)"
        by (simp only: power_mult[symmetric])
      have "p - 1 \<noteq> 0" using prime_ge_2_nat [OF p(1)] by arith
      then have pS: "Suc (p - 1) = p" by arith
      from b have d: "n dvd a^((n - 1) div p)" unfolding b0
        by (metis b0 diff_0_eq_0 gcd_dvd2_nat gcd_lcm_complete_lattice_nat.inf_bot_left 
                   gcd_lcm_complete_lattice_nat.inf_top_left) 
      from divides_rexp[OF d, of "p - 1"] pS eq cong_dvd_eq_nat [OF an] n
      have False
        by simp}
    then have b0: "b \<noteq> 0" ..
    hence b1: "b \<ge> 1" by arith thm Cong.cong_diff_nat[OF cong_sym_nat [OF b(1)] cong_refl_nat[of 1]]
    from cong_imp_coprime_nat[OF Cong.cong_diff_nat[OF cong_sym_nat [OF b(1)] cong_refl_nat[of 1] b1]] ath b1 b(2) nqr
    have "coprime (a ^ ((n - 1) div p) - 1) n"
      by simp}
  hence th: "\<forall>p. prime p \<and> p dvd q \<longrightarrow> coprime (a ^ ((n - 1) div p) - 1) n "
    by blast
  from pocklington[OF n nqr sqr an th] show ?thesis .
qed


subsection{*Prime factorizations*}

text{*FIXME Some overlap with material in UniqueFactorization, class unique_factorization.*}

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
    obtain p where p: "prime p" "p dvd n"
      by (metis n1 prime_factor_nat) 
    from p(2) obtain m where m: "n = p*m" unfolding dvd_def by blast
    from n m have m0: "m > 0" "m\<noteq>0" by auto
    have "1 < p"
      by (metis p(1) prime_nat_def)
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
  ultimately show ?case
    by (metis p prime_dvd_mult_eq_nat) 
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

lemma pocklington_primefact:
  assumes n: "n \<ge> 2" and qrn: "q*r = n - 1" and nq2: "n \<le> q\<^sup>2"
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
    by (metis bqn cong_nat_def mod_mod_trivial)
  {fix p assume p: "prime p" "p dvd q"
    from psp psq have pfpsq: "primefact ps q"
      by (auto simp add: primefact_variant list_all_iff)
    from psp primefact_contains[OF pfpsq p]
    have p': "coprime (a ^ (r * (q div p)) mod n - 1) n"
      by (simp add: list_all_iff)
    from p prime_def have p01: "p \<noteq> 0" "p \<noteq> 1" "p =Suc(p - 1)" 
      by auto
    from div_mult1_eq[of r q p] p(2)
    have eq1: "r* (q div p) = (n - 1) div p"
      unfolding qrn[symmetric] dvd_eq_mod_eq_0 by (simp add: mult_commute)
    have ath: "\<And>a (b::nat). a <= b \<Longrightarrow> a \<noteq> 0 ==> 1 <= a \<and> 1 <= b" by arith
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
      unfolding cong_nat_def by simp
    from  th1   ath[OF mod_less_eq_dividend th11]
    have th: "[a ^ ((n - 1) div p) mod n - 1 = a ^ ((n - 1) div p) - 1] (mod n)"
      by (metis cong_diff_nat cong_refl_nat)
    have "coprime (a ^ ((n - 1) div p) - 1) n"
      by (metis cong_imp_coprime_nat eq1 p' th) }
  with pocklington[OF n qrn[symmetric] nq2 an1]
  show ?thesis by blast
qed

end
