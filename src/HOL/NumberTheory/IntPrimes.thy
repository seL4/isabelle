(*  Title:      HOL/NumberTheory/IntPrimes.thy
    ID:         $Id$
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge

Changes by Jeremy Avigad, 2003/02/21:
   Repaired definition of zprime_def, added "0 <= m &"
   Added lemma zgcd_geq_zero
   Repaired proof of zprime_imp_zrelprime
*)

header {* Divisibility and prime numbers (on integers) *}

theory IntPrimes = Primes:

text {*
  The @{text dvd} relation, GCD, Euclid's extended algorithm, primes,
  congruences (all on the Integers).  Comparable to theory @{text
  Primes}, but @{text dvd} is included here as it is not present in
  main HOL.  Also includes extended GCD and congruences not present in
  @{text Primes}.
*}


subsection {* Definitions *}

consts
  xzgcda :: "int * int * int * int * int * int * int * int => int * int * int"

recdef xzgcda
  "measure ((\<lambda>(m, n, r', r, s', s, t', t). nat r)
    :: int * int * int * int *int * int * int * int => nat)"
  "xzgcda (m, n, r', r, s', s, t', t) =
	(if r \<le> 0 then (r', s', t')
	 else xzgcda (m, n, r, r' mod r, 
		      s, s' - (r' div r) * s, 
		      t, t' - (r' div r) * t))"

constdefs
  zgcd :: "int * int => int"
  "zgcd == \<lambda>(x,y). int (gcd (nat (abs x), nat (abs y)))"

  zprime :: "int set"
  "zprime == {p. 1 < p \<and> (\<forall>m. 0 <= m & m dvd p --> m = 1 \<or> m = p)}"

  xzgcd :: "int => int => int * int * int"
  "xzgcd m n == xzgcda (m, n, m, n, 1, 0, 0, 1)"

  zcong :: "int => int => int => bool"    ("(1[_ = _] '(mod _'))")
  "[a = b] (mod m) == m dvd (a - b)"



text {* \medskip @{term gcd} lemmas *}

lemma gcd_add1_eq: "gcd (m + k, k) = gcd (m + k, m)"
  by (simp add: gcd_commute)

lemma gcd_diff2: "m \<le> n ==> gcd (n, n - m) = gcd (n, m)"
  apply (subgoal_tac "n = m + (n - m)")
   apply (erule ssubst, rule gcd_add1_eq, simp)
  done


subsection {* Euclid's Algorithm and GCD *}

lemma zgcd_0 [simp]: "zgcd (m, 0) = abs m"
  by (simp add: zgcd_def zabs_def)

lemma zgcd_0_left [simp]: "zgcd (0, m) = abs m"
  by (simp add: zgcd_def zabs_def)

lemma zgcd_zminus [simp]: "zgcd (-m, n) = zgcd (m, n)"
  by (simp add: zgcd_def)

lemma zgcd_zminus2 [simp]: "zgcd (m, -n) = zgcd (m, n)"
  by (simp add: zgcd_def)

lemma zgcd_non_0: "0 < n ==> zgcd (m, n) = zgcd (n, m mod n)"
  apply (frule_tac b = n and a = m in pos_mod_sign)
  apply (simp del: pos_mod_sign add: zgcd_def zabs_def nat_mod_distrib)
  apply (auto simp add: gcd_non_0 nat_mod_distrib [symmetric] zmod_zminus1_eq_if)
  apply (frule_tac a = m in pos_mod_bound)
  apply (simp del: pos_mod_bound add: nat_diff_distrib gcd_diff2 nat_le_eq_zle)
  done

lemma zgcd_eq: "zgcd (m, n) = zgcd (n, m mod n)"
  apply (case_tac "n = 0", simp add: DIVISION_BY_ZERO)
  apply (auto simp add: linorder_neq_iff zgcd_non_0)
  apply (cut_tac m = "-m" and n = "-n" in zgcd_non_0, auto)
  done

lemma zgcd_1 [simp]: "zgcd (m, 1) = 1"
  by (simp add: zgcd_def zabs_def)

lemma zgcd_0_1_iff [simp]: "(zgcd (0, m) = 1) = (abs m = 1)"
  by (simp add: zgcd_def zabs_def)

lemma zgcd_zdvd1 [iff]: "zgcd (m, n) dvd m"
  by (simp add: zgcd_def zabs_def int_dvd_iff)

lemma zgcd_zdvd2 [iff]: "zgcd (m, n) dvd n"
  by (simp add: zgcd_def zabs_def int_dvd_iff)

lemma zgcd_greatest_iff: "k dvd zgcd (m, n) = (k dvd m \<and> k dvd n)"
  by (simp add: zgcd_def zabs_def int_dvd_iff dvd_int_iff nat_dvd_iff)

lemma zgcd_commute: "zgcd (m, n) = zgcd (n, m)"
  by (simp add: zgcd_def gcd_commute)

lemma zgcd_1_left [simp]: "zgcd (1, m) = 1"
  by (simp add: zgcd_def gcd_1_left)

lemma zgcd_assoc: "zgcd (zgcd (k, m), n) = zgcd (k, zgcd (m, n))"
  by (simp add: zgcd_def gcd_assoc)

lemma zgcd_left_commute: "zgcd (k, zgcd (m, n)) = zgcd (m, zgcd (k, n))"
  apply (rule zgcd_commute [THEN trans])
  apply (rule zgcd_assoc [THEN trans])
  apply (rule zgcd_commute [THEN arg_cong])
  done

lemmas zgcd_ac = zgcd_assoc zgcd_commute zgcd_left_commute
  -- {* addition is an AC-operator *}

lemma zgcd_zmult_distrib2: "0 \<le> k ==> k * zgcd (m, n) = zgcd (k * m, k * n)"
  by (simp del: zmult_zminus_right
      add: zmult_zminus_right [symmetric] nat_mult_distrib zgcd_def zabs_def
          zmult_less_0_iff gcd_mult_distrib2 [symmetric] zmult_int [symmetric])

lemma zgcd_zmult_distrib2_abs: "zgcd (k * m, k * n) = abs k * zgcd (m, n)"
  by (simp add: zabs_def zgcd_zmult_distrib2)

lemma zgcd_self [simp]: "0 \<le> m ==> zgcd (m, m) = m"
  by (cut_tac k = m and m = 1 and n = 1 in zgcd_zmult_distrib2, simp_all)

lemma zgcd_zmult_eq_self [simp]: "0 \<le> k ==> zgcd (k, k * n) = k"
  by (cut_tac k = k and m = 1 and n = n in zgcd_zmult_distrib2, simp_all)

lemma zgcd_zmult_eq_self2 [simp]: "0 \<le> k ==> zgcd (k * n, k) = k"
  by (cut_tac k = k and m = n and n = 1 in zgcd_zmult_distrib2, simp_all)

lemma zrelprime_zdvd_zmult_aux:
     "zgcd (n, k) = 1 ==> k dvd m * n ==> 0 \<le> m ==> k dvd m"
  apply (subgoal_tac "m = zgcd (m * n, m * k)")
   apply (erule ssubst, rule zgcd_greatest_iff [THEN iffD2])
   apply (simp_all add: zgcd_zmult_distrib2 [symmetric] int_0_le_mult_iff)
  done

lemma zrelprime_zdvd_zmult: "zgcd (n, k) = 1 ==> k dvd m * n ==> k dvd m"
  apply (case_tac "0 \<le> m")
   apply (blast intro: zrelprime_zdvd_zmult_aux)
  apply (subgoal_tac "k dvd -m")
   apply (rule_tac [2] zrelprime_zdvd_zmult_aux, auto)
  done

lemma zgcd_geq_zero: "0 <= zgcd(x,y)"
  by (auto simp add: zgcd_def)

text{*This is merely a sanity check on zprime, since the previous version
      denoted the empty set.*}
lemma "2 \<in> zprime"
  apply (auto simp add: zprime_def) 
  apply (frule zdvd_imp_le, simp) 
  apply (auto simp add: order_le_less dvd_def) 
  done

lemma zprime_imp_zrelprime:
    "p \<in> zprime ==> \<not> p dvd n ==> zgcd (n, p) = 1"
  apply (auto simp add: zprime_def)
  apply (drule_tac x = "zgcd(n, p)" in allE)
  apply (auto simp add: zgcd_zdvd2 [of n p] zgcd_geq_zero)
  apply (insert zgcd_zdvd1 [of n p], auto)
  done

lemma zless_zprime_imp_zrelprime:
    "p \<in> zprime ==> 0 < n ==> n < p ==> zgcd (n, p) = 1"
  apply (erule zprime_imp_zrelprime)
  apply (erule zdvd_not_zless, assumption)
  done

lemma zprime_zdvd_zmult:
    "0 \<le> (m::int) ==> p \<in> zprime ==> p dvd m * n ==> p dvd m \<or> p dvd n"
  apply safe
  apply (rule zrelprime_zdvd_zmult)
   apply (rule zprime_imp_zrelprime, auto)
  done

lemma zgcd_zadd_zmult [simp]: "zgcd (m + n * k, n) = zgcd (m, n)"
  apply (rule zgcd_eq [THEN trans])
  apply (simp add: zmod_zadd1_eq)
  apply (rule zgcd_eq [symmetric])
  done

lemma zgcd_zdvd_zgcd_zmult: "zgcd (m, n) dvd zgcd (k * m, n)"
  apply (simp add: zgcd_greatest_iff)
  apply (blast intro: zdvd_trans)
  done

lemma zgcd_zmult_zdvd_zgcd:
    "zgcd (k, n) = 1 ==> zgcd (k * m, n) dvd zgcd (m, n)"
  apply (simp add: zgcd_greatest_iff)
  apply (rule_tac n = k in zrelprime_zdvd_zmult)
   prefer 2
   apply (simp add: zmult_commute)
  apply (subgoal_tac "zgcd (k, zgcd (k * m, n)) = zgcd (k * m, zgcd (k, n))")
   apply simp
  apply (simp (no_asm) add: zgcd_ac)
  done

lemma zgcd_zmult_cancel: "zgcd (k, n) = 1 ==> zgcd (k * m, n) = zgcd (m, n)"
  by (simp add: zgcd_def nat_abs_mult_distrib gcd_mult_cancel)

lemma zgcd_zgcd_zmult:
    "zgcd (k, m) = 1 ==> zgcd (n, m) = 1 ==> zgcd (k * n, m) = 1"
  by (simp add: zgcd_zmult_cancel)

lemma zdvd_iff_zgcd: "0 < m ==> (m dvd n) = (zgcd (n, m) = m)"
  apply safe
   apply (rule_tac [2] n = "zgcd (n, m)" in zdvd_trans)
    apply (rule_tac [3] zgcd_zdvd1, simp_all)
  apply (unfold dvd_def, auto)
  done


subsection {* Congruences *}

lemma zcong_1 [simp]: "[a = b] (mod 1)"
  by (unfold zcong_def, auto)

lemma zcong_refl [simp]: "[k = k] (mod m)"
  by (unfold zcong_def, auto)

lemma zcong_sym: "[a = b] (mod m) = [b = a] (mod m)"
  apply (unfold zcong_def dvd_def, auto)
   apply (rule_tac [!] x = "-k" in exI, auto)
  done

lemma zcong_zadd:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a + c = b + d] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac s = "(a - b) + (c - d)" in subst)
   apply (rule_tac [2] zdvd_zadd, auto)
  done

lemma zcong_zdiff:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a - c = b - d] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac s = "(a - b) - (c - d)" in subst)
   apply (rule_tac [2] zdvd_zdiff, auto)
  done

lemma zcong_trans:
    "[a = b] (mod m) ==> [b = c] (mod m) ==> [a = c] (mod m)"
  apply (unfold zcong_def dvd_def, auto)
  apply (rule_tac x = "k + ka" in exI)
  apply (simp add: zadd_ac zadd_zmult_distrib2)
  done

lemma zcong_zmult:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a * c = b * d] (mod m)"
  apply (rule_tac b = "b * c" in zcong_trans)
   apply (unfold zcong_def)
   apply (rule_tac s = "c * (a - b)" in subst)
    apply (rule_tac [3] s = "b * (c - d)" in subst)
     prefer 4
     apply (blast intro: zdvd_zmult)
    prefer 2
    apply (blast intro: zdvd_zmult)
   apply (simp_all add: zdiff_zmult_distrib2 zmult_commute)
  done

lemma zcong_scalar: "[a = b] (mod m) ==> [a * k = b * k] (mod m)"
  by (rule zcong_zmult, simp_all)

lemma zcong_scalar2: "[a = b] (mod m) ==> [k * a = k * b] (mod m)"
  by (rule zcong_zmult, simp_all)

lemma zcong_zmult_self: "[a * m = b * m] (mod m)"
  apply (unfold zcong_def)
  apply (rule zdvd_zdiff, simp_all)
  done

lemma zcong_square:
   "[|p \<in> zprime;  0 < a;  [a * a = 1] (mod p)|]
    ==> [a = 1] (mod p) \<or> [a = p - 1] (mod p)"
  apply (unfold zcong_def)
  apply (rule zprime_zdvd_zmult)
    apply (rule_tac [3] s = "a * a - 1 + p * (1 - a)" in subst)
     prefer 4
     apply (simp add: zdvd_reduce)
    apply (simp_all add: zdiff_zmult_distrib zmult_commute zdiff_zmult_distrib2)
  done

lemma zcong_cancel:
  "0 \<le> m ==>
    zgcd (k, m) = 1 ==> [a * k = b * k] (mod m) = [a = b] (mod m)"
  apply safe
   prefer 2
   apply (blast intro: zcong_scalar)
  apply (case_tac "b < a")
   prefer 2
   apply (subst zcong_sym)
   apply (unfold zcong_def)
   apply (rule_tac [!] zrelprime_zdvd_zmult)
     apply (simp_all add: zdiff_zmult_distrib)
  apply (subgoal_tac "m dvd (-(a * k - b * k))")
   apply (simp add: zminus_zdiff_eq)
  apply (subst zdvd_zminus_iff, assumption)
  done

lemma zcong_cancel2:
  "0 \<le> m ==>
    zgcd (k, m) = 1 ==> [k * a = k * b] (mod m) = [a = b] (mod m)"
  by (simp add: zmult_commute zcong_cancel)

lemma zcong_zgcd_zmult_zmod:
  "[a = b] (mod m) ==> [a = b] (mod n) ==> zgcd (m, n) = 1
    ==> [a = b] (mod m * n)"
  apply (unfold zcong_def dvd_def, auto)
  apply (subgoal_tac "m dvd n * ka")
   apply (subgoal_tac "m dvd ka")
    apply (case_tac [2] "0 \<le> ka")
     prefer 3
     apply (subst zdvd_zminus_iff [symmetric])
     apply (rule_tac n = n in zrelprime_zdvd_zmult)
      apply (simp add: zgcd_commute)
     apply (simp add: zmult_commute zdvd_zminus_iff)
    prefer 2
    apply (rule_tac n = n in zrelprime_zdvd_zmult)
     apply (simp add: zgcd_commute)
    apply (simp add: zmult_commute)
   apply (auto simp add: dvd_def)
  done

lemma zcong_zless_imp_eq:
  "0 \<le> a ==>
    a < m ==> 0 \<le> b ==> b < m ==> [a = b] (mod m) ==> a = b"
  apply (unfold zcong_def dvd_def, auto)
  apply (drule_tac f = "\<lambda>z. z mod m" in arg_cong)
  apply (cut_tac z = a and w = b in zless_linear, auto)
   apply (subgoal_tac [2] "(a - b) mod m = a - b")
    apply (rule_tac [3] mod_pos_pos_trivial, auto)
  apply (subgoal_tac "(m + (a - b)) mod m = m + (a - b)")
   apply (rule_tac [2] mod_pos_pos_trivial, auto)
  done

lemma zcong_square_zless:
  "p \<in> zprime ==> 0 < a ==> a < p ==>
    [a * a = 1] (mod p) ==> a = 1 \<or> a = p - 1"
  apply (cut_tac p = p and a = a in zcong_square)
     apply (simp add: zprime_def)
    apply (auto intro: zcong_zless_imp_eq)
  done

lemma zcong_not:
    "0 < a ==> a < m ==> 0 < b ==> b < a ==> \<not> [a = b] (mod m)"
  apply (unfold zcong_def)
  apply (rule zdvd_not_zless, auto)
  done

lemma zcong_zless_0:
    "0 \<le> a ==> a < m ==> [a = 0] (mod m) ==> a = 0"
  apply (unfold zcong_def dvd_def, auto)
  apply (subgoal_tac "0 < m")
   apply (simp add: int_0_le_mult_iff)
   apply (subgoal_tac "m * k < m * 1")
    apply (drule zmult_zless_cancel1 [THEN iffD1])
    apply (auto simp add: linorder_neq_iff)
  done

lemma zcong_zless_unique:
    "0 < m ==> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  apply auto
   apply (subgoal_tac [2] "[b = y] (mod m)")
    apply (case_tac [2] "b = 0")
     apply (case_tac [3] "y = 0")
      apply (auto intro: zcong_trans zcong_zless_0 zcong_zless_imp_eq order_less_le
        simp add: zcong_sym)
  apply (unfold zcong_def dvd_def)
  apply (rule_tac x = "a mod m" in exI, auto)
  apply (rule_tac x = "-(a div m)" in exI)
  apply (simp add:zdiff_eq_eq eq_zdiff_eq zadd_commute)
  done

lemma zcong_iff_lin: "([a = b] (mod m)) = (\<exists>k. b = a + m * k)"
  apply (unfold zcong_def dvd_def, auto)
   apply (rule_tac [!] x = "-k" in exI, auto)
  done

lemma zgcd_zcong_zgcd:
  "0 < m ==>
    zgcd (a, m) = 1 ==> [a = b] (mod m) ==> zgcd (b, m) = 1"
  by (auto simp add: zcong_iff_lin)

lemma zcong_zmod_aux:
     "a - b = (m::int) * (a div m - b div m) + (a mod m - b mod m)"
  by(simp add: zdiff_zmult_distrib2 zadd_zdiff_eq eq_zdiff_eq zadd_ac)

lemma zcong_zmod: "[a = b] (mod m) = [a mod m = b mod m] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac t = "a - b" in ssubst)
  apply (rule_tac "m" = m in zcong_zmod_aux)
  apply (rule trans)
   apply (rule_tac [2] k = m and m = "a div m - b div m" in zdvd_reduce)
  apply (simp add: zadd_commute)
  done

lemma zcong_zmod_eq: "0 < m ==> [a = b] (mod m) = (a mod m = b mod m)"
  apply auto
   apply (rule_tac m = m in zcong_zless_imp_eq)
       prefer 5
       apply (subst zcong_zmod [symmetric], simp_all)
  apply (unfold zcong_def dvd_def)
  apply (rule_tac x = "a div m - b div m" in exI)
  apply (rule_tac m1 = m in zcong_zmod_aux [THEN trans], auto)
  done

lemma zcong_zminus [iff]: "[a = b] (mod -m) = [a = b] (mod m)"
  by (auto simp add: zcong_def)

lemma zcong_zero [iff]: "[a = b] (mod 0) = (a = b)"
  by (auto simp add: zcong_def)

lemma "[a = b] (mod m) = (a mod m = b mod m)"
  apply (case_tac "m = 0", simp add: DIVISION_BY_ZERO)
  apply (simp add: linorder_neq_iff)
  apply (erule disjE)  
   prefer 2 apply (simp add: zcong_zmod_eq)
  txt{*Remainding case: @{term "m<0"}*}
  apply (rule_tac t = m in zminus_zminus [THEN subst])
  apply (subst zcong_zminus)
  apply (subst zcong_zmod_eq, arith)
  apply (frule neg_mod_bound [of _ a], frule neg_mod_bound [of _ b]) 
  apply (simp add: zmod_zminus2_eq_if del: neg_mod_bound)
  done

subsection {* Modulo *}

lemma zmod_zdvd_zmod:
    "0 < (m::int) ==> m dvd b ==> (a mod b mod m) = (a mod m)"
  apply (unfold dvd_def, auto)
  apply (subst zcong_zmod_eq [symmetric])
   prefer 2
   apply (subst zcong_iff_lin)
   apply (rule_tac x = "k * (a div (m * k))" in exI)
   apply (simp add:zmult_assoc [symmetric], assumption)
  done


subsection {* Extended GCD *}

declare xzgcda.simps [simp del]

lemma xzgcd_correct_aux1:
  "zgcd (r', r) = k --> 0 < r -->
    (\<exists>sn tn. xzgcda (m, n, r', r, s', s, t', t) = (k, sn, tn))"
  apply (rule_tac u = m and v = n and w = r' and x = r and y = s' and
    z = s and aa = t' and ab = t in xzgcda.induct)
  apply (subst zgcd_eq)
  apply (subst xzgcda.simps, auto)
  apply (case_tac "r' mod r = 0")
   prefer 2
   apply (frule_tac a = "r'" in pos_mod_sign, auto)
  apply (rule exI)
  apply (rule exI)
  apply (subst xzgcda.simps, auto)
  apply (simp add: zabs_def)
  done

lemma xzgcd_correct_aux2:
  "(\<exists>sn tn. xzgcda (m, n, r', r, s', s, t', t) = (k, sn, tn)) --> 0 < r -->
    zgcd (r', r) = k"
  apply (rule_tac u = m and v = n and w = r' and x = r and y = s' and
    z = s and aa = t' and ab = t in xzgcda.induct)
  apply (subst zgcd_eq)
  apply (subst xzgcda.simps)
  apply (auto simp add: linorder_not_le)
  apply (case_tac "r' mod r = 0")
   prefer 2
   apply (frule_tac a = "r'" in pos_mod_sign, auto)
  apply (erule_tac P = "xzgcda ?u = ?v" in rev_mp)
  apply (subst xzgcda.simps, auto)
  apply (simp add: zabs_def)
  done

lemma xzgcd_correct:
    "0 < n ==> (zgcd (m, n) = k) = (\<exists>s t. xzgcd m n = (k, s, t))"
  apply (unfold xzgcd_def)
  apply (rule iffI)
   apply (rule_tac [2] xzgcd_correct_aux2 [THEN mp, THEN mp])
    apply (rule xzgcd_correct_aux1 [THEN mp, THEN mp], auto)
  done


text {* \medskip @{term xzgcd} linear *}

lemma xzgcda_linear_aux1:
  "(a - r * b) * m + (c - r * d) * (n::int) =
   (a * m + c * n) - r * (b * m + d * n)"
  by (simp add: zdiff_zmult_distrib zadd_zmult_distrib2 zmult_assoc)

lemma xzgcda_linear_aux2:
  "r' = s' * m + t' * n ==> r = s * m + t * n
    ==> (r' mod r) = (s' - (r' div r) * s) * m + (t' - (r' div r) * t) * (n::int)"
  apply (rule trans)
   apply (rule_tac [2] xzgcda_linear_aux1 [symmetric])
  apply (simp add: eq_zdiff_eq zmult_commute)
  done

lemma order_le_neq_implies_less: "(x::'a::order) \<le> y ==> x \<noteq> y ==> x < y"
  by (rule iffD2 [OF order_less_le conjI])

lemma xzgcda_linear [rule_format]:
  "0 < r --> xzgcda (m, n, r', r, s', s, t', t) = (rn, sn, tn) -->
    r' = s' * m + t' * n -->  r = s * m + t * n --> rn = sn * m + tn * n"
  apply (rule_tac u = m and v = n and w = r' and x = r and y = s' and
    z = s and aa = t' and ab = t in xzgcda.induct)
  apply (subst xzgcda.simps)
  apply (simp (no_asm))
  apply (rule impI)+
  apply (case_tac "r' mod r = 0")
   apply (simp add: xzgcda.simps, clarify)
  apply (subgoal_tac "0 < r' mod r")
   apply (rule_tac [2] order_le_neq_implies_less)
   apply (rule_tac [2] pos_mod_sign)
    apply (cut_tac m = m and n = n and r' = r' and r = r and s' = s' and
      s = s and t' = t' and t = t in xzgcda_linear_aux2, auto)
  done

lemma xzgcd_linear:
    "0 < n ==> xzgcd m n = (r, s, t) ==> r = s * m + t * n"
  apply (unfold xzgcd_def)
  apply (erule xzgcda_linear, assumption, auto)
  done

lemma zgcd_ex_linear:
    "0 < n ==> zgcd (m, n) = k ==> (\<exists>s t. k = s * m + t * n)"
  apply (simp add: xzgcd_correct, safe)
  apply (rule exI)+
  apply (erule xzgcd_linear, auto)
  done

lemma zcong_lineq_ex:
    "0 < n ==> zgcd (a, n) = 1 ==> \<exists>x. [a * x = 1] (mod n)"
  apply (cut_tac m = a and n = n and k = 1 in zgcd_ex_linear, safe)
  apply (rule_tac x = s in exI)
  apply (rule_tac b = "s * a + t * n" in zcong_trans)
   prefer 2
   apply simp
  apply (unfold zcong_def)
  apply (simp (no_asm) add: zmult_commute zdvd_zminus_iff)
  done

lemma zcong_lineq_unique:
  "0 < n ==>
    zgcd (a, n) = 1 ==> \<exists>!x. 0 \<le> x \<and> x < n \<and> [a * x = b] (mod n)"
  apply auto
   apply (rule_tac [2] zcong_zless_imp_eq)
       apply (tactic {* stac (thm "zcong_cancel2" RS sym) 6 *})
         apply (rule_tac [8] zcong_trans)
          apply (simp_all (no_asm_simp))
   prefer 2
   apply (simp add: zcong_sym)
  apply (cut_tac a = a and n = n in zcong_lineq_ex, auto)
  apply (rule_tac x = "x * b mod n" in exI, safe)
    apply (simp_all (no_asm_simp))
  apply (subst zcong_zmod)
  apply (subst zmod_zmult1_eq [symmetric])
  apply (subst zcong_zmod [symmetric])
  apply (subgoal_tac "[a * x * b = 1 * b] (mod n)")
   apply (rule_tac [2] zcong_zmult)
    apply (simp_all add: zmult_assoc)
  done

end
