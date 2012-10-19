(*  Title:      HOL/Old_Number_Theory/IntPrimes.thy
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* Divisibility and prime numbers (on integers) *}

theory IntPrimes
imports Primes
begin

text {*
  The @{text dvd} relation, GCD, Euclid's extended algorithm, primes,
  congruences (all on the Integers).  Comparable to theory @{text
  Primes}, but @{text dvd} is included here as it is not present in
  main HOL.  Also includes extended GCD and congruences not present in
  @{text Primes}.
*}


subsection {* Definitions *}

fun xzgcda :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int => (int * int * int)"
where
  "xzgcda m n r' r s' s t' t =
        (if r \<le> 0 then (r', s', t')
         else xzgcda m n r (r' mod r) 
                      s (s' - (r' div r) * s) 
                      t (t' - (r' div r) * t))"

definition zprime :: "int \<Rightarrow> bool"
  where "zprime p = (1 < p \<and> (\<forall>m. 0 <= m & m dvd p --> m = 1 \<or> m = p))"

definition xzgcd :: "int => int => int * int * int"
  where "xzgcd m n = xzgcda m n m n 1 0 0 1"

definition zcong :: "int => int => int => bool"  ("(1[_ = _] '(mod _'))")
  where "[a = b] (mod m) = (m dvd (a - b))"


subsection {* Euclid's Algorithm and GCD *}


lemma zrelprime_zdvd_zmult_aux:
     "zgcd n k = 1 ==> k dvd m * n ==> 0 \<le> m ==> k dvd m"
    by (metis abs_of_nonneg dvd_triv_right zgcd_greatest_iff zgcd_zmult_distrib2_abs mult_1_right)

lemma zrelprime_zdvd_zmult: "zgcd n k = 1 ==> k dvd m * n ==> k dvd m"
  apply (case_tac "0 \<le> m")
   apply (blast intro: zrelprime_zdvd_zmult_aux)
  apply (subgoal_tac "k dvd -m")
   apply (rule_tac [2] zrelprime_zdvd_zmult_aux, auto)
  done

lemma zgcd_geq_zero: "0 <= zgcd x y"
  by (auto simp add: zgcd_def)

text{*This is merely a sanity check on zprime, since the previous version
      denoted the empty set.*}
lemma "zprime 2"
  apply (auto simp add: zprime_def) 
  apply (frule zdvd_imp_le, simp) 
  apply (auto simp add: order_le_less dvd_def) 
  done

lemma zprime_imp_zrelprime:
    "zprime p ==> \<not> p dvd n ==> zgcd n p = 1"
  apply (auto simp add: zprime_def)
  apply (metis zgcd_geq_zero zgcd_zdvd1 zgcd_zdvd2)
  done

lemma zless_zprime_imp_zrelprime:
    "zprime p ==> 0 < n ==> n < p ==> zgcd n p = 1"
  apply (erule zprime_imp_zrelprime)
  apply (erule zdvd_not_zless, assumption)
  done

lemma zprime_zdvd_zmult:
    "0 \<le> (m::int) ==> zprime p ==> p dvd m * n ==> p dvd m \<or> p dvd n"
  by (metis zgcd_zdvd1 zgcd_zdvd2 zgcd_pos zprime_def zrelprime_dvd_mult)

lemma zgcd_zadd_zmult [simp]: "zgcd (m + n * k) n = zgcd m n"
  apply (rule zgcd_eq [THEN trans])
  apply (simp add: mod_add_eq)
  apply (rule zgcd_eq [symmetric])
  done

lemma zgcd_zdvd_zgcd_zmult: "zgcd m n dvd zgcd (k * m) n"
by (simp add: zgcd_greatest_iff)

lemma zgcd_zmult_zdvd_zgcd:
    "zgcd k n = 1 ==> zgcd (k * m) n dvd zgcd m n"
  apply (simp add: zgcd_greatest_iff)
  apply (rule_tac n = k in zrelprime_zdvd_zmult)
   prefer 2
   apply (simp add: mult_commute)
  apply (metis zgcd_1 zgcd_commute zgcd_left_commute)
  done

lemma zgcd_zmult_cancel: "zgcd k n = 1 ==> zgcd (k * m) n = zgcd m n"
  by (simp add: zgcd_def nat_abs_mult_distrib gcd_mult_cancel)

lemma zgcd_zgcd_zmult:
    "zgcd k m = 1 ==> zgcd n m = 1 ==> zgcd (k * n) m = 1"
  by (simp add: zgcd_zmult_cancel)

lemma zdvd_iff_zgcd: "0 < m ==> m dvd n \<longleftrightarrow> zgcd n m = m"
  by (metis abs_of_pos dvd_mult_div_cancel zgcd_0 zgcd_commute zgcd_geq_zero zgcd_zdvd2 zgcd_zmult_eq_self)



subsection {* Congruences *}

lemma zcong_1 [simp]: "[a = b] (mod 1)"
  by (unfold zcong_def, auto)

lemma zcong_refl [simp]: "[k = k] (mod m)"
  by (unfold zcong_def, auto)

lemma zcong_sym: "[a = b] (mod m) = [b = a] (mod m)"
  unfolding zcong_def minus_diff_eq [of a, symmetric] dvd_minus_iff ..

lemma zcong_zadd:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a + c = b + d] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac s = "(a - b) + (c - d)" in subst)
   apply (rule_tac [2] dvd_add, auto)
  done

lemma zcong_zdiff:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a - c = b - d] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac s = "(a - b) - (c - d)" in subst)
   apply (rule_tac [2] dvd_diff, auto)
  done

lemma zcong_trans:
  "[a = b] (mod m) ==> [b = c] (mod m) ==> [a = c] (mod m)"
unfolding zcong_def by (auto elim!: dvdE simp add: algebra_simps)

lemma zcong_zmult:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a * c = b * d] (mod m)"
  apply (rule_tac b = "b * c" in zcong_trans)
   apply (unfold zcong_def)
  apply (metis right_diff_distrib dvd_mult mult_commute)
  apply (metis right_diff_distrib dvd_mult)
  done

lemma zcong_scalar: "[a = b] (mod m) ==> [a * k = b * k] (mod m)"
  by (rule zcong_zmult, simp_all)

lemma zcong_scalar2: "[a = b] (mod m) ==> [k * a = k * b] (mod m)"
  by (rule zcong_zmult, simp_all)

lemma zcong_zmult_self: "[a * m = b * m] (mod m)"
  apply (unfold zcong_def)
  apply (rule dvd_diff, simp_all)
  done

lemma zcong_square:
   "[| zprime p;  0 < a;  [a * a = 1] (mod p)|]
    ==> [a = 1] (mod p) \<or> [a = p - 1] (mod p)"
  apply (unfold zcong_def)
  apply (rule zprime_zdvd_zmult)
    apply (rule_tac [3] s = "a * a - 1 + p * (1 - a)" in subst)
     prefer 4
     apply (simp add: zdvd_reduce)
    apply (simp_all add: left_diff_distrib mult_commute right_diff_distrib)
  done

lemma zcong_cancel:
  "0 \<le> m ==>
    zgcd k m = 1 ==> [a * k = b * k] (mod m) = [a = b] (mod m)"
  apply safe
   prefer 2
   apply (blast intro: zcong_scalar)
  apply (case_tac "b < a")
   prefer 2
   apply (subst zcong_sym)
   apply (unfold zcong_def)
   apply (rule_tac [!] zrelprime_zdvd_zmult)
     apply (simp_all add: left_diff_distrib)
  apply (subgoal_tac "m dvd (-(a * k - b * k))")
   apply simp
  apply (subst dvd_minus_iff, assumption)
  done

lemma zcong_cancel2:
  "0 \<le> m ==>
    zgcd k m = 1 ==> [k * a = k * b] (mod m) = [a = b] (mod m)"
  by (simp add: mult_commute zcong_cancel)

lemma zcong_zgcd_zmult_zmod:
  "[a = b] (mod m) ==> [a = b] (mod n) ==> zgcd m n = 1
    ==> [a = b] (mod m * n)"
  apply (auto simp add: zcong_def dvd_def)
  apply (subgoal_tac "m dvd n * ka")
   apply (subgoal_tac "m dvd ka")
    apply (case_tac [2] "0 \<le> ka")
  apply (metis dvd_mult_div_cancel dvd_refl dvd_mult_left mult_commute zrelprime_zdvd_zmult)
  apply (metis abs_dvd_iff abs_of_nonneg add_0 zgcd_0_left zgcd_commute zgcd_zadd_zmult zgcd_zdvd_zgcd_zmult zgcd_zmult_distrib2_abs mult_1_right mult_commute)
  apply (metis mult_le_0_iff  zdvd_mono zdvd_mult_cancel dvd_triv_left zero_le_mult_iff order_antisym linorder_linear order_refl mult_commute zrelprime_zdvd_zmult)
  apply (metis dvd_triv_left)
  done

lemma zcong_zless_imp_eq:
  "0 \<le> a ==>
    a < m ==> 0 \<le> b ==> b < m ==> [a = b] (mod m) ==> a = b"
  apply (unfold zcong_def dvd_def, auto)
  apply (drule_tac f = "\<lambda>z. z mod m" in arg_cong)
  apply (metis diff_add_cancel mod_pos_pos_trivial add_0 add_commute zmod_eq_0_iff mod_add_right_eq)
  done

lemma zcong_square_zless:
  "zprime p ==> 0 < a ==> a < p ==>
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
  apply (metis div_pos_pos_trivial linorder_not_less div_mult_self1_is_id)
  done

lemma zcong_zless_unique:
    "0 < m ==> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  apply auto
   prefer 2 apply (metis zcong_sym zcong_trans zcong_zless_imp_eq)
  apply (unfold zcong_def dvd_def)
  apply (rule_tac x = "a mod m" in exI, auto)
  apply (metis zmult_div_cancel)
  done

lemma zcong_iff_lin: "([a = b] (mod m)) = (\<exists>k. b = a + m * k)"
  unfolding zcong_def
  apply (auto elim!: dvdE simp add: algebra_simps)
  apply (rule_tac x = "-k" in exI) apply simp
  done

lemma zgcd_zcong_zgcd:
  "0 < m ==>
    zgcd a m = 1 ==> [a = b] (mod m) ==> zgcd b m = 1"
  by (auto simp add: zcong_iff_lin)

lemma zcong_zmod_aux:
     "a - b = (m::int) * (a div m - b div m) + (a mod m - b mod m)"
  by(simp add: right_diff_distrib add_diff_eq eq_diff_eq add_ac)

lemma zcong_zmod: "[a = b] (mod m) = [a mod m = b mod m] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac t = "a - b" in ssubst)
  apply (rule_tac m = m in zcong_zmod_aux)
  apply (rule trans)
   apply (rule_tac [2] k = m and m = "a div m - b div m" in zdvd_reduce)
  apply (simp add: add_commute)
  done

lemma zcong_zmod_eq: "0 < m ==> [a = b] (mod m) = (a mod m = b mod m)"
  apply auto
  apply (metis pos_mod_conj zcong_zless_imp_eq zcong_zmod)
  apply (metis zcong_refl zcong_zmod)
  done

lemma zcong_zminus [iff]: "[a = b] (mod -m) = [a = b] (mod m)"
  by (auto simp add: zcong_def)

lemma zcong_zero [iff]: "[a = b] (mod 0) = (a = b)"
  by (auto simp add: zcong_def)

lemma "[a = b] (mod m) = (a mod m = b mod m)"
  apply (cases "m = 0", simp)
  apply (simp add: linorder_neq_iff)
  apply (erule disjE)  
   prefer 2 apply (simp add: zcong_zmod_eq)
  txt{*Remainding case: @{term "m<0"}*}
  apply (rule_tac t = m in minus_minus [THEN subst])
  apply (subst zcong_zminus)
  apply (subst zcong_zmod_eq, arith)
  apply (frule neg_mod_bound [of _ a], frule neg_mod_bound [of _ b]) 
  apply (simp add: zmod_zminus2_eq_if del: neg_mod_bound)
  done

subsection {* Modulo *}

lemma zmod_zdvd_zmod:
    "0 < (m::int) ==> m dvd b ==> (a mod b mod m) = (a mod m)"
  by (rule mod_mod_cancel) 


subsection {* Extended GCD *}

declare xzgcda.simps [simp del]

lemma xzgcd_correct_aux1:
  "zgcd r' r = k --> 0 < r -->
    (\<exists>sn tn. xzgcda m n r' r s' s t' t = (k, sn, tn))"
  apply (induct m n r' r s' s t' t rule: xzgcda.induct)
  apply (subst zgcd_eq)
  apply (subst xzgcda.simps, auto)
  apply (case_tac "r' mod r = 0")
   prefer 2
   apply (frule_tac a = "r'" in pos_mod_sign, auto)
  apply (rule exI)
  apply (rule exI)
  apply (subst xzgcda.simps, auto)
  done

lemma xzgcd_correct_aux2:
  "(\<exists>sn tn. xzgcda m n r' r s' s t' t = (k, sn, tn)) --> 0 < r -->
    zgcd r' r = k"
  apply (induct m n r' r s' s t' t rule: xzgcda.induct)
  apply (subst zgcd_eq)
  apply (subst xzgcda.simps)
  apply (auto simp add: linorder_not_le)
  apply (case_tac "r' mod r = 0")
   prefer 2
   apply (frule_tac a = "r'" in pos_mod_sign, auto)
  apply (metis Pair_eq xzgcda.simps order_refl)
  done

lemma xzgcd_correct:
    "0 < n ==> (zgcd m n = k) = (\<exists>s t. xzgcd m n = (k, s, t))"
  apply (unfold xzgcd_def)
  apply (rule iffI)
   apply (rule_tac [2] xzgcd_correct_aux2 [THEN mp, THEN mp])
    apply (rule xzgcd_correct_aux1 [THEN mp, THEN mp], auto)
  done


text {* \medskip @{term xzgcd} linear *}

lemma xzgcda_linear_aux1:
  "(a - r * b) * m + (c - r * d) * (n::int) =
   (a * m + c * n) - r * (b * m + d * n)"
  by (simp add: left_diff_distrib distrib_left mult_assoc)

lemma xzgcda_linear_aux2:
  "r' = s' * m + t' * n ==> r = s * m + t * n
    ==> (r' mod r) = (s' - (r' div r) * s) * m + (t' - (r' div r) * t) * (n::int)"
  apply (rule trans)
   apply (rule_tac [2] xzgcda_linear_aux1 [symmetric])
  apply (simp add: eq_diff_eq mult_commute)
  done

lemma order_le_neq_implies_less: "(x::'a::order) \<le> y ==> x \<noteq> y ==> x < y"
  by (rule iffD2 [OF order_less_le conjI])

lemma xzgcda_linear [rule_format]:
  "0 < r --> xzgcda m n r' r s' s t' t = (rn, sn, tn) -->
    r' = s' * m + t' * n -->  r = s * m + t * n --> rn = sn * m + tn * n"
  apply (induct m n r' r s' s t' t rule: xzgcda.induct)
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
    "0 < n ==> zgcd m n = k ==> (\<exists>s t. k = s * m + t * n)"
  apply (simp add: xzgcd_correct, safe)
  apply (rule exI)+
  apply (erule xzgcd_linear, auto)
  done

lemma zcong_lineq_ex:
    "0 < n ==> zgcd a n = 1 ==> \<exists>x. [a * x = 1] (mod n)"
  apply (cut_tac m = a and n = n and k = 1 in zgcd_ex_linear, safe)
  apply (rule_tac x = s in exI)
  apply (rule_tac b = "s * a + t * n" in zcong_trans)
   prefer 2
   apply simp
  apply (unfold zcong_def)
  apply (simp (no_asm) add: mult_commute)
  done

lemma zcong_lineq_unique:
  "0 < n ==>
    zgcd a n = 1 ==> \<exists>!x. 0 \<le> x \<and> x < n \<and> [a * x = b] (mod n)"
  apply auto
   apply (rule_tac [2] zcong_zless_imp_eq)
       apply (tactic {* stac (@{thm zcong_cancel2} RS sym) 6 *})
         apply (rule_tac [8] zcong_trans)
          apply (simp_all (no_asm_simp))
   prefer 2
   apply (simp add: zcong_sym)
  apply (cut_tac a = a and n = n in zcong_lineq_ex, auto)
  apply (rule_tac x = "x * b mod n" in exI, safe)
    apply (simp_all (no_asm_simp))
  apply (metis zcong_scalar zcong_zmod mod_mult_right_eq mult_1 mult_assoc)
  done

end
