(*  Title:      HOL/NumberTheory/IntPrimes.thy
    ID:         $Id$
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
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
  xzgcd :: "int => int => int * int * int"
  zprime :: "int set"
  zcong :: "int => int => int => bool"    ("(1[_ = _] '(mod _'))")

recdef xzgcda
  "measure ((\<lambda>(m, n, r', r, s', s, t', t). nat r)
    :: int * int * int * int *int * int * int * int => nat)"
  "xzgcda (m, n, r', r, s', s, t', t) =
    (if r \<le> #0 then (r', s', t')
     else xzgcda (m, n, r, r' mod r, s, s' - (r' div r) * s, t, t' - (r' div r) * t))"
  (hints simp: pos_mod_bound)

constdefs
  zgcd :: "int * int => int"
  "zgcd == \<lambda>(x,y). int (gcd (nat (abs x), nat (abs y)))"

defs
  xzgcd_def: "xzgcd m n == xzgcda (m, n, m, n, #1, #0, #0, #1)"
  zprime_def: "zprime == {p. #1 < p \<and> (\<forall>m. m dvd p --> m = #1 \<or> m = p)}"
  zcong_def: "[a = b] (mod m) == m dvd (a - b)"


lemma zabs_eq_iff:
    "(abs (z::int) = w) = (z = w \<and> #0 <= z \<or> z = -w \<and> z < #0)"
  apply (auto simp add: zabs_def)
  done


text {* \medskip @{term gcd} lemmas *}

lemma gcd_add1_eq: "gcd (m + k, k) = gcd (m + k, m)"
  apply (simp add: gcd_commute)
  done

lemma gcd_diff2: "m \<le> n ==> gcd (n, n - m) = gcd (n, m)"
  apply (subgoal_tac "n = m + (n - m)")
   apply (erule ssubst, rule gcd_add1_eq)
  apply simp
  done


subsection {* Divides relation *}

lemma zdvd_0_right [iff]: "(m::int) dvd #0"
  apply (unfold dvd_def)
  apply (blast intro: zmult_0_right [symmetric])
  done

lemma zdvd_0_left [iff]: "(#0 dvd (m::int)) = (m = #0)"
  apply (unfold dvd_def)
  apply auto
  done

lemma zdvd_1_left [iff]: "#1 dvd (m::int)"
  apply (unfold dvd_def)
  apply simp
  done

lemma zdvd_refl [simp]: "m dvd (m::int)"
  apply (unfold dvd_def)
  apply (blast intro: zmult_1_right [symmetric])
  done

lemma zdvd_trans: "m dvd n ==> n dvd k ==> m dvd (k::int)"
  apply (unfold dvd_def)
  apply (blast intro: zmult_assoc)
  done

lemma zdvd_zminus_iff: "(m dvd -n) = (m dvd (n::int))"
  apply (unfold dvd_def)
  apply auto
   apply (rule_tac [!] x = "-k" in exI)
  apply auto
  done

lemma zdvd_zminus2_iff: "(-m dvd n) = (m dvd (n::int))"
  apply (unfold dvd_def)
  apply auto
   apply (rule_tac [!] x = "-k" in exI)
  apply auto
  done

lemma zdvd_anti_sym:
    "#0 < m ==> #0 < n ==> m dvd n ==> n dvd m ==> m = (n::int)"
  apply (unfold dvd_def)
  apply auto
  apply (simp add: zmult_assoc zmult_eq_self_iff int_0_less_mult_iff zmult_eq_1_iff)
  done

lemma zdvd_zadd: "k dvd m ==> k dvd n ==> k dvd (m + n :: int)"
  apply (unfold dvd_def)
  apply (blast intro: zadd_zmult_distrib2 [symmetric])
  done

lemma zdvd_zdiff: "k dvd m ==> k dvd n ==> k dvd (m - n :: int)"
  apply (unfold dvd_def)
  apply (blast intro: zdiff_zmult_distrib2 [symmetric])
  done

lemma zdvd_zdiffD: "k dvd m - n ==> k dvd n ==> k dvd (m::int)"
  apply (subgoal_tac "m = n + (m - n)")
   apply (erule ssubst)
   apply (blast intro: zdvd_zadd)
  apply simp
  done

lemma zdvd_zmult: "k dvd (n::int) ==> k dvd m * n"
  apply (unfold dvd_def)
  apply (blast intro: zmult_left_commute)
  done

lemma zdvd_zmult2: "k dvd (m::int) ==> k dvd m * n"
  apply (subst zmult_commute)
  apply (erule zdvd_zmult)
  done

lemma [iff]: "(k::int) dvd m * k"
  apply (rule zdvd_zmult)
  apply (rule zdvd_refl)
  done

lemma [iff]: "(k::int) dvd k * m"
  apply (rule zdvd_zmult2)
  apply (rule zdvd_refl)
  done

lemma zdvd_zmultD2: "j * k dvd n ==> j dvd (n::int)"
  apply (unfold dvd_def)
  apply (simp add: zmult_assoc)
  apply blast
  done

lemma zdvd_zmultD: "j * k dvd n ==> k dvd (n::int)"
  apply (rule zdvd_zmultD2)
  apply (subst zmult_commute)
  apply assumption
  done

lemma zdvd_zmult_mono: "i dvd m ==> j dvd (n::int) ==> i * j dvd m * n"
  apply (unfold dvd_def)
  apply clarify
  apply (rule_tac x = "k * ka" in exI)
  apply (simp add: zmult_ac)
  done

lemma zdvd_reduce: "(k dvd n + k * m) = (k dvd (n::int))"
  apply (rule iffI)
   apply (erule_tac [2] zdvd_zadd)
   apply (subgoal_tac "n = (n + k * m) - k * m")
    apply (erule ssubst)
    apply (erule zdvd_zdiff)
    apply simp_all
  done

lemma zdvd_zmod: "f dvd m ==> f dvd (n::int) ==> f dvd m mod n"
  apply (unfold dvd_def)
  apply (auto simp add: zmod_zmult_zmult1)
  done

lemma zdvd_zmod_imp_zdvd: "k dvd m mod n ==> k dvd n ==> k dvd (m::int)"
  apply (subgoal_tac "k dvd n * (m div n) + m mod n")
   apply (simp add: zmod_zdiv_equality [symmetric])
  apply (simp add: zdvd_zadd zdvd_zmult2)
  done

lemma zdvd_iff_zmod_eq_0: "(k dvd n) = (n mod (k::int) = #0)"
  apply (unfold dvd_def)
  apply auto
  done

lemma zdvd_not_zless: "#0 < m ==> m < n ==> \<not> n dvd (m::int)"
  apply (unfold dvd_def)
  apply auto
  apply (subgoal_tac "#0 < n")
   prefer 2
   apply (blast intro: zless_trans)
  apply (simp add: int_0_less_mult_iff)
  apply (subgoal_tac "n * k < n * #1")
   apply (drule zmult_zless_cancel1 [THEN iffD1])
   apply auto
  done

lemma int_dvd_iff: "(int m dvd z) = (m dvd nat (abs z))"
  apply (auto simp add: dvd_def nat_abs_mult_distrib)
  apply (auto simp add: nat_eq_iff zabs_eq_iff)
   apply (rule_tac [2] x = "-(int k)" in exI)
  apply (auto simp add: zmult_int [symmetric])
  done

lemma dvd_int_iff: "(z dvd int m) = (nat (abs z) dvd m)"
  apply (auto simp add: dvd_def zabs_def zmult_int [symmetric])
    apply (rule_tac [3] x = "nat k" in exI)
    apply (rule_tac [2] x = "-(int k)" in exI)
    apply (rule_tac x = "nat (-k)" in exI)
    apply (cut_tac [3] k = m in int_less_0_conv)
    apply (cut_tac k = m in int_less_0_conv)
    apply (auto simp add: int_0_le_mult_iff zmult_less_0_iff
      nat_mult_distrib [symmetric] nat_eq_iff2)
  done

lemma nat_dvd_iff: "(nat z dvd m) = (if #0 \<le> z then (z dvd int m) else m = 0)"
  apply (auto simp add: dvd_def zmult_int [symmetric])
  apply (rule_tac x = "nat k" in exI)
  apply (cut_tac k = m in int_less_0_conv)
  apply (auto simp add: int_0_le_mult_iff zmult_less_0_iff
    nat_mult_distrib [symmetric] nat_eq_iff2)
  done

lemma zminus_dvd_iff [iff]: "(-z dvd w) = (z dvd (w::int))"
  apply (auto simp add: dvd_def)
   apply (rule_tac [!] x = "-k" in exI)
   apply auto
  done

lemma dvd_zminus_iff [iff]: "(z dvd -w) = (z dvd (w::int))"
  apply (auto simp add: dvd_def)
   apply (drule zminus_equation [THEN iffD1])
   apply (rule_tac [!] x = "-k" in exI)
   apply auto
  done


subsection {* Euclid's Algorithm and GCD *}

lemma zgcd_0 [simp]: "zgcd (m, #0) = abs m"
  apply (simp add: zgcd_def zabs_def)
  done

lemma zgcd_0_left [simp]: "zgcd (#0, m) = abs m"
  apply (simp add: zgcd_def zabs_def)
  done

lemma zgcd_zminus [simp]: "zgcd (-m, n) = zgcd (m, n)"
  apply (simp add: zgcd_def)
  done

lemma zgcd_zminus2 [simp]: "zgcd (m, -n) = zgcd (m, n)"
  apply (simp add: zgcd_def)
  done

lemma zgcd_non_0: "#0 < n ==> zgcd (m, n) = zgcd (n, m mod n)"
  apply (frule_tac b = n and a = m in pos_mod_sign)
  apply (simp add: zgcd_def zabs_def nat_mod_distrib)
  apply (cut_tac a = "-m" and b = n in zmod_zminus1_eq_if)
  apply (auto simp add: gcd_non_0 nat_mod_distrib [symmetric] zmod_zminus1_eq_if)
  apply (frule_tac a = m in pos_mod_bound)
  apply (simp add: nat_diff_distrib)
  apply (rule gcd_diff2)
  apply (simp add: nat_le_eq_zle)
  done

lemma zgcd_eq: "zgcd (m, n) = zgcd (n, m mod n)"
  apply (tactic {* zdiv_undefined_case_tac "n = #0" 1 *})
  apply (auto simp add: linorder_neq_iff zgcd_non_0)
  apply (cut_tac m = "-m" and n = "-n" in zgcd_non_0)
   apply auto
  done

lemma zgcd_1 [simp]: "zgcd (m, #1) = #1"
  apply (simp add: zgcd_def zabs_def)
  done

lemma zgcd_0_1_iff [simp]: "(zgcd (#0, m) = #1) = (abs m = #1)"
  apply (simp add: zgcd_def zabs_def)
  done

lemma zgcd_zdvd1 [iff]: "zgcd (m, n) dvd m"
  apply (simp add: zgcd_def zabs_def int_dvd_iff)
  done

lemma zgcd_zdvd2 [iff]: "zgcd (m, n) dvd n"
  apply (simp add: zgcd_def zabs_def int_dvd_iff)
  done

lemma zgcd_greatest_iff: "k dvd zgcd (m, n) = (k dvd m \<and> k dvd n)"
  apply (simp add: zgcd_def zabs_def int_dvd_iff dvd_int_iff nat_dvd_iff)
  done

lemma zgcd_commute: "zgcd (m, n) = zgcd (n, m)"
  apply (simp add: zgcd_def gcd_commute)
  done

lemma zgcd_1_left [simp]: "zgcd (#1, m) = #1"
  apply (simp add: zgcd_def gcd_1_left)
  done

lemma zgcd_assoc: "zgcd (zgcd (k, m), n) = zgcd (k, zgcd (m, n))"
  apply (simp add: zgcd_def gcd_assoc)
  done

lemma zgcd_left_commute: "zgcd (k, zgcd (m, n)) = zgcd (m, zgcd (k, n))"
  apply (rule zgcd_commute [THEN trans])
  apply (rule zgcd_assoc [THEN trans])
  apply (rule zgcd_commute [THEN arg_cong])
  done

lemmas zgcd_ac = zgcd_assoc zgcd_commute zgcd_left_commute
  -- {* addition is an AC-operator *}

lemma zgcd_zmult_distrib2: "#0 \<le> k ==> k * zgcd (m, n) = zgcd (k * m, k * n)"
  apply (simp del: zmult_zminus_right
    add: zmult_zminus_right [symmetric] nat_mult_distrib zgcd_def zabs_def
    zmult_less_0_iff gcd_mult_distrib2 [symmetric] zmult_int [symmetric])
  done

lemma zgcd_zmult_distrib2_abs: "zgcd (k * m, k * n) = abs k * zgcd (m, n)"
  apply (simp add: zabs_def zgcd_zmult_distrib2)
  done

lemma zgcd_self [simp]: "#0 \<le> m ==> zgcd (m, m) = m"
  apply (cut_tac k = m and m = "#1" and n = "#1" in zgcd_zmult_distrib2)
   apply simp_all
  done

lemma zgcd_zmult_eq_self [simp]: "#0 \<le> k ==> zgcd (k, k * n) = k"
  apply (cut_tac k = k and m = "#1" and n = n in zgcd_zmult_distrib2)
   apply simp_all
  done

lemma zgcd_zmult_eq_self2 [simp]: "#0 \<le> k ==> zgcd (k * n, k) = k"
  apply (cut_tac k = k and m = n and n = "#1" in zgcd_zmult_distrib2)
   apply simp_all
  done

lemma aux: "zgcd (n, k) = #1 ==> k dvd m * n ==> #0 \<le> m ==> k dvd m"
  apply (subgoal_tac "m = zgcd (m * n, m * k)")
   apply (erule ssubst, rule zgcd_greatest_iff [THEN iffD2])
   apply (simp_all add: zgcd_zmult_distrib2 [symmetric] int_0_le_mult_iff)
  done

lemma zrelprime_zdvd_zmult: "zgcd (n, k) = #1 ==> k dvd m * n ==> k dvd m"
  apply (case_tac "#0 \<le> m")
   apply (blast intro: aux)
  apply (subgoal_tac "k dvd -m")
   apply (rule_tac [2] aux)
     apply auto
  done

lemma zprime_imp_zrelprime:
    "p \<in> zprime ==> \<not> p dvd n ==> zgcd (n, p) = #1"
  apply (unfold zprime_def)
  apply auto
  done

lemma zless_zprime_imp_zrelprime:
    "p \<in> zprime ==> #0 < n ==> n < p ==> zgcd (n, p) = #1"
  apply (erule zprime_imp_zrelprime)
  apply (erule zdvd_not_zless)
  apply assumption
  done

lemma zprime_zdvd_zmult:
    "#0 \<le> (m::int) ==> p \<in> zprime ==> p dvd m * n ==> p dvd m \<or> p dvd n"
  apply safe
  apply (rule zrelprime_zdvd_zmult)
   apply (rule zprime_imp_zrelprime)
    apply auto
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
    "zgcd (k, n) = #1 ==> zgcd (k * m, n) dvd zgcd (m, n)"
  apply (simp add: zgcd_greatest_iff)
  apply (rule_tac n = k in zrelprime_zdvd_zmult)
   prefer 2
   apply (simp add: zmult_commute)
  apply (subgoal_tac "zgcd (k, zgcd (k * m, n)) = zgcd (k * m, zgcd (k, n))")
   apply simp
  apply (simp (no_asm) add: zgcd_ac)
  done

lemma zgcd_zmult_cancel: "zgcd (k, n) = #1 ==> zgcd (k * m, n) = zgcd (m, n)"
  apply (simp add: zgcd_def nat_abs_mult_distrib gcd_mult_cancel)
  done

lemma zgcd_zgcd_zmult:
    "zgcd (k, m) = #1 ==> zgcd (n, m) = #1 ==> zgcd (k * n, m) = #1"
  apply (simp (no_asm_simp) add: zgcd_zmult_cancel)
  done

lemma zdvd_iff_zgcd: "#0 < m ==> (m dvd n) = (zgcd (n, m) = m)"
  apply safe
   apply (rule_tac [2] n = "zgcd (n, m)" in zdvd_trans)
    apply (rule_tac [3] zgcd_zdvd1)
   apply simp_all
  apply (unfold dvd_def)
  apply auto
  done


subsection {* Congruences *}

lemma zcong_1 [simp]: "[a = b] (mod #1)"
  apply (unfold zcong_def)
  apply auto
  done

lemma zcong_refl [simp]: "[k = k] (mod m)"
  apply (unfold zcong_def)
  apply auto
  done

lemma zcong_sym: "[a = b] (mod m) = [b = a] (mod m)"
  apply (unfold zcong_def dvd_def)
  apply auto
   apply (rule_tac [!] x = "-k" in exI)
   apply auto
  done

lemma zcong_zadd:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a + c = b + d] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac s = "(a - b) + (c - d)" in subst)
   apply (rule_tac [2] zdvd_zadd)
    apply auto
  done

lemma zcong_zdiff:
    "[a = b] (mod m) ==> [c = d] (mod m) ==> [a - c = b - d] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac s = "(a - b) - (c - d)" in subst)
   apply (rule_tac [2] zdvd_zdiff)
    apply auto
  done

lemma zcong_trans:
    "[a = b] (mod m) ==> [b = c] (mod m) ==> [a = c] (mod m)"
  apply (unfold zcong_def dvd_def)
  apply auto
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
  apply (rule zcong_zmult)
  apply simp_all
  done

lemma zcong_scalar2: "[a = b] (mod m) ==> [k * a = k * b] (mod m)"
  apply (rule zcong_zmult)
  apply simp_all
  done

lemma zcong_zmult_self: "[a * m = b * m] (mod m)"
  apply (unfold zcong_def)
  apply (rule zdvd_zdiff)
   apply simp_all
  done

lemma zcong_square:
  "p \<in> zprime ==> #0 < a ==> [a * a = #1] (mod p)
    ==> [a = #1] (mod p) \<or> [a = p - #1] (mod p)"
  apply (unfold zcong_def)
  apply (rule zprime_zdvd_zmult)
    apply (rule_tac [3] s = "a * a - #1 + p * (#1 - a)" in subst)
     prefer 4
     apply (simp add: zdvd_reduce)
    apply (simp_all add: zdiff_zmult_distrib zmult_commute zdiff_zmult_distrib2)
  done

lemma zcong_cancel:
  "#0 \<le> m ==>
    zgcd (k, m) = #1 ==> [a * k = b * k] (mod m) = [a = b] (mod m)"
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
  apply (subst zdvd_zminus_iff)
  apply assumption
  done

lemma zcong_cancel2:
  "#0 \<le> m ==>
    zgcd (k, m) = #1 ==> [k * a = k * b] (mod m) = [a = b] (mod m)"
  apply (simp add: zmult_commute zcong_cancel)
  done

lemma zcong_zgcd_zmult_zmod:
  "[a = b] (mod m) ==> [a = b] (mod n) ==> zgcd (m, n) = #1
    ==> [a = b] (mod m * n)"
  apply (unfold zcong_def dvd_def)
  apply auto
  apply (subgoal_tac "m dvd n * ka")
   apply (subgoal_tac "m dvd ka")
    apply (case_tac [2] "#0 \<le> ka")
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
  apply (blast intro: sym)
  done

lemma zcong_zless_imp_eq:
  "#0 \<le> a ==>
    a < m ==> #0 \<le> b ==> b < m ==> [a = b] (mod m) ==> a = b"
  apply (unfold zcong_def dvd_def)
  apply auto
  apply (drule_tac f = "\<lambda>z. z mod m" in arg_cong)
  apply (cut_tac z = a and w = b in zless_linear)
  apply auto
   apply (subgoal_tac [2] "(a - b) mod m = a - b")
    apply (rule_tac [3] mod_pos_pos_trivial)
     apply auto
  apply (subgoal_tac "(m + (a - b)) mod m = m + (a - b)")
   apply (rule_tac [2] mod_pos_pos_trivial)
    apply auto
  done

lemma zcong_square_zless:
  "p \<in> zprime ==> #0 < a ==> a < p ==>
    [a * a = #1] (mod p) ==> a = #1 \<or> a = p - #1"
  apply (cut_tac p = p and a = a in zcong_square)
     apply (simp add: zprime_def)
    apply (auto intro: zcong_zless_imp_eq)
  done

lemma zcong_not:
    "#0 < a ==> a < m ==> #0 < b ==> b < a ==> \<not> [a = b] (mod m)"
  apply (unfold zcong_def)
  apply (rule zdvd_not_zless)
   apply auto
  done

lemma zcong_zless_0:
    "#0 \<le> a ==> a < m ==> [a = #0] (mod m) ==> a = #0"
  apply (unfold zcong_def dvd_def)
  apply auto
  apply (subgoal_tac "#0 < m")
   apply (rotate_tac -1)
   apply (simp add: int_0_le_mult_iff)
   apply (subgoal_tac "m * k < m * #1")
    apply (drule zmult_zless_cancel1 [THEN iffD1])
    apply (auto simp add: linorder_neq_iff)
  done

lemma zcong_zless_unique:
    "#0 < m ==> (\<exists>!b. #0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  apply auto
   apply (subgoal_tac [2] "[b = y] (mod m)")
    apply (case_tac [2] "b = #0")
     apply (case_tac [3] "y = #0")
      apply (auto intro: zcong_trans zcong_zless_0 zcong_zless_imp_eq order_less_le
        simp add: zcong_sym)
  apply (unfold zcong_def dvd_def)
  apply (rule_tac x = "a mod m" in exI)
  apply (auto simp add: pos_mod_sign pos_mod_bound)
  apply (rule_tac x = "-(a div m)" in exI)
  apply (cut_tac a = a and b = m in zmod_zdiv_equality)
  apply auto
  done

lemma zcong_iff_lin: "([a = b] (mod m)) = (\<exists>k. b = a + m * k)"
  apply (unfold zcong_def dvd_def)
  apply auto
   apply (rule_tac [!] x = "-k" in exI)
   apply auto
  done

lemma zgcd_zcong_zgcd:
  "#0 < m ==>
    zgcd (a, m) = #1 ==> [a = b] (mod m) ==> zgcd (b, m) = #1"
  apply (auto simp add: zcong_iff_lin)
  done

lemma aux: "a = c ==> b = d ==> a - b = c - (d::int)"
  apply auto
  done

lemma aux: "a - b = (m::int) * (a div m - b div m) + (a mod m - b mod m)"
  apply (rule_tac "s" = "(m * (a div m) + a mod m) - (m * (b div m) + b mod m)"
    in trans)
   prefer 2
   apply (simp add: zdiff_zmult_distrib2)
  apply (rule aux)
   apply (rule_tac [!] zmod_zdiv_equality)
  done

lemma zcong_zmod: "[a = b] (mod m) = [a mod m = b mod m] (mod m)"
  apply (unfold zcong_def)
  apply (rule_tac t = "a - b" in ssubst)
  apply (rule_tac "m" = "m" in aux)
  apply (rule trans)
   apply (rule_tac [2] k = m and m = "a div m - b div m" in zdvd_reduce)
  apply (simp add: zadd_commute)
  done

lemma zcong_zmod_eq: "#0 < m ==> [a = b] (mod m) = (a mod m = b mod m)"
  apply auto
   apply (rule_tac m = m in zcong_zless_imp_eq)
       prefer 5
       apply (subst zcong_zmod [symmetric])
       apply (simp_all add: pos_mod_bound pos_mod_sign)
  apply (unfold zcong_def dvd_def)
  apply (rule_tac x = "a div m - b div m" in exI)
  apply (rule_tac m1 = m in aux [THEN trans])
  apply auto
  done

lemma zcong_zminus [iff]: "[a = b] (mod -m) = [a = b] (mod m)"
  apply (auto simp add: zcong_def)
  done

lemma zcong_zero [iff]: "[a = b] (mod #0) = (a = b)"
  apply (auto simp add: zcong_def)
  done

lemma "[a = b] (mod m) = (a mod m = b mod m)"
  apply (tactic {* zdiv_undefined_case_tac "m = #0" 1 *})
  apply (case_tac "#0 < m")
   apply (simp add: zcong_zmod_eq)
  apply (rule_tac t = m in zminus_zminus [THEN subst])
  apply (subst zcong_zminus)
  apply (subst zcong_zmod_eq)
   apply arith
  oops  -- {* FIXME: finish this proof? *}


subsection {* Modulo *}

lemma zmod_zdvd_zmod:
    "#0 < (m::int) ==> m dvd b ==> (a mod b mod m) = (a mod m)"
  apply (unfold dvd_def)
  apply auto
  apply (subst zcong_zmod_eq [symmetric])
   prefer 2
   apply (subst zcong_iff_lin)
   apply (rule_tac x = "k * (a div (m * k))" in exI)
   apply (subst zadd_commute)
   apply (subst zmult_assoc [symmetric])
   apply (rule_tac zmod_zdiv_equality)
  apply assumption
  done


subsection {* Extended GCD *}

declare xzgcda.simps [simp del]

lemma aux1:
  "zgcd (r', r) = k --> #0 < r -->
    (\<exists>sn tn. xzgcda (m, n, r', r, s', s, t', t) = (k, sn, tn))"
  apply (rule_tac u = m and v = n and w = r' and x = r and y = s' and
    z = s and aa = t' and ab = t in xzgcda.induct)
  apply (subst zgcd_eq)
  apply (subst xzgcda.simps)
  apply auto
  apply (case_tac "r' mod r = #0")
   prefer 2
   apply (frule_tac a = "r'" in pos_mod_sign)
   apply auto
   apply arith
  apply (rule exI)
  apply (rule exI)
  apply (subst xzgcda.simps)
  apply auto
  apply (simp add: zabs_def)
  done

lemma aux2:
  "(\<exists>sn tn. xzgcda (m, n, r', r, s', s, t', t) = (k, sn, tn)) --> #0 < r -->
    zgcd (r', r) = k"
  apply (rule_tac u = m and v = n and w = r' and x = r and y = s' and
    z = s and aa = t' and ab = t in xzgcda.induct)
  apply (subst zgcd_eq)
  apply (subst xzgcda.simps)
  apply (auto simp add: linorder_not_le)
  apply (case_tac "r' mod r = #0")
   prefer 2
   apply (frule_tac a = "r'" in pos_mod_sign)
   apply auto
   apply arith
  apply (erule_tac P = "xzgcda ?u = ?v" in rev_mp)
  apply (subst xzgcda.simps)
  apply auto
  apply (simp add: zabs_def)
  done

lemma xzgcd_correct:
    "#0 < n ==> (zgcd (m, n) = k) = (\<exists>s t. xzgcd m n = (k, s, t))"
  apply (unfold xzgcd_def)
  apply (rule iffI)
   apply (rule_tac [2] aux2 [THEN mp, THEN mp])
    apply (rule aux1 [THEN mp, THEN mp])
     apply auto
  done


text {* \medskip @{term xzgcd} linear *}

lemma aux:
  "(a - r * b) * m + (c - r * d) * (n::int) =
    (a * m + c * n) - r * (b * m + d * n)"
  apply (simp add: zdiff_zmult_distrib zadd_zmult_distrib2 zmult_assoc)
  done

lemma aux:
  "r' = s' * m + t' * n ==> r = s * m + t * n
    ==> (r' mod r) = (s' - (r' div r) * s) * m + (t' - (r' div r) * t) * (n::int)"
  apply (rule trans)
   apply (rule_tac [2] aux [symmetric])
  apply simp
  apply (subst eq_zdiff_eq)
  apply (rule trans [symmetric])
  apply (rule_tac b = "s * m + t * n" in zmod_zdiv_equality)
  apply (simp add: zmult_commute)
  done

lemma order_le_neq_implies_less: "(x::'a::order) \<le> y ==> x \<noteq> y ==> x < y"
  by (rule iffD2 [OF order_less_le conjI])

lemma xzgcda_linear [rule_format]:
  "#0 < r --> xzgcda (m, n, r', r, s', s, t', t) = (rn, sn, tn) -->
    r' = s' * m + t' * n -->  r = s * m + t * n --> rn = sn * m + tn * n"
  apply (rule_tac u = m and v = n and w = r' and x = r and y = s' and
    z = s and aa = t' and ab = t in xzgcda.induct)
  apply (subst xzgcda.simps)
  apply (simp (no_asm))
  apply (rule impI)+
  apply (case_tac "r' mod r = #0")
   apply (simp add: xzgcda.simps)
   apply clarify
  apply (subgoal_tac "#0 < r' mod r")
   apply (rule_tac [2] order_le_neq_implies_less)
   apply (rule_tac [2] pos_mod_sign)
    apply (cut_tac m = m and n = n and r' = r' and r = r and s' = s' and
      s = s and t' = t' and t = t in aux)
      apply auto
  done

lemma xzgcd_linear:
    "#0 < n ==> xzgcd m n = (r, s, t) ==> r = s * m + t * n"
  apply (unfold xzgcd_def)
  apply (erule xzgcda_linear)
    apply assumption
   apply auto
  done

lemma zgcd_ex_linear:
    "#0 < n ==> zgcd (m, n) = k ==> (\<exists>s t. k = s * m + t * n)"
  apply (simp add: xzgcd_correct)
  apply safe
  apply (rule exI)+
  apply (erule xzgcd_linear)
  apply auto
  done

lemma zcong_lineq_ex:
    "#0 < n ==> zgcd (a, n) = #1 ==> \<exists>x. [a * x = #1] (mod n)"
  apply (cut_tac m = a and n = n and k = "#1" in zgcd_ex_linear)
    apply safe
  apply (rule_tac x = s in exI)
  apply (rule_tac b = "s * a + t * n" in zcong_trans)
   prefer 2
   apply simp
  apply (unfold zcong_def)
  apply (simp (no_asm) add: zmult_commute zdvd_zminus_iff)
  done

lemma zcong_lineq_unique:
  "#0 < n ==>
    zgcd (a, n) = #1 ==> \<exists>!x. #0 \<le> x \<and> x < n \<and> [a * x = b] (mod n)"
  apply auto
   apply (rule_tac [2] zcong_zless_imp_eq)
       apply (tactic {* stac (thm "zcong_cancel2" RS sym) 6 *})
         apply (rule_tac [8] zcong_trans)
          apply (simp_all (no_asm_simp))
   prefer 2
   apply (simp add: zcong_sym)
  apply (cut_tac a = a and n = n in zcong_lineq_ex)
    apply auto
  apply (rule_tac x = "x * b mod n" in exI)
  apply safe
    apply (simp_all (no_asm_simp) add: pos_mod_bound pos_mod_sign)
  apply (subst zcong_zmod)
  apply (subst zmod_zmult1_eq [symmetric])
  apply (subst zcong_zmod [symmetric])
  apply (subgoal_tac "[a * x * b = #1 * b] (mod n)")
   apply (rule_tac [2] zcong_zmult)
    apply (simp_all add: zmult_assoc)
  done

end
