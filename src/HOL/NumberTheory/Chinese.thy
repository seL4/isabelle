(*  Title:      HOL/NumberTheory/Chinese.thy
    ID:         $Id$
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* The Chinese Remainder Theorem *}

theory Chinese = IntPrimes:

text {*
  The Chinese Remainder Theorem for an arbitrary finite number of
  equations.  (The one-equation case is included in theory @{text
  IntPrimes}.  Uses functions for indexing.\footnote{Maybe @{term
  funprod} and @{term funsum} should be based on general @{term fold}
  on indices?}
*}


subsection {* Definitions *}

consts
  funprod :: "(nat => int) => nat => nat => int"
  funsum :: "(nat => int) => nat => nat => int"

primrec
  "funprod f i 0 = f i"
  "funprod f i (Suc n) = f (Suc (i + n)) * funprod f i n"

primrec
  "funsum f i 0 = f i"
  "funsum f i (Suc n) = f (Suc (i + n)) + funsum f i n"

consts
  m_cond :: "nat => (nat => int) => bool"
  km_cond :: "nat => (nat => int) => (nat => int) => bool"
  lincong_sol ::
    "nat => (nat => int) => (nat => int) => (nat => int) => int => bool"

  mhf :: "(nat => int) => nat => nat => int"
  xilin_sol ::
    "nat => nat => (nat => int) => (nat => int) => (nat => int) => int"
  x_sol :: "nat => (nat => int) => (nat => int) => (nat => int) => int"

defs
  m_cond_def:
    "m_cond n mf ==
      (\<forall>i. i \<le> n --> 0 < mf i) \<and>
      (\<forall>i j. i \<le> n \<and> j \<le> n \<and> i \<noteq> j --> zgcd (mf i, mf j) = 1)"

  km_cond_def:
    "km_cond n kf mf == \<forall>i. i \<le> n --> zgcd (kf i, mf i) = 1"

  lincong_sol_def:
    "lincong_sol n kf bf mf x == \<forall>i. i \<le> n --> zcong (kf i * x) (bf i) (mf i)"

  mhf_def:
    "mhf mf n i ==
      if i = 0 then funprod mf (Suc 0) (n - Suc 0)
      else if i = n then funprod mf 0 (n - Suc 0)
      else funprod mf 0 (i - Suc 0) * funprod mf (Suc i) (n - Suc 0 - i)"

  xilin_sol_def:
    "xilin_sol i n kf bf mf ==
      if 0 < n \<and> i \<le> n \<and> m_cond n mf \<and> km_cond n kf mf then
        (SOME x. 0 \<le> x \<and> x < mf i \<and> zcong (kf i * mhf mf n i * x) (bf i) (mf i))
      else 0"

  x_sol_def:
    "x_sol n kf bf mf == funsum (\<lambda>i. xilin_sol i n kf bf mf * mhf mf n i) 0 n"


text {* \medskip @{term funprod} and @{term funsum} *}

lemma funprod_pos: "(\<forall>i. i \<le> n --> 0 < mf i) ==> 0 < funprod mf 0 n"
  apply (induct n)
   apply auto
  apply (simp add: zero_less_mult_iff)
  done

lemma funprod_zgcd [rule_format (no_asm)]:
  "(\<forall>i. k \<le> i \<and> i \<le> k + l --> zgcd (mf i, mf m) = 1) -->
    zgcd (funprod mf k l, mf m) = 1"
  apply (induct l)
   apply simp_all
  apply (rule impI)+
  apply (subst zgcd_zmult_cancel)
  apply auto
  done

lemma funprod_zdvd [rule_format]:
    "k \<le> i --> i \<le> k + l --> mf i dvd funprod mf k l"
  apply (induct l)
   apply auto
    apply (rule_tac [2] zdvd_zmult2)
    apply (rule_tac [3] zdvd_zmult)
    apply (subgoal_tac "i = k")
    apply (subgoal_tac [3] "i = Suc (k + n)")
    apply (simp_all (no_asm_simp))
  done

lemma funsum_mod:
    "funsum f k l mod m = funsum (\<lambda>i. (f i) mod m) k l mod m"
  apply (induct l)
   apply auto
  apply (rule trans)
   apply (rule zmod_zadd1_eq)
  apply simp
  apply (rule zmod_zadd_right_eq [symmetric])
  done

lemma funsum_zero [rule_format (no_asm)]:
    "(\<forall>i. k \<le> i \<and> i \<le> k + l --> f i = 0) --> (funsum f k l) = 0"
  apply (induct l)
   apply auto
  done

lemma funsum_oneelem [rule_format (no_asm)]:
  "k \<le> j --> j \<le> k + l -->
    (\<forall>i. k \<le> i \<and> i \<le> k + l \<and> i \<noteq> j --> f i = 0) -->
    funsum f k l = f j"
  apply (induct l)
   prefer 2
   apply clarify
   defer
   apply clarify
   apply (subgoal_tac "k = j")
    apply (simp_all (no_asm_simp))
  apply (case_tac "Suc (k + n) = j")
   apply (subgoal_tac "funsum f k n = 0")
    apply (rule_tac [2] funsum_zero)
    apply (subgoal_tac [3] "f (Suc (k + n)) = 0")
     apply (subgoal_tac [3] "j \<le> k + n")
      prefer 4
      apply arith
     apply auto
  done


subsection {* Chinese: uniqueness *}

lemma zcong_funprod_aux:
  "m_cond n mf ==> km_cond n kf mf
    ==> lincong_sol n kf bf mf x ==> lincong_sol n kf bf mf y
    ==> [x = y] (mod mf n)"
  apply (unfold m_cond_def km_cond_def lincong_sol_def)
  apply (rule iffD1)
   apply (rule_tac k = "kf n" in zcong_cancel2)
    apply (rule_tac [3] b = "bf n" in zcong_trans)
     prefer 4
     apply (subst zcong_sym)
     defer
     apply (rule order_less_imp_le)
     apply simp_all
  done

lemma zcong_funprod [rule_format]:
  "m_cond n mf --> km_cond n kf mf -->
    lincong_sol n kf bf mf x --> lincong_sol n kf bf mf y -->
    [x = y] (mod funprod mf 0 n)"
  apply (induct n)
   apply (simp_all (no_asm))
   apply (blast intro: zcong_funprod_aux)
  apply (rule impI)+
  apply (rule zcong_zgcd_zmult_zmod)
    apply (blast intro: zcong_funprod_aux)
    prefer 2
    apply (subst zgcd_commute)
    apply (rule funprod_zgcd)
   apply (auto simp add: m_cond_def km_cond_def lincong_sol_def)
  done


subsection {* Chinese: existence *}

lemma unique_xi_sol:
  "0 < n ==> i \<le> n ==> m_cond n mf ==> km_cond n kf mf
    ==> \<exists>!x. 0 \<le> x \<and> x < mf i \<and> [kf i * mhf mf n i * x = bf i] (mod mf i)"
  apply (rule zcong_lineq_unique)
   apply (tactic {* stac (thm "zgcd_zmult_cancel") 2 *})
    apply (unfold m_cond_def km_cond_def mhf_def)
    apply (simp_all (no_asm_simp))
  apply safe
    apply (tactic {* stac (thm "zgcd_zmult_cancel") 3 *})
     apply (rule_tac [!] funprod_zgcd)
     apply safe
     apply simp_all
   apply (subgoal_tac "i<n")
    prefer 2
    apply arith
   apply (case_tac [2] i)
    apply simp_all
  done

lemma x_sol_lin_aux:
    "0 < n ==> i \<le> n ==> j \<le> n ==> j \<noteq> i ==> mf j dvd mhf mf n i"
  apply (unfold mhf_def)
  apply (case_tac "i = 0")
   apply (case_tac [2] "i = n")
    apply (simp_all (no_asm_simp))
    apply (case_tac [3] "j < i")
     apply (rule_tac [3] zdvd_zmult2)
     apply (rule_tac [4] zdvd_zmult)
     apply (rule_tac [!] funprod_zdvd)
          apply arith+
  done

lemma x_sol_lin:
  "0 < n ==> i \<le> n
    ==> x_sol n kf bf mf mod mf i =
      xilin_sol i n kf bf mf * mhf mf n i mod mf i"
  apply (unfold x_sol_def)
  apply (subst funsum_mod)
  apply (subst funsum_oneelem)
     apply auto
  apply (subst zdvd_iff_zmod_eq_0 [symmetric])
  apply (rule zdvd_zmult)
  apply (rule x_sol_lin_aux)
  apply auto
  done


subsection {* Chinese *}

lemma chinese_remainder:
  "0 < n ==> m_cond n mf ==> km_cond n kf mf
    ==> \<exists>!x. 0 \<le> x \<and> x < funprod mf 0 n \<and> lincong_sol n kf bf mf x"
  apply safe
   apply (rule_tac [2] m = "funprod mf 0 n" in zcong_zless_imp_eq)
       apply (rule_tac [6] zcong_funprod)
          apply auto
  apply (rule_tac x = "x_sol n kf bf mf mod funprod mf 0 n" in exI)
  apply (unfold lincong_sol_def)
  apply safe
    apply (tactic {* stac (thm "zcong_zmod") 3 *})
    apply (tactic {* stac (thm "zmod_zmult_distrib") 3 *})
    apply (tactic {* stac (thm "zmod_zdvd_zmod") 3 *})
      apply (tactic {* stac (thm "x_sol_lin") 5 *})
        apply (tactic {* stac (thm "zmod_zmult_distrib" RS sym) 7 *})
        apply (tactic {* stac (thm "zcong_zmod" RS sym) 7 *})
        apply (subgoal_tac [7]
          "0 \<le> xilin_sol i n kf bf mf \<and> xilin_sol i n kf bf mf < mf i
          \<and> [kf i * mhf mf n i * xilin_sol i n kf bf mf = bf i] (mod mf i)")
         prefer 7
         apply (simp add: zmult_ac)
        apply (unfold xilin_sol_def)
        apply (tactic {* Asm_simp_tac 7 *})
        apply (rule_tac [7] ex1_implies_ex [THEN someI_ex])
        apply (rule_tac [7] unique_xi_sol)
           apply (rule_tac [4] funprod_zdvd)
            apply (unfold m_cond_def)
            apply (rule funprod_pos [THEN pos_mod_sign])
            apply (rule_tac [2] funprod_pos [THEN pos_mod_bound])
            apply auto
  done

end
