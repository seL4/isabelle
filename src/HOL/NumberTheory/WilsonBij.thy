(*  Title:      HOL/NumberTheory/WilsonBij.thy
    ID:         $Id$
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* Wilson's Theorem using a more abstract approach *}

theory WilsonBij = BijectionRel + IntFact:

text {*
  Wilson's Theorem using a more ``abstract'' approach based on
  bijections between sets.  Does not use Fermat's Little Theorem
  (unlike Russinoff).
*}


subsection {* Definitions and lemmas *}

constdefs
  reciR :: "int => int => int => bool"
  "reciR p ==
    \<lambda>a b. zcong (a * b) Numeral1 p \<and> Numeral1 < a \<and> a < p - Numeral1 \<and> Numeral1 < b \<and> b < p - Numeral1"
  inv :: "int => int => int"
  "inv p a ==
    if p \<in> zprime \<and> Numeral0 < a \<and> a < p then
      (SOME x. Numeral0 \<le> x \<and> x < p \<and> zcong (a * x) Numeral1 p)
    else Numeral0"


text {* \medskip Inverse *}

lemma inv_correct:
  "p \<in> zprime ==> Numeral0 < a ==> a < p
    ==> Numeral0 \<le> inv p a \<and> inv p a < p \<and> [a * inv p a = Numeral1] (mod p)"
  apply (unfold inv_def)
  apply (simp (no_asm_simp))
  apply (rule zcong_lineq_unique [THEN ex1_implies_ex, THEN someI_ex])
   apply (erule_tac [2] zless_zprime_imp_zrelprime)
    apply (unfold zprime_def)
    apply auto
  done

lemmas inv_ge = inv_correct [THEN conjunct1, standard]
lemmas inv_less = inv_correct [THEN conjunct2, THEN conjunct1, standard]
lemmas inv_is_inv = inv_correct [THEN conjunct2, THEN conjunct2, standard]

lemma inv_not_0:
  "p \<in> zprime ==> Numeral1 < a ==> a < p - Numeral1 ==> inv p a \<noteq> Numeral0"
  -- {* same as @{text WilsonRuss} *}
  apply safe
  apply (cut_tac a = a and p = p in inv_is_inv)
     apply (unfold zcong_def)
     apply auto
  apply (subgoal_tac "\<not> p dvd Numeral1")
   apply (rule_tac [2] zdvd_not_zless)
    apply (subgoal_tac "p dvd Numeral1")
     prefer 2
     apply (subst zdvd_zminus_iff [symmetric])
     apply auto
  done

lemma inv_not_1:
  "p \<in> zprime ==> Numeral1 < a ==> a < p - Numeral1 ==> inv p a \<noteq> Numeral1"
  -- {* same as @{text WilsonRuss} *}
  apply safe
  apply (cut_tac a = a and p = p in inv_is_inv)
     prefer 4
     apply simp
     apply (subgoal_tac "a = Numeral1")
      apply (rule_tac [2] zcong_zless_imp_eq)
          apply auto
  done

lemma aux: "[a * (p - Numeral1) = Numeral1] (mod p) = [a = p - Numeral1] (mod p)"
  -- {* same as @{text WilsonRuss} *}
  apply (unfold zcong_def)
  apply (simp add: zdiff_zdiff_eq zdiff_zdiff_eq2 zdiff_zmult_distrib2)
  apply (rule_tac s = "p dvd -((a + Numeral1) + (p * -a))" in trans)
   apply (simp add: zmult_commute zminus_zdiff_eq)
  apply (subst zdvd_zminus_iff)
  apply (subst zdvd_reduce)
  apply (rule_tac s = "p dvd (a + Numeral1) + (p * -Numeral1)" in trans)
   apply (subst zdvd_reduce)
   apply auto
  done

lemma inv_not_p_minus_1:
  "p \<in> zprime ==> Numeral1 < a ==> a < p - Numeral1 ==> inv p a \<noteq> p - Numeral1"
  -- {* same as @{text WilsonRuss} *}
  apply safe
  apply (cut_tac a = a and p = p in inv_is_inv)
     apply auto
  apply (simp add: aux)
  apply (subgoal_tac "a = p - Numeral1")
   apply (rule_tac [2] zcong_zless_imp_eq)
       apply auto
  done

text {*
  Below is slightly different as we don't expand @{term [source] inv}
  but use ``@{text correct}'' theorems.
*}

lemma inv_g_1: "p \<in> zprime ==> Numeral1 < a ==> a < p - Numeral1 ==> Numeral1 < inv p a"
  apply (subgoal_tac "inv p a \<noteq> Numeral1")
   apply (subgoal_tac "inv p a \<noteq> Numeral0")
    apply (subst order_less_le)
    apply (subst zle_add1_eq_le [symmetric])
    apply (subst order_less_le)
    apply (rule_tac [2] inv_not_0)
      apply (rule_tac [5] inv_not_1)
        apply auto
  apply (rule inv_ge)
    apply auto
  done

lemma inv_less_p_minus_1:
  "p \<in> zprime ==> Numeral1 < a ==> a < p - Numeral1 ==> inv p a < p - Numeral1"
  -- {* ditto *}
  apply (subst order_less_le)
  apply (simp add: inv_not_p_minus_1 inv_less)
  done


text {* \medskip Bijection *}

lemma aux1: "Numeral1 < x ==> Numeral0 \<le> (x::int)"
  apply auto
  done

lemma aux2: "Numeral1 < x ==> Numeral0 < (x::int)"
  apply auto
  done

lemma aux3: "x \<le> p - # 2 ==> x < (p::int)"
  apply auto
  done

lemma aux4: "x \<le> p - # 2 ==> x < (p::int)-Numeral1"
  apply auto
  done

lemma inv_inj: "p \<in> zprime ==> inj_on (inv p) (d22set (p - # 2))"
  apply (unfold inj_on_def)
  apply auto
  apply (rule zcong_zless_imp_eq)
      apply (tactic {* stac (thm "zcong_cancel" RS sym) 5 *})
        apply (rule_tac [7] zcong_trans)
         apply (tactic {* stac (thm "zcong_sym") 8 *})
         apply (erule_tac [7] inv_is_inv)
          apply (tactic "Asm_simp_tac 9")
          apply (erule_tac [9] inv_is_inv)
           apply (rule_tac [6] zless_zprime_imp_zrelprime)
             apply (rule_tac [8] inv_less)
               apply (rule_tac [7] inv_g_1 [THEN aux2])
                 apply (unfold zprime_def)
                 apply (auto intro: d22set_g_1 d22set_le
		   aux1 aux2 aux3 aux4)
  done

lemma inv_d22set_d22set:
    "p \<in> zprime ==> inv p ` d22set (p - # 2) = d22set (p - # 2)"
  apply (rule endo_inj_surj)
    apply (rule d22set_fin)
   apply (erule_tac [2] inv_inj)
  apply auto
  apply (rule d22set_mem)
   apply (erule inv_g_1)
    apply (subgoal_tac [3] "inv p xa < p - Numeral1")
     apply (erule_tac [4] inv_less_p_minus_1)
      apply (auto intro: d22set_g_1 d22set_le aux4)
  done

lemma d22set_d22set_bij:
    "p \<in> zprime ==> (d22set (p - # 2), d22set (p - # 2)) \<in> bijR (reciR p)"
  apply (unfold reciR_def)
  apply (rule_tac s = "(d22set (p - # 2), inv p ` d22set (p - # 2))" in subst)
   apply (simp add: inv_d22set_d22set)
  apply (rule inj_func_bijR)
    apply (rule_tac [3] d22set_fin)
   apply (erule_tac [2] inv_inj)
  apply auto
      apply (erule inv_is_inv)
       apply (erule_tac [5] inv_g_1)
        apply (erule_tac [7] inv_less_p_minus_1)
         apply (auto intro: d22set_g_1 d22set_le aux2 aux3 aux4)
  done

lemma reciP_bijP: "p \<in> zprime ==> bijP (reciR p) (d22set (p - # 2))"
  apply (unfold reciR_def bijP_def)
  apply auto
  apply (rule d22set_mem)
   apply auto
  done

lemma reciP_uniq: "p \<in> zprime ==> uniqP (reciR p)"
  apply (unfold reciR_def uniqP_def)
  apply auto
   apply (rule zcong_zless_imp_eq)
       apply (tactic {* stac (thm "zcong_cancel2" RS sym) 5 *})
         apply (rule_tac [7] zcong_trans)
          apply (tactic {* stac (thm "zcong_sym") 8 *})
          apply (rule_tac [6] zless_zprime_imp_zrelprime)
            apply auto
  apply (rule zcong_zless_imp_eq)
      apply (tactic {* stac (thm "zcong_cancel" RS sym) 5 *})
        apply (rule_tac [7] zcong_trans)
         apply (tactic {* stac (thm "zcong_sym") 8 *})
         apply (rule_tac [6] zless_zprime_imp_zrelprime)
           apply auto
  done

lemma reciP_sym: "p \<in> zprime ==> symP (reciR p)"
  apply (unfold reciR_def symP_def)
  apply (simp add: zmult_commute)
  apply auto
  done

lemma bijER_d22set: "p \<in> zprime ==> d22set (p - # 2) \<in> bijER (reciR p)"
  apply (rule bijR_bijER)
     apply (erule d22set_d22set_bij)
    apply (erule reciP_bijP)
   apply (erule reciP_uniq)
  apply (erule reciP_sym)
  done


subsection {* Wilson *}

lemma bijER_zcong_prod_1:
    "p \<in> zprime ==> A \<in> bijER (reciR p) ==> [setprod A = Numeral1] (mod p)"
  apply (unfold reciR_def)
  apply (erule bijER.induct)
    apply (subgoal_tac [2] "a = Numeral1 \<or> a = p - Numeral1")
     apply (rule_tac [3] zcong_square_zless)
        apply auto
  apply (subst setprod_insert)
    prefer 3
    apply (subst setprod_insert)
      apply (auto simp add: fin_bijER)
  apply (subgoal_tac "zcong ((a * b) * setprod A) (Numeral1 * Numeral1) p")
   apply (simp add: zmult_assoc)
  apply (rule zcong_zmult)
   apply auto
  done

theorem Wilson_Bij: "p \<in> zprime ==> [zfact (p - Numeral1) = # -1] (mod p)"
  apply (subgoal_tac "zcong ((p - Numeral1) * zfact (p - # 2)) (# -1 * Numeral1) p")
   apply (rule_tac [2] zcong_zmult)
    apply (simp add: zprime_def)
    apply (subst zfact.simps)
    apply (rule_tac t = "p - Numeral1 - Numeral1" and s = "p - # 2" in subst)
     apply auto
   apply (simp add: zcong_def)
  apply (subst d22set_prod_zfact [symmetric])
  apply (rule bijER_zcong_prod_1)
   apply (rule_tac [2] bijER_d22set)
   apply auto
  done

end
