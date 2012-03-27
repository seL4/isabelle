(*  Title:      HOL/Old_Number_Theory/WilsonRuss.thy
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* Wilson's Theorem according to Russinoff *}

theory WilsonRuss
imports EulerFermat
begin

text {*
  Wilson's Theorem following quite closely Russinoff's approach
  using Boyer-Moore (using finite sets instead of lists, though).
*}

subsection {* Definitions and lemmas *}

definition inv :: "int => int => int"
  where "inv p a = (a^(nat (p - 2))) mod p"

fun wset :: "int \<Rightarrow> int => int set" where
  "wset a p =
    (if 1 < a then
      let ws = wset (a - 1) p
      in (if a \<in> ws then ws else insert a (insert (inv p a) ws)) else {})"


text {* \medskip @{term [source] inv} *}

lemma inv_is_inv_aux: "1 < m ==> Suc (nat (m - 2)) = nat (m - 1)"
  by (subst int_int_eq [symmetric]) auto

lemma inv_is_inv:
    "zprime p \<Longrightarrow> 0 < a \<Longrightarrow> a < p ==> [a * inv p a = 1] (mod p)"
  apply (unfold inv_def)
  apply (subst zcong_zmod)
  apply (subst mod_mult_right_eq [symmetric])
  apply (subst zcong_zmod [symmetric])
  apply (subst power_Suc [symmetric])
  apply (subst inv_is_inv_aux)
   apply (erule_tac [2] Little_Fermat)
   apply (erule_tac [2] zdvd_not_zless)
   apply (unfold zprime_def, auto)
  done

lemma inv_distinct:
    "zprime p \<Longrightarrow> 1 < a \<Longrightarrow> a < p - 1 ==> a \<noteq> inv p a"
  apply safe
  apply (cut_tac a = a and p = p in zcong_square)
     apply (cut_tac [3] a = a and p = p in inv_is_inv, auto)
   apply (subgoal_tac "a = 1")
    apply (rule_tac [2] m = p in zcong_zless_imp_eq)
        apply (subgoal_tac [7] "a = p - 1")
         apply (rule_tac [8] m = p in zcong_zless_imp_eq, auto)
  done

lemma inv_not_0:
    "zprime p \<Longrightarrow> 1 < a \<Longrightarrow> a < p - 1 ==> inv p a \<noteq> 0"
  apply safe
  apply (cut_tac a = a and p = p in inv_is_inv)
     apply (unfold zcong_def, auto)
  apply (subgoal_tac "\<not> p dvd 1")
   apply (rule_tac [2] zdvd_not_zless)
    apply (subgoal_tac "p dvd 1")
     prefer 2
     apply (subst dvd_minus_iff [symmetric], auto)
  done

lemma inv_not_1:
    "zprime p \<Longrightarrow> 1 < a \<Longrightarrow> a < p - 1 ==> inv p a \<noteq> 1"
  apply safe
  apply (cut_tac a = a and p = p in inv_is_inv)
     prefer 4
     apply simp
     apply (subgoal_tac "a = 1")
      apply (rule_tac [2] zcong_zless_imp_eq, auto)
  done

lemma inv_not_p_minus_1_aux:
    "[a * (p - 1) = 1] (mod p) = [a = p - 1] (mod p)"
  apply (unfold zcong_def)
  apply (simp add: diff_diff_eq diff_diff_eq2 right_diff_distrib)
  apply (rule_tac s = "p dvd -((a + 1) + (p * -a))" in trans)
   apply (simp add: algebra_simps)
  apply (subst dvd_minus_iff)
  apply (subst zdvd_reduce)
  apply (rule_tac s = "p dvd (a + 1) + (p * -1)" in trans)
   apply (subst zdvd_reduce, auto)
  done

lemma inv_not_p_minus_1:
    "zprime p \<Longrightarrow> 1 < a \<Longrightarrow> a < p - 1 ==> inv p a \<noteq> p - 1"
  apply safe
  apply (cut_tac a = a and p = p in inv_is_inv, auto)
  apply (simp add: inv_not_p_minus_1_aux)
  apply (subgoal_tac "a = p - 1")
   apply (rule_tac [2] zcong_zless_imp_eq, auto)
  done

lemma inv_g_1:
    "zprime p \<Longrightarrow> 1 < a \<Longrightarrow> a < p - 1 ==> 1 < inv p a"
  apply (case_tac "0\<le> inv p a")
   apply (subgoal_tac "inv p a \<noteq> 1")
    apply (subgoal_tac "inv p a \<noteq> 0")
     apply (subst order_less_le)
     apply (subst zle_add1_eq_le [symmetric])
     apply (subst order_less_le)
     apply (rule_tac [2] inv_not_0)
       apply (rule_tac [5] inv_not_1, auto)
  apply (unfold inv_def zprime_def, simp)
  done

lemma inv_less_p_minus_1:
    "zprime p \<Longrightarrow> 1 < a \<Longrightarrow> a < p - 1 ==> inv p a < p - 1"
  apply (case_tac "inv p a < p")
   apply (subst order_less_le)
   apply (simp add: inv_not_p_minus_1, auto)
  apply (unfold inv_def zprime_def, simp)
  done

lemma inv_inv_aux: "5 \<le> p ==>
    nat (p - 2) * nat (p - 2) = Suc (nat (p - 1) * nat (p - 3))"
  apply (subst int_int_eq [symmetric])
  apply (simp add: of_nat_mult)
  apply (simp add: left_diff_distrib right_diff_distrib)
  done

lemma zcong_zpower_zmult:
    "[x^y = 1] (mod p) \<Longrightarrow> [x^(y * z) = 1] (mod p)"
  apply (induct z)
   apply (auto simp add: power_add)
  apply (subgoal_tac "zcong (x^y * x^(y * z)) (1 * 1) p")
   apply (rule_tac [2] zcong_zmult, simp_all)
  done

lemma inv_inv: "zprime p \<Longrightarrow>
    5 \<le> p \<Longrightarrow> 0 < a \<Longrightarrow> a < p ==> inv p (inv p a) = a"
  apply (unfold inv_def)
  apply (subst zpower_zmod)
  apply (subst zpower_zpower)
  apply (rule zcong_zless_imp_eq)
      prefer 5
      apply (subst zcong_zmod)
      apply (subst mod_mod_trivial)
      apply (subst zcong_zmod [symmetric])
      apply (subst inv_inv_aux)
       apply (subgoal_tac [2]
         "zcong (a * a^(nat (p - 1) * nat (p - 3))) (a * 1) p")
        apply (rule_tac [3] zcong_zmult)
         apply (rule_tac [4] zcong_zpower_zmult)
         apply (erule_tac [4] Little_Fermat)
         apply (rule_tac [4] zdvd_not_zless, simp_all)
  done


text {* \medskip @{term wset} *}

declare wset.simps [simp del]

lemma wset_induct:
  assumes "!!a p. P {} a p"
    and "!!a p. 1 < (a::int) \<Longrightarrow>
      P (wset (a - 1) p) (a - 1) p ==> P (wset a p) a p"
  shows "P (wset u v) u v"
  apply (rule wset.induct)
  apply (case_tac "1 < a")
   apply (rule assms)
    apply (simp_all add: wset.simps assms)
  done

lemma wset_mem_imp_or [rule_format]:
  "1 < a \<Longrightarrow> b \<notin> wset (a - 1) p
    ==> b \<in> wset a p --> b = a \<or> b = inv p a"
  apply (subst wset.simps)
  apply (unfold Let_def, simp)
  done

lemma wset_mem_mem [simp]: "1 < a ==> a \<in> wset a p"
  apply (subst wset.simps)
  apply (unfold Let_def, simp)
  done

lemma wset_subset: "1 < a \<Longrightarrow> b \<in> wset (a - 1) p ==> b \<in> wset a p"
  apply (subst wset.simps)
  apply (unfold Let_def, auto)
  done

lemma wset_g_1 [rule_format]:
    "zprime p --> a < p - 1 --> b \<in> wset a p --> 1 < b"
  apply (induct a p rule: wset_induct, auto)
  apply (case_tac "b = a")
   apply (case_tac [2] "b = inv p a")
    apply (subgoal_tac [3] "b = a \<or> b = inv p a")
     apply (rule_tac [4] wset_mem_imp_or)
       prefer 2
       apply simp
       apply (rule inv_g_1, auto)
  done

lemma wset_less [rule_format]:
    "zprime p --> a < p - 1 --> b \<in> wset a p --> b < p - 1"
  apply (induct a p rule: wset_induct, auto)
  apply (case_tac "b = a")
   apply (case_tac [2] "b = inv p a")
    apply (subgoal_tac [3] "b = a \<or> b = inv p a")
     apply (rule_tac [4] wset_mem_imp_or)
       prefer 2
       apply simp
       apply (rule inv_less_p_minus_1, auto)
  done

lemma wset_mem [rule_format]:
  "zprime p -->
    a < p - 1 --> 1 < b --> b \<le> a --> b \<in> wset a p"
  apply (induct a p rule: wset.induct, auto)
  apply (rule_tac wset_subset)
  apply (simp (no_asm_simp))
  apply auto
  done

lemma wset_mem_inv_mem [rule_format]:
  "zprime p --> 5 \<le> p --> a < p - 1 --> b \<in> wset a p
    --> inv p b \<in> wset a p"
  apply (induct a p rule: wset_induct, auto)
   apply (case_tac "b = a")
    apply (subst wset.simps)
    apply (unfold Let_def)
    apply (rule_tac [3] wset_subset, auto)
  apply (case_tac "b = inv p a")
   apply (simp (no_asm_simp))
   apply (subst inv_inv)
       apply (subgoal_tac [6] "b = a \<or> b = inv p a")
        apply (rule_tac [7] wset_mem_imp_or, auto)
  done

lemma wset_inv_mem_mem:
  "zprime p \<Longrightarrow> 5 \<le> p \<Longrightarrow> a < p - 1 \<Longrightarrow> 1 < b \<Longrightarrow> b < p - 1
    \<Longrightarrow> inv p b \<in> wset a p \<Longrightarrow> b \<in> wset a p"
  apply (rule_tac s = "inv p (inv p b)" and t = b in subst)
   apply (rule_tac [2] wset_mem_inv_mem)
      apply (rule inv_inv, simp_all)
  done

lemma wset_fin: "finite (wset a p)"
  apply (induct a p rule: wset_induct)
   prefer 2
   apply (subst wset.simps)
   apply (unfold Let_def, auto)
  done

lemma wset_zcong_prod_1 [rule_format]:
  "zprime p -->
    5 \<le> p --> a < p - 1 --> [(\<Prod>x\<in>wset a p. x) = 1] (mod p)"
  apply (induct a p rule: wset_induct)
   prefer 2
   apply (subst wset.simps)
   apply (auto, unfold Let_def, auto)
  apply (subst setprod_insert)
    apply (tactic {* stac @{thm setprod_insert} 3 *})
      apply (subgoal_tac [5]
        "zcong (a * inv p a * (\<Prod>x\<in>wset (a - 1) p. x)) (1 * 1) p")
       prefer 5
       apply (simp add: mult_assoc)
      apply (rule_tac [5] zcong_zmult)
       apply (rule_tac [5] inv_is_inv)
         apply (tactic "clarify_tac @{context} 4")
         apply (subgoal_tac [4] "a \<in> wset (a - 1) p")
          apply (rule_tac [5] wset_inv_mem_mem)
               apply (simp_all add: wset_fin)
  apply (rule inv_distinct, auto)
  done

lemma d22set_eq_wset: "zprime p ==> d22set (p - 2) = wset (p - 2) p"
  apply safe
   apply (erule wset_mem)
     apply (rule_tac [2] d22set_g_1)
     apply (rule_tac [3] d22set_le)
     apply (rule_tac [4] d22set_mem)
      apply (erule_tac [4] wset_g_1)
       prefer 6
       apply (subst zle_add1_eq_le [symmetric])
       apply (subgoal_tac "p - 2 + 1 = p - 1")
        apply (simp (no_asm_simp))
        apply (erule wset_less, auto)
  done


subsection {* Wilson *}

lemma prime_g_5: "zprime p \<Longrightarrow> p \<noteq> 2 \<Longrightarrow> p \<noteq> 3 ==> 5 \<le> p"
  apply (unfold zprime_def dvd_def)
  apply (case_tac "p = 4", auto)
   apply (rule notE)
    prefer 2
    apply assumption
   apply (simp (no_asm))
   apply (rule_tac x = 2 in exI)
   apply (safe, arith)
     apply (rule_tac x = 2 in exI, auto)
  done

theorem Wilson_Russ:
    "zprime p ==> [zfact (p - 1) = -1] (mod p)"
  apply (subgoal_tac "[(p - 1) * zfact (p - 2) = -1 * 1] (mod p)")
   apply (rule_tac [2] zcong_zmult)
    apply (simp only: zprime_def)
    apply (subst zfact.simps)
    apply (rule_tac t = "p - 1 - 1" and s = "p - 2" in subst, auto)
   apply (simp only: zcong_def)
   apply (simp (no_asm_simp))
  apply (case_tac "p = 2")
   apply (simp add: zfact.simps)
  apply (case_tac "p = 3")
   apply (simp add: zfact.simps)
  apply (subgoal_tac "5 \<le> p")
   apply (erule_tac [2] prime_g_5)
    apply (subst d22set_prod_zfact [symmetric])
    apply (subst d22set_eq_wset)
     apply (rule_tac [2] wset_zcong_prod_1, auto)
  done

end
