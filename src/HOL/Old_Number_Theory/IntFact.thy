(*  Title:      HOL/Old_Number_Theory/IntFact.thy
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

section {* Factorial on integers *}

theory IntFact
imports IntPrimes
begin

text {*
  Factorial on integers and recursively defined set including all
  Integers from @{text 2} up to @{text a}.  Plus definition of product
  of finite set.

  \bigskip
*}

fun zfact :: "int => int"
  where "zfact n = (if n \<le> 0 then 1 else n * zfact (n - 1))"

fun d22set :: "int => int set"
  where "d22set a = (if 1 < a then insert a (d22set (a - 1)) else {})"


text {*
  \medskip @{term d22set} --- recursively defined set including all
  integers from @{text 2} up to @{text a}
*}

declare d22set.simps [simp del]


lemma d22set_induct:
  assumes "!!a. P {} a"
    and "!!a. 1 < (a::int) ==> P (d22set (a - 1)) (a - 1) ==> P (d22set a) a"
  shows "P (d22set u) u"
  apply (rule d22set.induct)
  apply (case_tac "1 < a")
   apply (rule_tac assms)
    apply (simp_all (no_asm_simp))
  apply (simp_all (no_asm_simp) add: d22set.simps assms)
  done

lemma d22set_g_1 [rule_format]: "b \<in> d22set a --> 1 < b"
  apply (induct a rule: d22set_induct)
   apply simp
  apply (subst d22set.simps)
  apply auto
  done

lemma d22set_le [rule_format]: "b \<in> d22set a --> b \<le> a"
  apply (induct a rule: d22set_induct)
  apply simp
   apply (subst d22set.simps)
   apply auto
  done

lemma d22set_le_swap: "a < b ==> b \<notin> d22set a"
  by (auto dest: d22set_le)

lemma d22set_mem: "1 < b \<Longrightarrow> b \<le> a \<Longrightarrow> b \<in> d22set a"
  apply (induct a rule: d22set.induct)
  apply auto
  apply (subst d22set.simps)
  apply (case_tac "b < a", auto)
  done

lemma d22set_fin: "finite (d22set a)"
  apply (induct a rule: d22set_induct)
   prefer 2
   apply (subst d22set.simps)
   apply auto
  done


declare zfact.simps [simp del]

lemma d22set_prod_zfact: "\<Prod>(d22set a) = zfact a"
  apply (induct a rule: d22set.induct)
  apply (subst d22set.simps)
  apply (subst zfact.simps)
  apply (case_tac "1 < a")
   prefer 2
   apply (simp add: d22set.simps zfact.simps)
  apply (simp add: d22set_fin d22set_le_swap)
  done

end
