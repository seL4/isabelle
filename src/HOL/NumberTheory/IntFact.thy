(*  Title:      HOL/NumberTheory/IntFact.thy
    ID:         $Id$
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* Factorial on integers *}

theory IntFact = IntPrimes:

text {*
  Factorial on integers and recursively defined set including all
  Integers from @{term 2} up to @{term a}.  Plus definition of product
  of finite set.

  \bigskip
*}

consts
  zfact :: "int => int"
  setprod :: "int set => int"
  d22set :: "int => int set"

recdef zfact  "measure ((\<lambda>n. nat n) :: int => nat)"
  "zfact n = (if n \<le> #0 then #1 else n * zfact (n - #1))"

defs
  setprod_def: "setprod A == (if finite A then fold (op *) #1 A else #1)"

recdef d22set  "measure ((\<lambda>a. nat a) :: int => nat)"
  "d22set a = (if #1 < a then insert a (d22set (a - #1)) else {})"


text {* \medskip @{term setprod} --- product of finite set *}

lemma setprod_empty [simp]: "setprod {} = #1"
  apply (simp add: setprod_def)
  done

lemma setprod_insert [simp]:
    "finite A ==> a \<notin> A ==> setprod (insert a A) = a * setprod A"
  apply (unfold setprod_def)
  apply (simp add: zmult_left_commute fold_insert [standard])
  done


text {*
  \medskip @{term d22set} --- recursively defined set including all
  integers from @{term 2} up to @{term a}
*}

declare d22set.simps [simp del]


lemma d22set_induct:
  "(!!a. P {} a) ==>
    (!!a. #1 < (a::int) ==> P (d22set (a - #1)) (a - #1)
      ==> P (d22set a) a)
    ==> P (d22set u) u"
proof -
  case rule_context
  show ?thesis
    apply (rule d22set.induct)
    apply safe
     apply (case_tac [2] "#1 < a")
      apply (rule_tac [2] rule_context)
       apply (simp_all (no_asm_simp))
     apply (simp_all (no_asm_simp) add: d22set.simps rule_context)
    done
qed

lemma d22set_g_1 [rule_format]: "b \<in> d22set a --> #1 < b"
  apply (induct a rule: d22set_induct)
   prefer 2
   apply (subst d22set.simps)
   apply auto
  done

lemma d22set_le [rule_format]: "b \<in> d22set a --> b \<le> a"
  apply (induct a rule: d22set_induct)
   prefer 2
   apply (subst d22set.simps)
   apply auto
  done

lemma d22set_le_swap: "a < b ==> b \<notin> d22set a"
  apply (auto dest: d22set_le)
  done

lemma d22set_mem [rule_format]: "#1 < b --> b \<le> a --> b \<in> d22set a"
  apply (induct a rule: d22set.induct)
  apply auto
   apply (simp_all add: d22set.simps)
  done

lemma d22set_fin: "finite (d22set a)"
  apply (induct a rule: d22set_induct)
   prefer 2
   apply (subst d22set.simps)
   apply auto
  done


declare zfact.simps [simp del]

lemma d22set_prod_zfact: "setprod (d22set a) = zfact a"
  apply (induct a rule: d22set.induct)
  apply safe
   apply (simp add: d22set.simps zfact.simps)
  apply (subst d22set.simps)
  apply (subst zfact.simps)
  apply (case_tac "#1 < a")
   prefer 2
   apply (simp add: d22set.simps zfact.simps)
  apply (simp add: d22set_fin d22set_le_swap)
  done

end
