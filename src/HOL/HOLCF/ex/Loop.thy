(*  Title:      HOL/HOLCF/ex/Loop.thy
    Author:     Franz Regensburger
*)

section \<open>Theory for a loop primitive like while\<close>

theory Loop
imports HOLCF
begin

definition
  step  :: "('a \<rightarrow> tr) \<rightarrow> ('a \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> 'a" where
  "step = (LAM b g x. If b\<cdot>x then g\<cdot>x else x)"

definition
  while :: "('a \<rightarrow> tr) \<rightarrow> ('a \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> 'a" where
  "while = (LAM b g. fix\<cdot>(LAM f x. If b\<cdot>x then f\<cdot>(g\<cdot>x) else x))"

(* ------------------------------------------------------------------------- *)
(* access to definitions                                                     *)
(* ------------------------------------------------------------------------- *)


lemma step_def2: "step\<cdot>b\<cdot>g\<cdot>x = If b\<cdot>x then g\<cdot>x else x"
apply (unfold step_def)
apply simp
done

lemma while_def2: "while\<cdot>b\<cdot>g = fix\<cdot>(LAM f x. If b\<cdot>x then f\<cdot>(g\<cdot>x) else x)"
apply (unfold while_def)
apply simp
done


(* ------------------------------------------------------------------------- *)
(* rekursive properties of while                                             *)
(* ------------------------------------------------------------------------- *)

lemma while_unfold: "while\<cdot>b\<cdot>g\<cdot>x = If b\<cdot>x then while\<cdot>b\<cdot>g\<cdot>(g\<cdot>x) else x"
apply (rule trans)
apply (rule while_def2 [THEN fix_eq5])
apply simp
done

lemma while_unfold2: "\<forall>x. while\<cdot>b\<cdot>g\<cdot>x = while\<cdot>b\<cdot>g\<cdot>(iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x)"
apply (induct_tac k)
apply simp
apply (rule allI)
apply (rule trans)
apply (rule while_unfold)
apply (subst iterate_Suc2)
apply (rule trans)
apply (erule_tac [2] spec)
apply (subst step_def2)
apply (rule_tac p = "b\<cdot>x" in trE)
apply simp
apply (subst while_unfold)
apply (rule_tac s = "UU" and t = "b\<cdot>UU" in ssubst)
apply (erule strictI)
apply simp
apply simp
apply simp
apply (subst while_unfold)
apply simp
done

lemma while_unfold3: "while\<cdot>b\<cdot>g\<cdot>x = while\<cdot>b\<cdot>g\<cdot>(step\<cdot>b\<cdot>g\<cdot>x)"
apply (rule_tac s = "while\<cdot>b\<cdot>g\<cdot>(iterate (Suc 0)\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x)" in trans)
apply (rule while_unfold2 [THEN spec])
apply simp
done


(* ------------------------------------------------------------------------- *)
(* properties of while and iterations                                        *)
(* ------------------------------------------------------------------------- *)

lemma loop_lemma1: "\<lbrakk>\<exists>y. b\<cdot>y = FF; iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x = UU\<rbrakk>
     \<Longrightarrow> iterate(Suc k)\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x = UU"
apply (simp (no_asm))
apply (rule trans)
apply (rule step_def2)
apply simp
apply (erule exE)
apply (erule flat_codom [THEN disjE])
apply simp_all
done

lemma loop_lemma2: "\<lbrakk>\<exists>y. b\<cdot>y = FF; iterate (Suc k)\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x \<noteq> UU\<rbrakk> \<Longrightarrow>
      iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x \<noteq> UU"
apply (blast intro: loop_lemma1)
done

lemma loop_lemma3 [rule_format (no_asm)]:
  "\<lbrakk>\<forall>x. INV x \<and> b\<cdot>x = TT \<and> g\<cdot>x \<noteq> UU \<longrightarrow> INV (g\<cdot>x);
         \<exists>y. b\<cdot>y = FF; INV x\<rbrakk>
      \<Longrightarrow> iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x \<noteq> UU \<longrightarrow> INV (iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x)"
apply (induct_tac "k")
apply (simp (no_asm_simp))
apply (intro strip)
apply (simp (no_asm) add: step_def2)
apply (rule_tac p = "b\<cdot>(iterate n\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x)" in trE)
apply (erule notE)
apply (simp add: step_def2)
apply (simp (no_asm_simp))
apply (rule mp)
apply (erule spec)
apply (simp (no_asm_simp) del: iterate_Suc add: loop_lemma2)
apply (rule_tac s = "iterate (Suc n)\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x"
  and t = "g\<cdot>(iterate n\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x)" in ssubst)
prefer 2 apply (assumption)
apply (simp add: step_def2)
apply (drule (1) loop_lemma2, simp)
done

lemma loop_lemma4 [rule_format]:
  "\<forall>x. b\<cdot>(iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x) = FF \<longrightarrow> while\<cdot>b\<cdot>g\<cdot>x = iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x"
apply (induct_tac k)
apply (simp (no_asm))
apply (intro strip)
apply (simplesubst while_unfold)
apply simp
apply (rule allI)
apply (simplesubst iterate_Suc2)
apply (intro strip)
apply (rule trans)
apply (rule while_unfold3)
apply simp
done

lemma loop_lemma5 [rule_format (no_asm)]:
  "\<forall>k. b\<cdot>(iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x) \<noteq> FF \<Longrightarrow>
    \<forall>m. while\<cdot>b\<cdot>g\<cdot>(iterate m\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x) = UU"
apply (simplesubst while_def2)
apply (rule fix_ind)
apply simp
apply simp
apply (rule allI)
apply (simp (no_asm))
apply (rule_tac p = "b\<cdot>(iterate m\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x)" in trE)
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply (rule_tac s = "xa\<cdot>(iterate (Suc m)\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x)" in trans)
apply (erule_tac [2] spec)
apply (rule cfun_arg_cong)
apply (rule trans)
apply (rule_tac [2] iterate_Suc [symmetric])
apply (simp add: step_def2)
apply blast
done

lemma loop_lemma6: "\<forall>k. b\<cdot>(iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x) \<noteq> FF \<Longrightarrow> while\<cdot>b\<cdot>g\<cdot>x = UU"
apply (rule_tac t = "x" in iterate_0 [THEN subst])
apply (erule loop_lemma5)
done

lemma loop_lemma7: "while\<cdot>b\<cdot>g\<cdot>x \<noteq> UU \<Longrightarrow> \<exists>k. b\<cdot>(iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x) = FF"
apply (blast intro: loop_lemma6)
done


(* ------------------------------------------------------------------------- *)
(* an invariant rule for loops                                               *)
(* ------------------------------------------------------------------------- *)

lemma loop_inv2:
"\<lbrakk>(\<forall>y. INV y \<and> b\<cdot>y = TT \<and> g\<cdot>y \<noteq> UU \<longrightarrow> INV (g\<cdot>y));
    (\<forall>y. INV y \<and> b\<cdot>y = FF \<longrightarrow> Q y);
    INV x; while\<cdot>b\<cdot>g\<cdot>x \<noteq> UU\<rbrakk> \<Longrightarrow> Q (while\<cdot>b\<cdot>g\<cdot>x)"
apply (rule_tac P = "\<lambda>k. b\<cdot>(iterate k\<cdot>(step\<cdot>b\<cdot>g)\<cdot>x) = FF" in exE)
apply (erule loop_lemma7)
apply (simplesubst loop_lemma4)
apply assumption
apply (drule spec, erule mp)
apply (rule conjI)
prefer 2 apply (assumption)
apply (rule loop_lemma3)
apply assumption
apply (blast intro: loop_lemma6)
apply assumption
apply (rotate_tac -1)
apply (simp add: loop_lemma4)
done

lemma loop_inv:
  assumes premP: "P(x)"
    and premI: "\<And>y. P y \<Longrightarrow> INV y"
    and premTT: "\<And>y. \<lbrakk>INV y; b\<cdot>y = TT; g\<cdot>y \<noteq> UU\<rbrakk> \<Longrightarrow> INV (g\<cdot>y)"
    and premFF: "\<And>y. \<lbrakk>INV y; b\<cdot>y = FF\<rbrakk> \<Longrightarrow> Q y"
    and premW: "while\<cdot>b\<cdot>g\<cdot>x \<noteq> UU"
  shows "Q (while\<cdot>b\<cdot>g\<cdot>x)"
apply (rule loop_inv2)
apply (rule_tac [3] premP [THEN premI])
apply (rule_tac [3] premW)
apply (blast intro: premTT)
apply (blast intro: premFF)
done

end
