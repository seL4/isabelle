(*  Title:      HOL/Lambda/InductTermi.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen

Inductive characterization of terminating lambda terms.  Goes back to
Raamsdonk & Severi. On normalization. CWI TR CS-R9545, 1995.  Also
rediscovered by Matthes and Joachimski.
*)

header {* Inductive characterization of terminating lambda terms *}

theory InductTermi = ListBeta:

subsection {* Terminating lambda terms *}

consts
  IT :: "dB set"

inductive IT
  intros
    Var [intro]: "rs : lists IT ==> Var n $$ rs : IT"
    Lambda [intro]: "r : IT ==> Abs r : IT"
    Beta [intro]: "(r[s/0]) $$ ss : IT ==> s : IT ==> (Abs r $ s) $$ ss : IT"


subsection {* Every term in IT terminates *}

lemma double_induction_lemma [rule_format]:
  "s : termi beta ==> \<forall>t. t : termi beta -->
    (\<forall>r ss. t = r[s/0] $$ ss --> Abs r $ s $$ ss : termi beta)"
  apply (erule acc_induct)
  apply (erule thin_rl)
  apply (rule allI)
  apply (rule impI)
  apply (erule acc_induct)
  apply clarify
  apply (rule accI)
  apply (safe elim!: apps_betasE)
     apply assumption
    apply (blast intro: subst_preserves_beta apps_preserves_beta)
   apply (blast intro: apps_preserves_beta2 subst_preserves_beta2 rtrancl_converseI
     dest: acc_downwards)  (* FIXME: acc_downwards can be replaced by acc(R ^* ) = acc(r) *)
  apply (blast dest: apps_preserves_betas)
  done

lemma IT_implies_termi: "t : IT ==> t : termi beta"
  apply (erule IT.induct)
    apply (drule rev_subsetD)
     apply (rule lists_mono)
     apply (rule Int_lower2)
    apply simp
    apply (drule lists_accD)
    apply (erule acc_induct)
    apply (rule accI)
    apply (blast dest: head_Var_reduction)
   apply (erule acc_induct)
   apply (rule accI)
   apply blast
  apply (blast intro: double_induction_lemma)
  done


subsection {* Every terminating term is in IT *}

declare Var_apps_neq_Abs_apps [THEN not_sym, simp]

lemma [simp, THEN not_sym, simp]: "Var n $$ ss \<noteq> Abs r $ s $$ ts"
  apply (simp add: foldl_Cons [symmetric] del: foldl_Cons)
  done

lemma [simp]:
  "(Abs r $ s $$ ss = Abs r' $ s' $$ ss') = (r = r' \<and> s = s' \<and> ss = ss')"
  apply (simp add: foldl_Cons [symmetric] del: foldl_Cons)
  done

inductive_cases [elim!]:
  "Var n $$ ss : IT"
  "Abs t : IT"
  "Abs r $ s $$ ts : IT"

theorem termi_implies_IT: "r : termi beta ==> r : IT"
  apply (erule acc_induct)
  apply (rename_tac r)
  apply (erule thin_rl)
  apply (erule rev_mp)
  apply simp
  apply (rule_tac t = r in Apps_dB_induct)
   apply clarify
   apply (rule IT.intros)
   apply clarify
   apply (drule bspec, assumption)
   apply (erule mp)
   apply clarify
   apply (drule converseI)
   apply (drule ex_step1I, assumption)
   apply clarify
   apply (rename_tac us)
   apply (erule_tac x = "Var n $$ us" in allE)
   apply force
   apply (rename_tac u ts)
   apply (case_tac ts)
    apply simp
    apply blast
   apply (rename_tac s ss)
   apply simp
   apply clarify
   apply (rule IT.intros)
    apply (blast intro: apps_preserves_beta)
   apply (erule mp)
   apply clarify
   apply (rename_tac t)
   apply (erule_tac x = "Abs u $ t $$ ss" in allE)
   apply force
   done

end
