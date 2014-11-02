(*  Title:      HOL/Proofs/Lambda/InductTermi.thy
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen

Inductive characterization of terminating lambda terms.  Goes back to
Raamsdonk & Severi. On normalization. CWI TR CS-R9545, 1995.  Also
rediscovered by Matthes and Joachimski.
*)

section {* Inductive characterization of terminating lambda terms *}

theory InductTermi imports ListBeta begin

subsection {* Terminating lambda terms *}

inductive IT :: "dB => bool"
  where
    Var [intro]: "listsp IT rs ==> IT (Var n \<degree>\<degree> rs)"
  | Lambda [intro]: "IT r ==> IT (Abs r)"
  | Beta [intro]: "IT ((r[s/0]) \<degree>\<degree> ss) ==> IT s ==> IT ((Abs r \<degree> s) \<degree>\<degree> ss)"


subsection {* Every term in @{text "IT"} terminates *}

lemma double_induction_lemma [rule_format]:
  "termip beta s ==> \<forall>t. termip beta t -->
    (\<forall>r ss. t = r[s/0] \<degree>\<degree> ss --> termip beta (Abs r \<degree> s \<degree>\<degree> ss))"
  apply (erule accp_induct)
  apply (rule allI)
  apply (rule impI)
  apply (erule thin_rl)
  apply (erule accp_induct)
  apply clarify
  apply (rule accp.accI)
  apply (safe elim!: apps_betasE)
    apply (blast intro: subst_preserves_beta apps_preserves_beta)
   apply (blast intro: apps_preserves_beta2 subst_preserves_beta2 rtranclp_converseI
     dest: accp_downwards)  (* FIXME: acc_downwards can be replaced by acc(R ^* ) = acc(r) *)
  apply (blast dest: apps_preserves_betas)
  done

lemma IT_implies_termi: "IT t ==> termip beta t"
  apply (induct set: IT)
    apply (drule rev_predicate1D [OF _ listsp_mono [where B="termip beta"]])
    apply (fast intro!: predicate1I)
    apply (drule lists_accD)
    apply (erule accp_induct)
    apply (rule accp.accI)
    apply (blast dest: head_Var_reduction)
   apply (erule accp_induct)
   apply (rule accp.accI)
   apply blast
  apply (blast intro: double_induction_lemma)
  done


subsection {* Every terminating term is in @{text "IT"} *}

declare Var_apps_neq_Abs_apps [symmetric, simp]

lemma [simp, THEN not_sym, simp]: "Var n \<degree>\<degree> ss \<noteq> Abs r \<degree> s \<degree>\<degree> ts"
  by (simp add: foldl_Cons [symmetric] del: foldl_Cons)

lemma [simp]:
  "(Abs r \<degree> s \<degree>\<degree> ss = Abs r' \<degree> s' \<degree>\<degree> ss') = (r = r' \<and> s = s' \<and> ss = ss')"
  by (simp add: foldl_Cons [symmetric] del: foldl_Cons)

inductive_cases [elim!]:
  "IT (Var n \<degree>\<degree> ss)"
  "IT (Abs t)"
  "IT (Abs r \<degree> s \<degree>\<degree> ts)"

theorem termi_implies_IT: "termip beta r ==> IT r"
  apply (erule accp_induct)
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
   apply (drule_tac r=beta in conversepI)
   apply (drule_tac r="beta^--1" in ex_step1I, assumption)
   apply clarify
   apply (rename_tac us)
   apply (erule_tac x = "Var n \<degree>\<degree> us" in allE)
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
   apply (erule_tac x = "Abs u \<degree> t \<degree>\<degree> ss" in allE)
   apply force
   done

end
