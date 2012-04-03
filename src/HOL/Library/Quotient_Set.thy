(*  Title:      HOL/Library/Quotient3_Set.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the set type *}

theory Quotient_Set
imports Main Quotient_Syntax
begin

lemma set_quotient [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (set_rel R) (vimage Rep) (vimage Abs)"
proof (rule Quotient3I)
  from assms have "\<And>x. Abs (Rep x) = x" by (rule Quotient3_abs_rep)
  then show "\<And>xs. Rep -` (Abs -` xs) = xs"
    unfolding vimage_def by auto
next
  show "\<And>xs. set_rel R (Abs -` xs) (Abs -` xs)"
    unfolding set_rel_def vimage_def
    by auto (metis Quotient3_rel_abs[OF assms])+
next
  fix r s
  show "set_rel R r s = (set_rel R r r \<and> set_rel R s s \<and> Rep -` r = Rep -` s)"
    unfolding set_rel_def vimage_def set_eq_iff
    by auto (metis rep_abs_rsp[OF assms] assms[simplified Quotient3_def])+
qed

declare [[mapQ3 set = (set_rel, set_quotient)]]

lemma empty_set_rsp[quot_respect]:
  "set_rel R {} {}"
  unfolding set_rel_def by simp

lemma collect_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "((R ===> op =) ===> set_rel R) Collect Collect"
  by (intro fun_relI) (simp add: fun_rel_def set_rel_def)

lemma collect_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "((Abs ---> id) ---> op -` Rep) Collect = Collect"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF assms])

lemma union_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(set_rel R ===> set_rel R ===> set_rel R) op \<union> op \<union>"
  by (intro fun_relI) (simp add: set_rel_def)

lemma union_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(op -` Abs ---> op -` Abs ---> op -` Rep) op \<union> = op \<union>"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF set_quotient[OF assms]])

lemma diff_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(set_rel R ===> set_rel R ===> set_rel R) op - op -"
  by (intro fun_relI) (simp add: set_rel_def)

lemma diff_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(op -` Abs ---> op -` Abs ---> op -` Rep) op - = op -"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF set_quotient[OF assms]] vimage_Diff)

lemma inter_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(set_rel R ===> set_rel R ===> set_rel R) op \<inter> op \<inter>"
  by (intro fun_relI) (auto simp add: set_rel_def)

lemma inter_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(op -` Abs ---> op -` Abs ---> op -` Rep) op \<inter> = op \<inter>"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF set_quotient[OF assms]])

lemma mem_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(Rep ---> op -` Abs ---> id) op \<in> = op \<in>"
  by (simp add: fun_eq_iff Quotient3_abs_rep[OF assms])

lemma mem_rsp[quot_respect]:
  shows "(R ===> set_rel R ===> op =) op \<in> op \<in>"
  by (intro fun_relI) (simp add: set_rel_def)

end
