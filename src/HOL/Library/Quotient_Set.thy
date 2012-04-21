(*  Title:      HOL/Library/Quotient_Set.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the set type *}

theory Quotient_Set
imports Main Quotient_Syntax
begin

subsection {* set map (vimage) and set relation *}

definition "vset_rel R xs ys \<equiv> \<forall>x y. R x y \<longrightarrow> x \<in> xs \<longleftrightarrow> y \<in> ys"

lemma vset_rel_eq [id_simps]:
  "vset_rel op = = op ="
  by (subst fun_eq_iff, subst fun_eq_iff) (simp add: set_eq_iff vset_rel_def)

lemma vset_rel_equivp:
  assumes e: "equivp R"
  shows "vset_rel R xs ys \<longleftrightarrow> xs = ys \<and> (\<forall>x y. x \<in> xs \<longrightarrow> R x y \<longrightarrow> y \<in> xs)"
  unfolding vset_rel_def
  using equivp_reflp[OF e]
  by auto (metis, metis equivp_symp[OF e])

lemma set_quotient [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (vset_rel R) (vimage Rep) (vimage Abs)"
proof (rule Quotient3I)
  from assms have "\<And>x. Abs (Rep x) = x" by (rule Quotient3_abs_rep)
  then show "\<And>xs. Rep -` (Abs -` xs) = xs"
    unfolding vimage_def by auto
next
  show "\<And>xs. vset_rel R (Abs -` xs) (Abs -` xs)"
    unfolding vset_rel_def vimage_def
    by auto (metis Quotient3_rel_abs[OF assms])+
next
  fix r s
  show "vset_rel R r s = (vset_rel R r r \<and> vset_rel R s s \<and> Rep -` r = Rep -` s)"
    unfolding vset_rel_def vimage_def set_eq_iff
    by auto (metis rep_abs_rsp[OF assms] assms[simplified Quotient3_def])+
qed

declare [[mapQ3 set = (vset_rel, set_quotient)]]

lemma empty_set_rsp[quot_respect]:
  "vset_rel R {} {}"
  unfolding vset_rel_def by simp

lemma collect_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "((R ===> op =) ===> vset_rel R) Collect Collect"
  by (intro fun_relI) (simp add: fun_rel_def vset_rel_def)

lemma collect_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "((Abs ---> id) ---> op -` Rep) Collect = Collect"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF assms])

lemma union_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(vset_rel R ===> vset_rel R ===> vset_rel R) op \<union> op \<union>"
  by (intro fun_relI) (simp add: vset_rel_def)

lemma union_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(op -` Abs ---> op -` Abs ---> op -` Rep) op \<union> = op \<union>"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF set_quotient[OF assms]])

lemma diff_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(vset_rel R ===> vset_rel R ===> vset_rel R) op - op -"
  by (intro fun_relI) (simp add: vset_rel_def)

lemma diff_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(op -` Abs ---> op -` Abs ---> op -` Rep) op - = op -"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF set_quotient[OF assms]] vimage_Diff)

lemma inter_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(vset_rel R ===> vset_rel R ===> vset_rel R) op \<inter> op \<inter>"
  by (intro fun_relI) (auto simp add: vset_rel_def)

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
  shows "(R ===> vset_rel R ===> op =) op \<in> op \<in>"
  by (intro fun_relI) (simp add: vset_rel_def)

end
