(*  Title:      HOL/Library/Quotient_Set.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

section {* Quotient infrastructure for the set type *}

theory Quotient_Set
imports Main Quotient_Syntax
begin

subsection {* Contravariant set map (vimage) and set relator, rules for the Quotient package *}

definition "rel_vset R xs ys \<equiv> \<forall>x y. R x y \<longrightarrow> x \<in> xs \<longleftrightarrow> y \<in> ys"

lemma rel_vset_eq [id_simps]:
  "rel_vset op = = op ="
  by (subst fun_eq_iff, subst fun_eq_iff) (simp add: set_eq_iff rel_vset_def)

lemma rel_vset_equivp:
  assumes e: "equivp R"
  shows "rel_vset R xs ys \<longleftrightarrow> xs = ys \<and> (\<forall>x y. x \<in> xs \<longrightarrow> R x y \<longrightarrow> y \<in> xs)"
  unfolding rel_vset_def
  using equivp_reflp[OF e]
  by auto (metis, metis equivp_symp[OF e])

lemma set_quotient [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (rel_vset R) (vimage Rep) (vimage Abs)"
proof (rule Quotient3I)
  from assms have "\<And>x. Abs (Rep x) = x" by (rule Quotient3_abs_rep)
  then show "\<And>xs. Rep -` (Abs -` xs) = xs"
    unfolding vimage_def by auto
next
  show "\<And>xs. rel_vset R (Abs -` xs) (Abs -` xs)"
    unfolding rel_vset_def vimage_def
    by auto (metis Quotient3_rel_abs[OF assms])+
next
  fix r s
  show "rel_vset R r s = (rel_vset R r r \<and> rel_vset R s s \<and> Rep -` r = Rep -` s)"
    unfolding rel_vset_def vimage_def set_eq_iff
    by auto (metis rep_abs_rsp[OF assms] assms[simplified Quotient3_def])+
qed

declare [[mapQ3 set = (rel_vset, set_quotient)]]

lemma empty_set_rsp[quot_respect]:
  "rel_vset R {} {}"
  unfolding rel_vset_def by simp

lemma collect_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "((R ===> op =) ===> rel_vset R) Collect Collect"
  by (intro rel_funI) (simp add: rel_fun_def rel_vset_def)

lemma collect_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "((Abs ---> id) ---> op -` Rep) Collect = Collect"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF assms])

lemma union_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(rel_vset R ===> rel_vset R ===> rel_vset R) op \<union> op \<union>"
  by (intro rel_funI) (simp add: rel_vset_def)

lemma union_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(op -` Abs ---> op -` Abs ---> op -` Rep) op \<union> = op \<union>"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF set_quotient[OF assms]])

lemma diff_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(rel_vset R ===> rel_vset R ===> rel_vset R) op - op -"
  by (intro rel_funI) (simp add: rel_vset_def)

lemma diff_prs[quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(op -` Abs ---> op -` Abs ---> op -` Rep) op - = op -"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep[OF set_quotient[OF assms]] vimage_Diff)

lemma inter_rsp[quot_respect]:
  assumes "Quotient3 R Abs Rep"
  shows "(rel_vset R ===> rel_vset R ===> rel_vset R) op \<inter> op \<inter>"
  by (intro rel_funI) (auto simp add: rel_vset_def)

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
  shows "(R ===> rel_vset R ===> op =) op \<in> op \<in>"
  by (intro rel_funI) (simp add: rel_vset_def)

end
