(*  Title:      HOL/Library/Quotient_Set.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the set type *}

theory Quotient_Set
imports Main Quotient_Syntax
begin

subsection {* Relator for set type *}

definition set_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "set_rel R = (\<lambda>A B. (\<forall>x\<in>A. \<exists>y\<in>B. R x y) \<and> (\<forall>y\<in>B. \<exists>x\<in>A. R x y))"

lemma set_relI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y\<in>B. R x y"
  assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x\<in>A. R x y"
  shows "set_rel R A B"
  using assms unfolding set_rel_def by simp

lemma set_rel_conversep: "set_rel (conversep R) = conversep (set_rel R)"
  unfolding set_rel_def by auto

lemma set_rel_OO: "set_rel (R OO S) = set_rel R OO set_rel S"
  apply (intro ext, rename_tac X Z)
  apply (rule iffI)
  apply (rule_tac b="{y. (\<exists>x\<in>X. R x y) \<and> (\<exists>z\<in>Z. S y z)}" in relcomppI)
  apply (simp add: set_rel_def, fast)
  apply (simp add: set_rel_def, fast)
  apply (simp add: set_rel_def, fast)
  done

lemma set_rel_eq [relator_eq]: "set_rel (op =) = (op =)"
  unfolding set_rel_def fun_eq_iff by auto

lemma reflp_set_rel: "reflp R \<Longrightarrow> reflp (set_rel R)"
  unfolding reflp_def set_rel_def by fast

lemma symp_set_rel: "symp R \<Longrightarrow> symp (set_rel R)"
  unfolding symp_def set_rel_def by fast

lemma transp_set_rel: "transp R \<Longrightarrow> transp (set_rel R)"
  unfolding transp_def set_rel_def by fast

lemma equivp_set_rel: "equivp R \<Longrightarrow> equivp (set_rel R)"
  by (blast intro: equivpI reflp_set_rel symp_set_rel transp_set_rel
    elim: equivpE)

lemma right_total_set_rel [transfer_rule]:
  "right_total A \<Longrightarrow> right_total (set_rel A)"
  unfolding right_total_def set_rel_def
  by (rule allI, rename_tac Y, rule_tac x="{x. \<exists>y\<in>Y. A x y}" in exI, fast)

lemma right_unique_set_rel [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (set_rel A)"
  unfolding right_unique_def set_rel_def by fast

lemma bi_total_set_rel [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (set_rel A)"
  unfolding bi_total_def set_rel_def
  apply safe
  apply (rename_tac X, rule_tac x="{y. \<exists>x\<in>X. A x y}" in exI, fast)
  apply (rename_tac Y, rule_tac x="{x. \<exists>y\<in>Y. A x y}" in exI, fast)
  done

lemma bi_unique_set_rel [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (set_rel A)"
  unfolding bi_unique_def set_rel_def by fast

subsection {* Transfer rules for transfer package *}

subsubsection {* Unconditional transfer rules *}

lemma empty_transfer [transfer_rule]: "(set_rel A) {} {}"
  unfolding set_rel_def by simp

lemma insert_transfer [transfer_rule]:
  "(A ===> set_rel A ===> set_rel A) insert insert"
  unfolding fun_rel_def set_rel_def by auto

lemma union_transfer [transfer_rule]:
  "(set_rel A ===> set_rel A ===> set_rel A) union union"
  unfolding fun_rel_def set_rel_def by auto

lemma Union_transfer [transfer_rule]:
  "(set_rel (set_rel A) ===> set_rel A) Union Union"
  unfolding fun_rel_def set_rel_def by simp fast

lemma image_transfer [transfer_rule]:
  "((A ===> B) ===> set_rel A ===> set_rel B) image image"
  unfolding fun_rel_def set_rel_def by simp fast

lemma UNION_transfer [transfer_rule]:
  "(set_rel A ===> (A ===> set_rel B) ===> set_rel B) UNION UNION"
  unfolding SUP_def [abs_def] by transfer_prover

lemma Ball_transfer [transfer_rule]:
  "(set_rel A ===> (A ===> op =) ===> op =) Ball Ball"
  unfolding set_rel_def fun_rel_def by fast

lemma Bex_transfer [transfer_rule]:
  "(set_rel A ===> (A ===> op =) ===> op =) Bex Bex"
  unfolding set_rel_def fun_rel_def by fast

lemma Pow_transfer [transfer_rule]:
  "(set_rel A ===> set_rel (set_rel A)) Pow Pow"
  apply (rule fun_relI, rename_tac X Y, rule set_relI)
  apply (rename_tac X', rule_tac x="{y\<in>Y. \<exists>x\<in>X'. A x y}" in rev_bexI, clarsimp)
  apply (simp add: set_rel_def, fast)
  apply (rename_tac Y', rule_tac x="{x\<in>X. \<exists>y\<in>Y'. A x y}" in rev_bexI, clarsimp)
  apply (simp add: set_rel_def, fast)
  done

subsubsection {* Rules requiring bi-unique or bi-total relations *}

lemma member_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> set_rel A ===> op =) (op \<in>) (op \<in>)"
  using assms unfolding fun_rel_def set_rel_def bi_unique_def by fast

lemma Collect_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> op =) ===> set_rel A) Collect Collect"
  using assms unfolding fun_rel_def set_rel_def bi_total_def by fast

lemma inter_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(set_rel A ===> set_rel A ===> set_rel A) inter inter"
  using assms unfolding fun_rel_def set_rel_def bi_unique_def by fast

lemma Diff_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(set_rel A ===> set_rel A ===> set_rel A) (op -) (op -)"
  using assms unfolding fun_rel_def set_rel_def bi_unique_def
  unfolding Ball_def Bex_def Diff_eq
  by (safe, simp, metis, simp, metis)

lemma subset_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(set_rel A ===> set_rel A ===> op =) (op \<subseteq>) (op \<subseteq>)"
  unfolding subset_eq [abs_def] by transfer_prover

lemma UNIV_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "(set_rel A) UNIV UNIV"
  using assms unfolding set_rel_def bi_total_def by simp

lemma Compl_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(set_rel A ===> set_rel A) uminus uminus"
  unfolding Compl_eq [abs_def] by transfer_prover

lemma Inter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(set_rel (set_rel A) ===> set_rel A) Inter Inter"
  unfolding Inter_eq [abs_def] by transfer_prover

lemma finite_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(set_rel A ===> op =) finite finite"
  apply (rule fun_relI, rename_tac X Y)
  apply (rule iffI)
  apply (subgoal_tac "Y \<subseteq> (\<lambda>x. THE y. A x y) ` X")
  apply (erule finite_subset, erule finite_imageI)
  apply (rule subsetI, rename_tac y)
  apply (clarsimp simp add: set_rel_def)
  apply (drule (1) bspec, clarify)
  apply (rule image_eqI)
  apply (rule the_equality [symmetric])
  apply assumption
  apply (simp add: assms [unfolded bi_unique_def])
  apply assumption
  apply (subgoal_tac "X \<subseteq> (\<lambda>y. THE x. A x y) ` Y")
  apply (erule finite_subset, erule finite_imageI)
  apply (rule subsetI, rename_tac x)
  apply (clarsimp simp add: set_rel_def)
  apply (drule (1) bspec, clarify)
  apply (rule image_eqI)
  apply (rule the_equality [symmetric])
  apply assumption
  apply (simp add: assms [unfolded bi_unique_def])
  apply assumption
  done

subsection {* Setup for lifting package *}

lemma Quotient_set:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (set_rel R) (image Abs) (image Rep) (set_rel T)"
  using assms unfolding Quotient_alt_def4
  apply (simp add: set_rel_OO set_rel_conversep)
  apply (simp add: set_rel_def, fast)
  done

declare [[map set = (set_rel, Quotient_set)]]

lemma set_invariant_commute [invariant_commute]:
  "set_rel (Lifting.invariant P) = Lifting.invariant (\<lambda>A. Ball A P)"
  unfolding fun_eq_iff set_rel_def Lifting.invariant_def Ball_def by fast

subsection {* Contravariant set map (vimage) and set relator *}

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
