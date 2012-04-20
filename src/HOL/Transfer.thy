(*  Title:      HOL/Transfer.thy
    Author:     Brian Huffman, TU Muenchen
*)

header {* Generic theorem transfer using relations *}

theory Transfer
imports Plain Hilbert_Choice
uses ("Tools/transfer.ML")
begin

subsection {* Relator for function space *}

definition
  fun_rel :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> bool" (infixr "===>" 55)
where
  "fun_rel A B = (\<lambda>f g. \<forall>x y. A x y \<longrightarrow> B (f x) (g y))"

lemma fun_relI [intro]:
  assumes "\<And>x y. A x y \<Longrightarrow> B (f x) (g y)"
  shows "(A ===> B) f g"
  using assms by (simp add: fun_rel_def)

lemma fun_relD:
  assumes "(A ===> B) f g" and "A x y"
  shows "B (f x) (g y)"
  using assms by (simp add: fun_rel_def)

lemma fun_relE:
  assumes "(A ===> B) f g" and "A x y"
  obtains "B (f x) (g y)"
  using assms by (simp add: fun_rel_def)

lemma fun_rel_eq:
  shows "((op =) ===> (op =)) = (op =)"
  by (auto simp add: fun_eq_iff elim: fun_relE)

lemma fun_rel_eq_rel:
  shows "((op =) ===> R) = (\<lambda>f g. \<forall>x. R (f x) (g x))"
  by (simp add: fun_rel_def)


subsection {* Transfer method *}

text {* Explicit tags for application, abstraction, and relation
membership allow for backward proof methods. *}

definition App :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "App f \<equiv> f"

definition Abs :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "Abs f \<equiv> f"

definition Rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  where "Rel r \<equiv> r"

text {* Handling of meta-logic connectives *}

definition transfer_forall where
  "transfer_forall \<equiv> All"

definition transfer_implies where
  "transfer_implies \<equiv> op \<longrightarrow>"

definition transfer_bforall :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transfer_bforall \<equiv> (\<lambda>P Q. \<forall>x. P x \<longrightarrow> Q x)"

lemma transfer_forall_eq: "(\<And>x. P x) \<equiv> Trueprop (transfer_forall (\<lambda>x. P x))"
  unfolding atomize_all transfer_forall_def ..

lemma transfer_implies_eq: "(A \<Longrightarrow> B) \<equiv> Trueprop (transfer_implies A B)"
  unfolding atomize_imp transfer_implies_def ..

lemma transfer_bforall_unfold:
  "Trueprop (transfer_bforall P (\<lambda>x. Q x)) \<equiv> (\<And>x. P x \<Longrightarrow> Q x)"
  unfolding transfer_bforall_def atomize_imp atomize_all ..

lemma transfer_start: "\<lbrakk>Rel (op =) P Q; P\<rbrakk> \<Longrightarrow> Q"
  unfolding Rel_def by simp

lemma transfer_start': "\<lbrakk>Rel (op \<longrightarrow>) P Q; P\<rbrakk> \<Longrightarrow> Q"
  unfolding Rel_def by simp

lemma transfer_prover_start: "\<lbrakk>x = x'; Rel R x' y\<rbrakk> \<Longrightarrow> Rel R x y"
  by simp

lemma Rel_eq_refl: "Rel (op =) x x"
  unfolding Rel_def ..

lemma Rel_App:
  assumes "Rel (A ===> B) f g" and "Rel A x y"
  shows "Rel B (App f x) (App g y)"
  using assms unfolding Rel_def App_def fun_rel_def by fast

lemma Rel_Abs:
  assumes "\<And>x y. Rel A x y \<Longrightarrow> Rel B (f x) (g y)"
  shows "Rel (A ===> B) (Abs (\<lambda>x. f x)) (Abs (\<lambda>y. g y))"
  using assms unfolding Rel_def Abs_def fun_rel_def by fast

use "Tools/transfer.ML"

setup Transfer.setup

declare fun_rel_eq [relator_eq]

hide_const (open) App Abs Rel


subsection {* Predicates on relations, i.e. ``class constraints'' *}

definition right_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "right_total R \<longleftrightarrow> (\<forall>y. \<exists>x. R x y)"

definition right_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "right_unique R \<longleftrightarrow> (\<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z)"

definition bi_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_total R \<longleftrightarrow> (\<forall>x. \<exists>y. R x y) \<and> (\<forall>y. \<exists>x. R x y)"

definition bi_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_unique R \<longleftrightarrow>
    (\<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z) \<and>
    (\<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y)"

lemma right_total_alt_def:
  "right_total R \<longleftrightarrow> ((R ===> op \<longrightarrow>) ===> op \<longrightarrow>) All All"
  unfolding right_total_def fun_rel_def
  apply (rule iffI, fast)
  apply (rule allI)
  apply (drule_tac x="\<lambda>x. True" in spec)
  apply (drule_tac x="\<lambda>y. \<exists>x. R x y" in spec)
  apply fast
  done

lemma right_unique_alt_def:
  "right_unique R \<longleftrightarrow> (R ===> R ===> op \<longrightarrow>) (op =) (op =)"
  unfolding right_unique_def fun_rel_def by auto

lemma bi_total_alt_def:
  "bi_total R \<longleftrightarrow> ((R ===> op =) ===> op =) All All"
  unfolding bi_total_def fun_rel_def
  apply (rule iffI, fast)
  apply safe
  apply (drule_tac x="\<lambda>x. \<exists>y. R x y" in spec)
  apply (drule_tac x="\<lambda>y. True" in spec)
  apply fast
  apply (drule_tac x="\<lambda>x. True" in spec)
  apply (drule_tac x="\<lambda>y. \<exists>x. R x y" in spec)
  apply fast
  done

lemma bi_unique_alt_def:
  "bi_unique R \<longleftrightarrow> (R ===> R ===> op =) (op =) (op =)"
  unfolding bi_unique_def fun_rel_def by auto


subsection {* Properties of relators *}

lemma right_total_eq [transfer_rule]: "right_total (op =)"
  unfolding right_total_def by simp

lemma right_unique_eq [transfer_rule]: "right_unique (op =)"
  unfolding right_unique_def by simp

lemma bi_total_eq [transfer_rule]: "bi_total (op =)"
  unfolding bi_total_def by simp

lemma bi_unique_eq [transfer_rule]: "bi_unique (op =)"
  unfolding bi_unique_def by simp

lemma right_total_fun [transfer_rule]:
  "\<lbrakk>right_unique A; right_total B\<rbrakk> \<Longrightarrow> right_total (A ===> B)"
  unfolding right_total_def fun_rel_def
  apply (rule allI, rename_tac g)
  apply (rule_tac x="\<lambda>x. SOME z. B z (g (THE y. A x y))" in exI)
  apply clarify
  apply (subgoal_tac "(THE y. A x y) = y", simp)
  apply (rule someI_ex)
  apply (simp)
  apply (rule the_equality)
  apply assumption
  apply (simp add: right_unique_def)
  done

lemma right_unique_fun [transfer_rule]:
  "\<lbrakk>right_total A; right_unique B\<rbrakk> \<Longrightarrow> right_unique (A ===> B)"
  unfolding right_total_def right_unique_def fun_rel_def
  by (clarify, rule ext, fast)

lemma bi_total_fun [transfer_rule]:
  "\<lbrakk>bi_unique A; bi_total B\<rbrakk> \<Longrightarrow> bi_total (A ===> B)"
  unfolding bi_total_def fun_rel_def
  apply safe
  apply (rename_tac f)
  apply (rule_tac x="\<lambda>y. SOME z. B (f (THE x. A x y)) z" in exI)
  apply clarify
  apply (subgoal_tac "(THE x. A x y) = x", simp)
  apply (rule someI_ex)
  apply (simp)
  apply (rule the_equality)
  apply assumption
  apply (simp add: bi_unique_def)
  apply (rename_tac g)
  apply (rule_tac x="\<lambda>x. SOME z. B z (g (THE y. A x y))" in exI)
  apply clarify
  apply (subgoal_tac "(THE y. A x y) = y", simp)
  apply (rule someI_ex)
  apply (simp)
  apply (rule the_equality)
  apply assumption
  apply (simp add: bi_unique_def)
  done

lemma bi_unique_fun [transfer_rule]:
  "\<lbrakk>bi_total A; bi_unique B\<rbrakk> \<Longrightarrow> bi_unique (A ===> B)"
  unfolding bi_total_def bi_unique_def fun_rel_def fun_eq_iff
  by (safe, metis, fast)


subsection {* Transfer rules *}

lemma eq_parametric [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> A ===> op =) (op =) (op =)"
  using assms unfolding bi_unique_def fun_rel_def by auto

lemma All_parametric [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> op =) ===> op =) All All"
  using assms unfolding bi_total_def fun_rel_def by fast

lemma Ex_parametric [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> op =) ===> op =) Ex Ex"
  using assms unfolding bi_total_def fun_rel_def by fast

lemma If_parametric [transfer_rule]: "(op = ===> A ===> A ===> A) If If"
  unfolding fun_rel_def by simp

lemma Let_parametric [transfer_rule]: "(A ===> (A ===> B) ===> B) Let Let"
  unfolding fun_rel_def by simp

lemma id_parametric [transfer_rule]: "(A ===> A) id id"
  unfolding fun_rel_def by simp

lemma comp_parametric [transfer_rule]:
  "((B ===> C) ===> (A ===> B) ===> (A ===> C)) (op \<circ>) (op \<circ>)"
  unfolding fun_rel_def by simp

lemma fun_upd_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> B) ===> A ===> B ===> A ===> B) fun_upd fun_upd"
  unfolding fun_upd_def [abs_def] by transfer_prover

lemma Domainp_iff: "Domainp T x \<longleftrightarrow> (\<exists>y. T x y)"
  by auto

text {* Fallback rule for transferring universal quantifiers over
  correspondence relations that are not bi-total, and do not have
  custom transfer rules (e.g. relations between function types). *}

lemma Domainp_forall_transfer [transfer_rule]:
  assumes "right_total A"
  shows "((A ===> op =) ===> op =)
    (transfer_bforall (Domainp A)) transfer_forall"
  using assms unfolding right_total_def
  unfolding transfer_forall_def transfer_bforall_def fun_rel_def Domainp_iff
  by metis

text {* Preferred rule for transferring universal quantifiers over
  bi-total correspondence relations (later rules are tried first). *}

lemma transfer_forall_parametric [transfer_rule]:
  "bi_total A \<Longrightarrow> ((A ===> op =) ===> op =) transfer_forall transfer_forall"
  unfolding transfer_forall_def by (rule All_parametric)

end
