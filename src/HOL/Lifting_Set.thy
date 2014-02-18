(*  Title:      HOL/Lifting_Set.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the set type *}

theory Lifting_Set
imports Lifting
begin

subsection {* Relator and predicator properties *}

definition set_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "set_rel R = (\<lambda>A B. (\<forall>x\<in>A. \<exists>y\<in>B. R x y) \<and> (\<forall>y\<in>B. \<exists>x\<in>A. R x y))"

lemma set_relI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y\<in>B. R x y"
  assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x\<in>A. R x y"
  shows "set_rel R A B"
  using assms unfolding set_rel_def by simp

lemma set_relD1: "\<lbrakk> set_rel R A B; x \<in> A \<rbrakk> \<Longrightarrow> \<exists>y \<in> B. R x y"
  and set_relD2: "\<lbrakk> set_rel R A B; y \<in> B \<rbrakk> \<Longrightarrow> \<exists>x \<in> A. R x y"
by(simp_all add: set_rel_def)

lemma set_rel_conversep [simp]: "set_rel A\<inverse>\<inverse> = (set_rel A)\<inverse>\<inverse>"
  unfolding set_rel_def by auto

lemma set_rel_eq [relator_eq]: "set_rel (op =) = (op =)"
  unfolding set_rel_def fun_eq_iff by auto

lemma set_rel_mono[relator_mono]:
  assumes "A \<le> B"
  shows "set_rel A \<le> set_rel B"
using assms unfolding set_rel_def by blast

lemma set_rel_OO[relator_distr]: "set_rel R OO set_rel S = set_rel (R OO S)"
  apply (rule sym)
  apply (intro ext, rename_tac X Z)
  apply (rule iffI)
  apply (rule_tac b="{y. (\<exists>x\<in>X. R x y) \<and> (\<exists>z\<in>Z. S y z)}" in relcomppI)
  apply (simp add: set_rel_def, fast)
  apply (simp add: set_rel_def, fast)
  apply (simp add: set_rel_def, fast)
  done

lemma Domainp_set[relator_domain]:
  assumes "Domainp T = R"
  shows "Domainp (set_rel T) = (\<lambda>A. Ball A R)"
using assms unfolding set_rel_def Domainp_iff[abs_def]
apply (intro ext)
apply (rule iffI) 
apply blast
apply (rename_tac A, rule_tac x="{y. \<exists>x\<in>A. T x y}" in exI, fast)
done

lemma left_total_set_rel[reflexivity_rule]: 
  "left_total A \<Longrightarrow> left_total (set_rel A)"
  unfolding left_total_def set_rel_def
  apply safe
  apply (rename_tac X, rule_tac x="{y. \<exists>x\<in>X. A x y}" in exI, fast)
done

lemma left_unique_set_rel[reflexivity_rule]: 
  "left_unique A \<Longrightarrow> left_unique (set_rel A)"
  unfolding left_unique_def set_rel_def
  by fast

lemma right_total_set_rel [transfer_rule]:
  "right_total A \<Longrightarrow> right_total (set_rel A)"
using left_total_set_rel[of "A\<inverse>\<inverse>"] by simp

lemma right_unique_set_rel [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (set_rel A)"
  unfolding right_unique_def set_rel_def by fast

lemma bi_total_set_rel [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (set_rel A)"
by(simp add: bi_total_conv_left_right left_total_set_rel right_total_set_rel)

lemma bi_unique_set_rel [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (set_rel A)"
  unfolding bi_unique_def set_rel_def by fast

lemma set_invariant_commute [invariant_commute]:
  "set_rel (Lifting.invariant P) = Lifting.invariant (\<lambda>A. Ball A P)"
  unfolding fun_eq_iff set_rel_def Lifting.invariant_def Ball_def by fast

subsection {* Quotient theorem for the Lifting package *}

lemma Quotient_set[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (set_rel R) (image Abs) (image Rep) (set_rel T)"
  using assms unfolding Quotient_alt_def4
  apply (simp add: set_rel_OO[symmetric])
  apply (simp add: set_rel_def, fast)
  done

subsection {* Transfer rules for the Transfer package *}

subsubsection {* Unconditional transfer rules *}

context
begin
interpretation lifting_syntax .

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

lemma set_rel_transfer [transfer_rule]:
  "((A ===> B ===> op =) ===> set_rel A ===> set_rel B ===> op =)
    set_rel set_rel"
  unfolding fun_rel_def set_rel_def by fast

lemma SUPR_parametric [transfer_rule]:
  "(set_rel R ===> (R ===> op =) ===> op =) SUPR (SUPR :: _ \<Rightarrow> _ \<Rightarrow> _::complete_lattice)"
proof(rule fun_relI)+
  fix A B f and g :: "'b \<Rightarrow> 'c"
  assume AB: "set_rel R A B"
    and fg: "(R ===> op =) f g"
  show "SUPR A f = SUPR B g"
    by(rule SUPR_eq)(auto 4 4 dest: set_relD1[OF AB] set_relD2[OF AB] fun_relD[OF fg] intro: rev_bexI)
qed

lemma bind_transfer [transfer_rule]:
  "(set_rel A ===> (A ===> set_rel B) ===> set_rel B) Set.bind Set.bind"
unfolding bind_UNION[abs_def] by transfer_prover

subsubsection {* Rules requiring bi-unique, bi-total or right-total relations *}

lemma member_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> set_rel A ===> op =) (op \<in>) (op \<in>)"
  using assms unfolding fun_rel_def set_rel_def bi_unique_def by fast

lemma right_total_Collect_transfer[transfer_rule]:
  assumes "right_total A"
  shows "((A ===> op =) ===> set_rel A) (\<lambda>P. Collect (\<lambda>x. P x \<and> Domainp A x)) Collect"
  using assms unfolding right_total_def set_rel_def fun_rel_def Domainp_iff by fast

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

lemma right_total_UNIV_transfer[transfer_rule]: 
  assumes "right_total A"
  shows "(set_rel A) (Collect (Domainp A)) UNIV"
  using assms unfolding right_total_def set_rel_def Domainp_iff by blast

lemma UNIV_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "(set_rel A) UNIV UNIV"
  using assms unfolding set_rel_def bi_total_def by simp

lemma right_total_Compl_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(set_rel A ===> set_rel A) (\<lambda>S. uminus S \<inter> Collect (Domainp A)) uminus"
  unfolding Compl_eq [abs_def]
  by (subst Collect_conj_eq[symmetric]) transfer_prover

lemma Compl_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(set_rel A ===> set_rel A) uminus uminus"
  unfolding Compl_eq [abs_def] by transfer_prover

lemma right_total_Inter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(set_rel (set_rel A) ===> set_rel A) (\<lambda>S. Inter S \<inter> Collect (Domainp A)) Inter"
  unfolding Inter_eq[abs_def]
  by (subst Collect_conj_eq[symmetric]) transfer_prover

lemma Inter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(set_rel (set_rel A) ===> set_rel A) Inter Inter"
  unfolding Inter_eq [abs_def] by transfer_prover

lemma filter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> op=) ===> set_rel A ===> set_rel A) Set.filter Set.filter"
  unfolding Set.filter_def[abs_def] fun_rel_def set_rel_def by blast

lemma bi_unique_set_rel_lemma:
  assumes "bi_unique R" and "set_rel R X Y"
  obtains f where "Y = image f X" and "inj_on f X" and "\<forall>x\<in>X. R x (f x)"
proof
  let ?f = "\<lambda>x. THE y. R x y"
  from assms show f: "\<forall>x\<in>X. R x (?f x)"
    apply (clarsimp simp add: set_rel_def)
    apply (drule (1) bspec, clarify)
    apply (rule theI2, assumption)
    apply (simp add: bi_unique_def)
    apply assumption
    done
  from assms show "Y = image ?f X"
    apply safe
    apply (clarsimp simp add: set_rel_def)
    apply (drule (1) bspec, clarify)
    apply (rule image_eqI)
    apply (rule the_equality [symmetric], assumption)
    apply (simp add: bi_unique_def)
    apply assumption
    apply (clarsimp simp add: set_rel_def)
    apply (frule (1) bspec, clarify)
    apply (rule theI2, assumption)
    apply (clarsimp simp add: bi_unique_def)
    apply (simp add: bi_unique_def, metis)
    done
  show "inj_on ?f X"
    apply (rule inj_onI)
    apply (drule f [rule_format])
    apply (drule f [rule_format])
    apply (simp add: assms(1) [unfolded bi_unique_def])
    done
qed

lemma finite_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (set_rel A ===> op =) finite finite"
  by (rule fun_relI, erule (1) bi_unique_set_rel_lemma,
    auto dest: finite_imageD)

lemma card_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (set_rel A ===> op =) card card"
  by (rule fun_relI, erule (1) bi_unique_set_rel_lemma, simp add: card_image)

lemma vimage_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_unique B"
  shows "((A ===> B) ===> set_rel B ===> set_rel A) vimage vimage"
unfolding vimage_def[abs_def] by transfer_prover

lemma setsum_parametric [transfer_rule]:
  assumes "bi_unique A"
  shows "((A ===> op =) ===> set_rel A ===> op =) setsum setsum"
proof(rule fun_relI)+
  fix f :: "'a \<Rightarrow> 'c" and g S T
  assume fg: "(A ===> op =) f g"
    and ST: "set_rel A S T"
  show "setsum f S = setsum g T"
  proof(rule setsum_reindex_cong)
    let ?f = "\<lambda>t. THE s. A s t"
    show "S = ?f ` T"
      by(blast dest: set_relD1[OF ST] set_relD2[OF ST] bi_uniqueDl[OF assms] 
           intro: rev_image_eqI the_equality[symmetric] subst[rotated, where P="\<lambda>x. x \<in> S"])

    show "inj_on ?f T"
    proof(rule inj_onI)
      fix t1 t2
      assume "t1 \<in> T" "t2 \<in> T" "?f t1 = ?f t2"
      from ST `t1 \<in> T` obtain s1 where "A s1 t1" "s1 \<in> S" by(auto dest: set_relD2)
      hence "?f t1 = s1" by(auto dest: bi_uniqueDl[OF assms])
      moreover
      from ST `t2 \<in> T` obtain s2 where "A s2 t2" "s2 \<in> S" by(auto dest: set_relD2)
      hence "?f t2 = s2" by(auto dest: bi_uniqueDl[OF assms])
      ultimately have "s1 = s2" using `?f t1 = ?f t2` by simp
      with `A s1 t1` `A s2 t2` show "t1 = t2" by(auto dest: bi_uniqueDr[OF assms])
    qed

    fix t
    assume "t \<in> T"
    with ST obtain s where "A s t" "s \<in> S" by(auto dest: set_relD2)
    hence "?f t = s" by(auto dest: bi_uniqueDl[OF assms])
    moreover from fg `A s t` have "f s = g t" by(rule fun_relD)
    ultimately show "g t = f (?f t)" by simp
  qed
qed

end

end
