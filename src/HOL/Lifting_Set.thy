(*  Title:      HOL/Lifting_Set.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the set type *}

theory Lifting_Set
imports Lifting
begin

subsection {* Relator and predicator properties *}

definition rel_set :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "rel_set R = (\<lambda>A B. (\<forall>x\<in>A. \<exists>y\<in>B. R x y) \<and> (\<forall>y\<in>B. \<exists>x\<in>A. R x y))"

lemma rel_setI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y\<in>B. R x y"
  assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x\<in>A. R x y"
  shows "rel_set R A B"
  using assms unfolding rel_set_def by simp

lemma rel_setD1: "\<lbrakk> rel_set R A B; x \<in> A \<rbrakk> \<Longrightarrow> \<exists>y \<in> B. R x y"
  and rel_setD2: "\<lbrakk> rel_set R A B; y \<in> B \<rbrakk> \<Longrightarrow> \<exists>x \<in> A. R x y"
by(simp_all add: rel_set_def)

lemma rel_set_conversep [simp]: "rel_set A\<inverse>\<inverse> = (rel_set A)\<inverse>\<inverse>"
  unfolding rel_set_def by auto

lemma rel_set_eq [relator_eq]: "rel_set (op =) = (op =)"
  unfolding rel_set_def fun_eq_iff by auto

lemma rel_set_mono[relator_mono]:
  assumes "A \<le> B"
  shows "rel_set A \<le> rel_set B"
using assms unfolding rel_set_def by blast

lemma rel_set_OO[relator_distr]: "rel_set R OO rel_set S = rel_set (R OO S)"
  apply (rule sym)
  apply (intro ext, rename_tac X Z)
  apply (rule iffI)
  apply (rule_tac b="{y. (\<exists>x\<in>X. R x y) \<and> (\<exists>z\<in>Z. S y z)}" in relcomppI)
  apply (simp add: rel_set_def, fast)
  apply (simp add: rel_set_def, fast)
  apply (simp add: rel_set_def, fast)
  done

lemma Domainp_set[relator_domain]:
  assumes "Domainp T = R"
  shows "Domainp (rel_set T) = (\<lambda>A. Ball A R)"
using assms unfolding rel_set_def Domainp_iff[abs_def]
apply (intro ext)
apply (rule iffI) 
apply blast
apply (rename_tac A, rule_tac x="{y. \<exists>x\<in>A. T x y}" in exI, fast)
done

lemma left_total_rel_set[transfer_rule]: 
  "left_total A \<Longrightarrow> left_total (rel_set A)"
  unfolding left_total_def rel_set_def
  apply safe
  apply (rename_tac X, rule_tac x="{y. \<exists>x\<in>X. A x y}" in exI, fast)
done

lemma left_unique_rel_set[transfer_rule]: 
  "left_unique A \<Longrightarrow> left_unique (rel_set A)"
  unfolding left_unique_def rel_set_def
  by fast

lemma right_total_rel_set [transfer_rule]:
  "right_total A \<Longrightarrow> right_total (rel_set A)"
using left_total_rel_set[of "A\<inverse>\<inverse>"] by simp

lemma right_unique_rel_set [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (rel_set A)"
  unfolding right_unique_def rel_set_def by fast

lemma bi_total_rel_set [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (rel_set A)"
by(simp add: bi_total_conv_left_right left_total_rel_set right_total_rel_set)

lemma bi_unique_rel_set [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (rel_set A)"
  unfolding bi_unique_def rel_set_def by fast

lemma set_invariant_commute [invariant_commute]:
  "rel_set (Lifting.invariant P) = Lifting.invariant (\<lambda>A. Ball A P)"
  unfolding fun_eq_iff rel_set_def Lifting.invariant_def Ball_def by fast

subsection {* Quotient theorem for the Lifting package *}

lemma Quotient_set[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (rel_set R) (image Abs) (image Rep) (rel_set T)"
  using assms unfolding Quotient_alt_def4
  apply (simp add: rel_set_OO[symmetric])
  apply (simp add: rel_set_def, fast)
  done

subsection {* Transfer rules for the Transfer package *}

subsubsection {* Unconditional transfer rules *}

context
begin
interpretation lifting_syntax .

lemma empty_transfer [transfer_rule]: "(rel_set A) {} {}"
  unfolding rel_set_def by simp

lemma insert_transfer [transfer_rule]:
  "(A ===> rel_set A ===> rel_set A) insert insert"
  unfolding rel_fun_def rel_set_def by auto

lemma union_transfer [transfer_rule]:
  "(rel_set A ===> rel_set A ===> rel_set A) union union"
  unfolding rel_fun_def rel_set_def by auto

lemma Union_transfer [transfer_rule]:
  "(rel_set (rel_set A) ===> rel_set A) Union Union"
  unfolding rel_fun_def rel_set_def by simp fast

lemma image_transfer [transfer_rule]:
  "((A ===> B) ===> rel_set A ===> rel_set B) image image"
  unfolding rel_fun_def rel_set_def by simp fast

lemma UNION_transfer [transfer_rule]:
  "(rel_set A ===> (A ===> rel_set B) ===> rel_set B) UNION UNION"
  unfolding Union_image_eq [symmetric, abs_def] by transfer_prover

lemma Ball_transfer [transfer_rule]:
  "(rel_set A ===> (A ===> op =) ===> op =) Ball Ball"
  unfolding rel_set_def rel_fun_def by fast

lemma Bex_transfer [transfer_rule]:
  "(rel_set A ===> (A ===> op =) ===> op =) Bex Bex"
  unfolding rel_set_def rel_fun_def by fast

lemma Pow_transfer [transfer_rule]:
  "(rel_set A ===> rel_set (rel_set A)) Pow Pow"
  apply (rule rel_funI, rename_tac X Y, rule rel_setI)
  apply (rename_tac X', rule_tac x="{y\<in>Y. \<exists>x\<in>X'. A x y}" in rev_bexI, clarsimp)
  apply (simp add: rel_set_def, fast)
  apply (rename_tac Y', rule_tac x="{x\<in>X. \<exists>y\<in>Y'. A x y}" in rev_bexI, clarsimp)
  apply (simp add: rel_set_def, fast)
  done

lemma rel_set_transfer [transfer_rule]:
  "((A ===> B ===> op =) ===> rel_set A ===> rel_set B ===> op =) rel_set rel_set"
  unfolding rel_fun_def rel_set_def by fast

lemma bind_transfer [transfer_rule]:
  "(rel_set A ===> (A ===> rel_set B) ===> rel_set B) Set.bind Set.bind"
  unfolding bind_UNION [abs_def] by transfer_prover

lemma INF_parametric [transfer_rule]:
  "(rel_set A ===> (A ===> HOL.eq) ===> HOL.eq) INFIMUM INFIMUM"
  unfolding INF_def [abs_def] by transfer_prover

lemma SUP_parametric [transfer_rule]:
  "(rel_set R ===> (R ===> HOL.eq) ===> HOL.eq) SUPREMUM SUPREMUM"
  unfolding SUP_def [abs_def] by transfer_prover


subsubsection {* Rules requiring bi-unique, bi-total or right-total relations *}

lemma member_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> rel_set A ===> op =) (op \<in>) (op \<in>)"
  using assms unfolding rel_fun_def rel_set_def bi_unique_def by fast

lemma right_total_Collect_transfer[transfer_rule]:
  assumes "right_total A"
  shows "((A ===> op =) ===> rel_set A) (\<lambda>P. Collect (\<lambda>x. P x \<and> Domainp A x)) Collect"
  using assms unfolding right_total_def rel_set_def rel_fun_def Domainp_iff by fast

lemma Collect_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> op =) ===> rel_set A) Collect Collect"
  using assms unfolding rel_fun_def rel_set_def bi_total_def by fast

lemma inter_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_set A ===> rel_set A ===> rel_set A) inter inter"
  using assms unfolding rel_fun_def rel_set_def bi_unique_def by fast

lemma Diff_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_set A ===> rel_set A ===> rel_set A) (op -) (op -)"
  using assms unfolding rel_fun_def rel_set_def bi_unique_def
  unfolding Ball_def Bex_def Diff_eq
  by (safe, simp, metis, simp, metis)

lemma subset_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set A ===> rel_set A ===> op =) (op \<subseteq>) (op \<subseteq>)"
  unfolding subset_eq [abs_def] by transfer_prover

lemma right_total_UNIV_transfer[transfer_rule]: 
  assumes "right_total A"
  shows "(rel_set A) (Collect (Domainp A)) UNIV"
  using assms unfolding right_total_def rel_set_def Domainp_iff by blast

lemma UNIV_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "(rel_set A) UNIV UNIV"
  using assms unfolding rel_set_def bi_total_def by simp

lemma right_total_Compl_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(rel_set A ===> rel_set A) (\<lambda>S. uminus S \<inter> Collect (Domainp A)) uminus"
  unfolding Compl_eq [abs_def]
  by (subst Collect_conj_eq[symmetric]) transfer_prover

lemma Compl_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(rel_set A ===> rel_set A) uminus uminus"
  unfolding Compl_eq [abs_def] by transfer_prover

lemma right_total_Inter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(rel_set (rel_set A) ===> rel_set A) (\<lambda>S. Inter S \<inter> Collect (Domainp A)) Inter"
  unfolding Inter_eq[abs_def]
  by (subst Collect_conj_eq[symmetric]) transfer_prover

lemma Inter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(rel_set (rel_set A) ===> rel_set A) Inter Inter"
  unfolding Inter_eq [abs_def] by transfer_prover

lemma filter_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> op=) ===> rel_set A ===> rel_set A) Set.filter Set.filter"
  unfolding Set.filter_def[abs_def] rel_fun_def rel_set_def by blast

lemma bi_unique_rel_set_lemma:
  assumes "bi_unique R" and "rel_set R X Y"
  obtains f where "Y = image f X" and "inj_on f X" and "\<forall>x\<in>X. R x (f x)"
proof
  let ?f = "\<lambda>x. THE y. R x y"
  from assms show f: "\<forall>x\<in>X. R x (?f x)"
    apply (clarsimp simp add: rel_set_def)
    apply (drule (1) bspec, clarify)
    apply (rule theI2, assumption)
    apply (simp add: bi_unique_def)
    apply assumption
    done
  from assms show "Y = image ?f X"
    apply safe
    apply (clarsimp simp add: rel_set_def)
    apply (drule (1) bspec, clarify)
    apply (rule image_eqI)
    apply (rule the_equality [symmetric], assumption)
    apply (simp add: bi_unique_def)
    apply assumption
    apply (clarsimp simp add: rel_set_def)
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
  "bi_unique A \<Longrightarrow> (rel_set A ===> op =) finite finite"
  by (rule rel_funI, erule (1) bi_unique_rel_set_lemma,
    auto dest: finite_imageD)

lemma card_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_set A ===> op =) card card"
  by (rule rel_funI, erule (1) bi_unique_rel_set_lemma, simp add: card_image)

lemma vimage_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_unique B"
  shows "((A ===> B) ===> rel_set B ===> rel_set A) vimage vimage"
unfolding vimage_def[abs_def] by transfer_prover

lemma setsum_parametric [transfer_rule]:
  assumes "bi_unique A"
  shows "((A ===> op =) ===> rel_set A ===> op =) setsum setsum"
proof(rule rel_funI)+
  fix f :: "'a \<Rightarrow> 'c" and g S T
  assume fg: "(A ===> op =) f g"
    and ST: "rel_set A S T"
  show "setsum f S = setsum g T"
  proof(rule setsum_reindex_cong)
    let ?f = "\<lambda>t. THE s. A s t"
    show "S = ?f ` T"
      by(blast dest: rel_setD1[OF ST] rel_setD2[OF ST] bi_uniqueDl[OF assms] 
           intro: rev_image_eqI the_equality[symmetric] subst[rotated, where P="\<lambda>x. x \<in> S"])

    show "inj_on ?f T"
    proof(rule inj_onI)
      fix t1 t2
      assume "t1 \<in> T" "t2 \<in> T" "?f t1 = ?f t2"
      from ST `t1 \<in> T` obtain s1 where "A s1 t1" "s1 \<in> S" by(auto dest: rel_setD2)
      hence "?f t1 = s1" by(auto dest: bi_uniqueDl[OF assms])
      moreover
      from ST `t2 \<in> T` obtain s2 where "A s2 t2" "s2 \<in> S" by(auto dest: rel_setD2)
      hence "?f t2 = s2" by(auto dest: bi_uniqueDl[OF assms])
      ultimately have "s1 = s2" using `?f t1 = ?f t2` by simp
      with `A s1 t1` `A s2 t2` show "t1 = t2" by(auto dest: bi_uniqueDr[OF assms])
    qed

    fix t
    assume "t \<in> T"
    with ST obtain s where "A s t" "s \<in> S" by(auto dest: rel_setD2)
    hence "?f t = s" by(auto dest: bi_uniqueDl[OF assms])
    moreover from fg `A s t` have "f s = g t" by(rule rel_funD)
    ultimately show "g t = f (?f t)" by simp
  qed
qed

end

end
