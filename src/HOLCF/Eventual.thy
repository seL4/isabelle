theory Eventual
imports Infinite_Set
begin

subsection {* Lemmas about MOST *}

lemma MOST_INFM:
  assumes inf: "infinite (UNIV::'a set)"
  shows "MOST x::'a. P x \<Longrightarrow> INFM x::'a. P x"
  unfolding Alm_all_def Inf_many_def
  apply (auto simp add: Collect_neg_eq)
  apply (drule (1) finite_UnI)
  apply (simp add: Compl_partition2 inf)
  done

lemma MOST_comp: "\<lbrakk>inj f; MOST x. P x\<rbrakk> \<Longrightarrow> MOST x. P (f x)"
unfolding MOST_iff_finiteNeg
by (drule (1) finite_vimageI, simp)

lemma INFM_comp: "\<lbrakk>inj f; INFM x. P (f x)\<rbrakk> \<Longrightarrow> INFM x. P x"
unfolding Inf_many_def
by (clarify, drule (1) finite_vimageI, simp)

lemma MOST_SucI: "MOST n. P n \<Longrightarrow> MOST n. P (Suc n)"
by (rule MOST_comp [OF inj_Suc])

lemma MOST_SucD: "MOST n. P (Suc n) \<Longrightarrow> MOST n. P n"
unfolding MOST_nat
apply (clarify, rule_tac x="Suc m" in exI, clarify)
apply (erule Suc_lessE, simp)
done

lemma MOST_Suc_iff: "(MOST n. P (Suc n)) \<longleftrightarrow> (MOST n. P n)"
by (rule iffI [OF MOST_SucD MOST_SucI])

lemma INFM_finite_Bex_distrib:
  "finite A \<Longrightarrow> (INFM y. \<exists>x\<in>A. P x y) \<longleftrightarrow> (\<exists>x\<in>A. INFM y. P x y)"
by (induct set: finite, simp, simp add: INFM_disj_distrib)

lemma MOST_finite_Ball_distrib:
  "finite A \<Longrightarrow> (MOST y. \<forall>x\<in>A. P x y) \<longleftrightarrow> (\<forall>x\<in>A. MOST y. P x y)"
by (induct set: finite, simp, simp add: MOST_conj_distrib)

lemma MOST_ge_nat: "MOST n::nat. m \<le> n"
unfolding MOST_nat_le by fast

subsection {* Eventually constant sequences *}

definition
  eventually_constant :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "eventually_constant S = (\<exists>x. MOST i. S i = x)"

lemma eventually_constant_MOST_MOST:
  "eventually_constant S \<longleftrightarrow> (MOST m. MOST n. S n = S m)"
unfolding eventually_constant_def MOST_nat
apply safe
apply (rule_tac x=m in exI, clarify)
apply (rule_tac x=m in exI, clarify)
apply simp
apply fast
done

lemma eventually_constantI: "MOST i. S i = x \<Longrightarrow> eventually_constant S"
unfolding eventually_constant_def by fast

lemma eventually_constant_comp:
  "eventually_constant (\<lambda>i. S i) \<Longrightarrow> eventually_constant (\<lambda>i. f (S i))"
unfolding eventually_constant_def
apply (erule exE, rule_tac x="f x" in exI)
apply (erule MOST_mono, simp)
done

lemma eventually_constant_Suc_iff:
  "eventually_constant (\<lambda>i. S (Suc i)) \<longleftrightarrow> eventually_constant (\<lambda>i. S i)"
unfolding eventually_constant_def
by (subst MOST_Suc_iff, rule refl)

lemma eventually_constant_SucD:
  "eventually_constant (\<lambda>i. S (Suc i)) \<Longrightarrow> eventually_constant (\<lambda>i. S i)"
by (rule eventually_constant_Suc_iff [THEN iffD1])

subsection {* Limits of eventually constant sequences *}

definition
  eventual :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "eventual S = (THE x. MOST i. S i = x)"

lemma eventual_eqI: "MOST i. S i = x \<Longrightarrow> eventual S = x"
unfolding eventual_def
apply (rule the_equality, assumption)
apply (rename_tac y)
apply (subgoal_tac "MOST i::nat. y = x", simp)
apply (erule MOST_rev_mp)
apply (erule MOST_rev_mp)
apply simp
done

lemma MOST_eq_eventual:
  "eventually_constant S \<Longrightarrow> MOST i. S i = eventual S"
unfolding eventually_constant_def
by (erule exE, simp add: eventual_eqI)

lemma eventual_mem_range:
  "eventually_constant S \<Longrightarrow> eventual S \<in> range S"
apply (drule MOST_eq_eventual)
apply (simp only: MOST_nat_le, clarify)
apply (drule spec, drule mp, rule order_refl)
apply (erule range_eqI [OF sym])
done

lemma eventually_constant_MOST_iff:
  assumes S: "eventually_constant S"
  shows "(MOST n. P (S n)) \<longleftrightarrow> P (eventual S)"
apply (subgoal_tac "(MOST n. P (S n)) \<longleftrightarrow> (MOST n::nat. P (eventual S))")
apply simp
apply (rule iffI)
apply (rule MOST_rev_mp [OF MOST_eq_eventual [OF S]])
apply (erule MOST_mono, force)
apply (rule MOST_rev_mp [OF MOST_eq_eventual [OF S]])
apply (erule MOST_mono, simp)
done

lemma MOST_eventual:
  "\<lbrakk>eventually_constant S; MOST n. P (S n)\<rbrakk> \<Longrightarrow> P (eventual S)"
proof -
  assume "eventually_constant S"
  hence "MOST n. S n = eventual S"
    by (rule MOST_eq_eventual)
  moreover assume "MOST n. P (S n)"
  ultimately have "MOST n. S n = eventual S \<and> P (S n)"
    by (rule MOST_conj_distrib [THEN iffD2, OF conjI])
  hence "MOST n::nat. P (eventual S)"
    by (rule MOST_mono) auto
  thus ?thesis by simp
qed

lemma eventually_constant_MOST_Suc_eq:
  "eventually_constant S \<Longrightarrow> MOST n. S (Suc n) = S n"
apply (drule MOST_eq_eventual)
apply (frule MOST_Suc_iff [THEN iffD2])
apply (erule MOST_rev_mp)
apply (erule MOST_rev_mp)
apply simp
done

lemma eventual_comp:
  "eventually_constant S \<Longrightarrow> eventual (\<lambda>i. f (S i)) = f (eventual (\<lambda>i. S i))"
apply (rule eventual_eqI)
apply (rule MOST_mono)
apply (erule MOST_eq_eventual)
apply simp
done

end
