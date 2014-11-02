(*  Title:      HOL/HOLCF/Adm.thy
    Author:     Franz Regensburger and Brian Huffman
*)

section {* Admissibility and compactness *}

theory Adm
imports Cont
begin

default_sort cpo

subsection {* Definitions *}

definition
  adm :: "('a::cpo \<Rightarrow> bool) \<Rightarrow> bool" where
  "adm P = (\<forall>Y. chain Y \<longrightarrow> (\<forall>i. P (Y i)) \<longrightarrow> P (\<Squnion>i. Y i))"

lemma admI:
   "(\<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)) \<Longrightarrow> adm P"
unfolding adm_def by fast

lemma admD: "\<lbrakk>adm P; chain Y; \<And>i. P (Y i)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)"
unfolding adm_def by fast

lemma admD2: "\<lbrakk>adm (\<lambda>x. \<not> P x); chain Y; P (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> \<exists>i. P (Y i)"
unfolding adm_def by fast

lemma triv_admI: "\<forall>x. P x \<Longrightarrow> adm P"
by (rule admI, erule spec)

subsection {* Admissibility on chain-finite types *}

text {* For chain-finite (easy) types every formula is admissible. *}

lemma adm_chfin [simp]: "adm (P::'a::chfin \<Rightarrow> bool)"
by (rule admI, frule chfin, auto simp add: maxinch_is_thelub)

subsection {* Admissibility of special formulae and propagation *}

lemma adm_const [simp]: "adm (\<lambda>x. t)"
by (rule admI, simp)

lemma adm_conj [simp]:
  "\<lbrakk>adm (\<lambda>x. P x); adm (\<lambda>x. Q x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<and> Q x)"
by (fast intro: admI elim: admD)

lemma adm_all [simp]:
  "(\<And>y. adm (\<lambda>x. P x y)) \<Longrightarrow> adm (\<lambda>x. \<forall>y. P x y)"
by (fast intro: admI elim: admD)

lemma adm_ball [simp]:
  "(\<And>y. y \<in> A \<Longrightarrow> adm (\<lambda>x. P x y)) \<Longrightarrow> adm (\<lambda>x. \<forall>y\<in>A. P x y)"
by (fast intro: admI elim: admD)

text {* Admissibility for disjunction is hard to prove. It requires 2 lemmas. *}

lemma adm_disj_lemma1:
  assumes adm: "adm P"
  assumes chain: "chain Y"
  assumes P: "\<forall>i. \<exists>j\<ge>i. P (Y j)"
  shows "P (\<Squnion>i. Y i)"
proof -
  def f \<equiv> "\<lambda>i. LEAST j. i \<le> j \<and> P (Y j)"
  have chain': "chain (\<lambda>i. Y (f i))"
    unfolding f_def
    apply (rule chainI)
    apply (rule chain_mono [OF chain])
    apply (rule Least_le)
    apply (rule LeastI2_ex)
    apply (simp_all add: P)
    done
  have f1: "\<And>i. i \<le> f i" and f2: "\<And>i. P (Y (f i))"
    using LeastI_ex [OF P [rule_format]] by (simp_all add: f_def)
  have lub_eq: "(\<Squnion>i. Y i) = (\<Squnion>i. Y (f i))"
    apply (rule below_antisym)
    apply (rule lub_mono [OF chain chain'])
    apply (rule chain_mono [OF chain f1])
    apply (rule lub_range_mono [OF _ chain chain'])
    apply clarsimp
    done
  show "P (\<Squnion>i. Y i)"
    unfolding lub_eq using adm chain' f2 by (rule admD)
qed

lemma adm_disj_lemma2:
  "\<forall>n::nat. P n \<or> Q n \<Longrightarrow> (\<forall>i. \<exists>j\<ge>i. P j) \<or> (\<forall>i. \<exists>j\<ge>i. Q j)"
apply (erule contrapos_pp)
apply (clarsimp, rename_tac a b)
apply (rule_tac x="max a b" in exI)
apply simp
done

lemma adm_disj [simp]:
  "\<lbrakk>adm (\<lambda>x. P x); adm (\<lambda>x. Q x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<or> Q x)"
apply (rule admI)
apply (erule adm_disj_lemma2 [THEN disjE])
apply (erule (2) adm_disj_lemma1 [THEN disjI1])
apply (erule (2) adm_disj_lemma1 [THEN disjI2])
done

lemma adm_imp [simp]:
  "\<lbrakk>adm (\<lambda>x. \<not> P x); adm (\<lambda>x. Q x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<longrightarrow> Q x)"
by (subst imp_conv_disj, rule adm_disj)

lemma adm_iff [simp]:
  "\<lbrakk>adm (\<lambda>x. P x \<longrightarrow> Q x); adm (\<lambda>x. Q x \<longrightarrow> P x)\<rbrakk>  
    \<Longrightarrow> adm (\<lambda>x. P x = Q x)"
by (subst iff_conv_conj_imp, rule adm_conj)

text {* admissibility and continuity *}

lemma adm_below [simp]:
  "\<lbrakk>cont (\<lambda>x. u x); cont (\<lambda>x. v x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<sqsubseteq> v x)"
by (simp add: adm_def cont2contlubE lub_mono ch2ch_cont)

lemma adm_eq [simp]:
  "\<lbrakk>cont (\<lambda>x. u x); cont (\<lambda>x. v x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x = v x)"
by (simp add: po_eq_conv)

lemma adm_subst: "\<lbrakk>cont (\<lambda>x. t x); adm P\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P (t x))"
by (simp add: adm_def cont2contlubE ch2ch_cont)

lemma adm_not_below [simp]: "cont (\<lambda>x. t x) \<Longrightarrow> adm (\<lambda>x. t x \<notsqsubseteq> u)"
by (rule admI, simp add: cont2contlubE ch2ch_cont lub_below_iff)

subsection {* Compactness *}

definition
  compact :: "'a::cpo \<Rightarrow> bool" where
  "compact k = adm (\<lambda>x. k \<notsqsubseteq> x)"

lemma compactI: "adm (\<lambda>x. k \<notsqsubseteq> x) \<Longrightarrow> compact k"
unfolding compact_def .

lemma compactD: "compact k \<Longrightarrow> adm (\<lambda>x. k \<notsqsubseteq> x)"
unfolding compact_def .

lemma compactI2:
  "(\<And>Y. \<lbrakk>chain Y; x \<sqsubseteq> (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> \<exists>i. x \<sqsubseteq> Y i) \<Longrightarrow> compact x"
unfolding compact_def adm_def by fast

lemma compactD2:
  "\<lbrakk>compact x; chain Y; x \<sqsubseteq> (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> \<exists>i. x \<sqsubseteq> Y i"
unfolding compact_def adm_def by fast

lemma compact_below_lub_iff:
  "\<lbrakk>compact x; chain Y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> (\<Squnion>i. Y i) \<longleftrightarrow> (\<exists>i. x \<sqsubseteq> Y i)"
by (fast intro: compactD2 elim: below_lub)

lemma compact_chfin [simp]: "compact (x::'a::chfin)"
by (rule compactI [OF adm_chfin])

lemma compact_imp_max_in_chain:
  "\<lbrakk>chain Y; compact (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> \<exists>i. max_in_chain i Y"
apply (drule (1) compactD2, simp)
apply (erule exE, rule_tac x=i in exI)
apply (rule max_in_chainI)
apply (rule below_antisym)
apply (erule (1) chain_mono)
apply (erule (1) below_trans [OF is_ub_thelub])
done

text {* admissibility and compactness *}

lemma adm_compact_not_below [simp]:
  "\<lbrakk>compact k; cont (\<lambda>x. t x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. k \<notsqsubseteq> t x)"
unfolding compact_def by (rule adm_subst)

lemma adm_neq_compact [simp]:
  "\<lbrakk>compact k; cont (\<lambda>x. t x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. t x \<noteq> k)"
by (simp add: po_eq_conv)

lemma adm_compact_neq [simp]:
  "\<lbrakk>compact k; cont (\<lambda>x. t x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. k \<noteq> t x)"
by (simp add: po_eq_conv)

lemma compact_bottom [simp, intro]: "compact \<bottom>"
by (rule compactI, simp)

text {* Any upward-closed predicate is admissible. *}

lemma adm_upward:
  assumes P: "\<And>x y. \<lbrakk>P x; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> P y"
  shows "adm P"
by (rule admI, drule spec, erule P, erule is_ub_thelub)

lemmas adm_lemmas =
  adm_const adm_conj adm_all adm_ball adm_disj adm_imp adm_iff
  adm_below adm_eq adm_not_below
  adm_compact_not_below adm_compact_neq adm_neq_compact

end
