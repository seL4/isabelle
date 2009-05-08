(*  Title:      HOLCF/Adm.thy
    Author:     Franz Regensburger and Brian Huffman
*)

header {* Admissibility and compactness *}

theory Adm
imports Cont
begin

defaultsort cpo

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

text {* improved admissibility introduction *}

lemma admI2:
  "(\<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i); \<forall>i. \<exists>j>i. Y i \<noteq> Y j \<and> Y i \<sqsubseteq> Y j\<rbrakk> 
    \<Longrightarrow> P (\<Squnion>i. Y i)) \<Longrightarrow> adm P"
apply (rule admI)
apply (erule (1) increasing_chain_adm_lemma)
apply fast
done

subsection {* Admissibility on chain-finite types *}

text {* for chain-finite (easy) types every formula is admissible *}

lemma adm_chfin: "adm (P::'a::chfin \<Rightarrow> bool)"
by (rule admI, frule chfin, auto simp add: maxinch_is_thelub)

subsection {* Admissibility of special formulae and propagation *}

lemma adm_not_free: "adm (\<lambda>x. t)"
by (rule admI, simp)

lemma adm_conj: "\<lbrakk>adm P; adm Q\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<and> Q x)"
by (fast intro: admI elim: admD)

lemma adm_all: "(\<And>y. adm (\<lambda>x. P x y)) \<Longrightarrow> adm (\<lambda>x. \<forall>y. P x y)"
by (fast intro: admI elim: admD)

lemma adm_ball: "(\<And>y. y \<in> A \<Longrightarrow> adm (\<lambda>x. P x y)) \<Longrightarrow> adm (\<lambda>x. \<forall>y\<in>A. P x y)"
by (fast intro: admI elim: admD)

text {* Admissibility for disjunction is hard to prove. It takes 5 Lemmas *}

lemma adm_disj_lemma1: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk>
    \<Longrightarrow> chain (\<lambda>i. Y (LEAST j. i \<le> j \<and> P (Y j)))"
apply (rule chainI)
apply (erule chain_mono)
apply (rule Least_le)
apply (rule LeastI2_ex)
apply simp_all
done

lemmas adm_disj_lemma2 = LeastI_ex [of "\<lambda>j. i \<le> j \<and> P (Y j)", standard]

lemma adm_disj_lemma3: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk> \<Longrightarrow> 
    (\<Squnion>i. Y i) = (\<Squnion>i. Y (LEAST j. i \<le> j \<and> P (Y j)))"
 apply (frule (1) adm_disj_lemma1)
 apply (rule below_antisym)
  apply (rule lub_mono, assumption+)
  apply (erule chain_mono)
  apply (simp add: adm_disj_lemma2)
 apply (rule lub_range_mono, fast, assumption+)
done

lemma adm_disj_lemma4:
  "\<lbrakk>adm P; chain Y; \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)"
apply (subst adm_disj_lemma3, assumption+)
apply (erule admD)
apply (simp add: adm_disj_lemma1)
apply (simp add: adm_disj_lemma2)
done

lemma adm_disj_lemma5:
  "\<forall>n::nat. P n \<or> Q n \<Longrightarrow> (\<forall>i. \<exists>j\<ge>i. P j) \<or> (\<forall>i. \<exists>j\<ge>i. Q j)"
apply (erule contrapos_pp)
apply (clarsimp, rename_tac a b)
apply (rule_tac x="max a b" in exI)
apply simp
done

lemma adm_disj: "\<lbrakk>adm P; adm Q\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<or> Q x)"
apply (rule admI)
apply (erule adm_disj_lemma5 [THEN disjE])
apply (erule (2) adm_disj_lemma4 [THEN disjI1])
apply (erule (2) adm_disj_lemma4 [THEN disjI2])
done

lemma adm_imp: "\<lbrakk>adm (\<lambda>x. \<not> P x); adm Q\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<longrightarrow> Q x)"
by (subst imp_conv_disj, rule adm_disj)

lemma adm_iff:
  "\<lbrakk>adm (\<lambda>x. P x \<longrightarrow> Q x); adm (\<lambda>x. Q x \<longrightarrow> P x)\<rbrakk>  
    \<Longrightarrow> adm (\<lambda>x. P x = Q x)"
by (subst iff_conv_conj_imp, rule adm_conj)

lemma adm_not_conj:
  "\<lbrakk>adm (\<lambda>x. \<not> P x); adm (\<lambda>x. \<not> Q x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. \<not> (P x \<and> Q x))"
by (simp add: adm_imp)

text {* admissibility and continuity *}

lemma adm_below: "\<lbrakk>cont u; cont v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<sqsubseteq> v x)"
apply (rule admI)
apply (simp add: cont2contlubE)
apply (rule lub_mono)
apply (erule (1) ch2ch_cont)
apply (erule (1) ch2ch_cont)
apply (erule spec)
done

lemma adm_eq: "\<lbrakk>cont u; cont v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x = v x)"
by (simp add: po_eq_conv adm_conj adm_below)

lemma adm_subst: "\<lbrakk>cont t; adm P\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P (t x))"
apply (rule admI)
apply (simp add: cont2contlubE)
apply (erule admD)
apply (erule (1) ch2ch_cont)
apply (erule spec)
done

lemma adm_not_below: "cont t \<Longrightarrow> adm (\<lambda>x. \<not> t x \<sqsubseteq> u)"
apply (rule admI)
apply (drule_tac x=0 in spec)
apply (erule contrapos_nn)
apply (erule rev_below_trans)
apply (erule cont2mono [THEN monofunE])
apply (erule is_ub_thelub)
done

subsection {* Compactness *}

definition
  compact :: "'a::cpo \<Rightarrow> bool" where
  "compact k = adm (\<lambda>x. \<not> k \<sqsubseteq> x)"

lemma compactI: "adm (\<lambda>x. \<not> k \<sqsubseteq> x) \<Longrightarrow> compact k"
unfolding compact_def .

lemma compactD: "compact k \<Longrightarrow> adm (\<lambda>x. \<not> k \<sqsubseteq> x)"
unfolding compact_def .

lemma compactI2:
  "(\<And>Y. \<lbrakk>chain Y; x \<sqsubseteq> (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> \<exists>i. x \<sqsubseteq> Y i) \<Longrightarrow> compact x"
unfolding compact_def adm_def by fast

lemma compactD2:
  "\<lbrakk>compact x; chain Y; x \<sqsubseteq> (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> \<exists>i. x \<sqsubseteq> Y i"
unfolding compact_def adm_def by fast

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

lemma adm_compact_not_below: "\<lbrakk>compact k; cont t\<rbrakk> \<Longrightarrow> adm (\<lambda>x. \<not> k \<sqsubseteq> t x)"
unfolding compact_def by (rule adm_subst)

lemma adm_neq_compact: "\<lbrakk>compact k; cont t\<rbrakk> \<Longrightarrow> adm (\<lambda>x. t x \<noteq> k)"
by (simp add: po_eq_conv adm_imp adm_not_below adm_compact_not_below)

lemma adm_compact_neq: "\<lbrakk>compact k; cont t\<rbrakk> \<Longrightarrow> adm (\<lambda>x. k \<noteq> t x)"
by (simp add: po_eq_conv adm_imp adm_not_below adm_compact_not_below)

lemma compact_UU [simp, intro]: "compact \<bottom>"
by (rule compactI, simp add: adm_not_free)

lemma adm_not_UU: "cont t \<Longrightarrow> adm (\<lambda>x. t x \<noteq> \<bottom>)"
by (simp add: adm_neq_compact)

text {* Any upward-closed predicate is admissible. *}

lemma adm_upward:
  assumes P: "\<And>x y. \<lbrakk>P x; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> P y"
  shows "adm P"
by (rule admI, drule spec, erule P, erule is_ub_thelub)

lemmas adm_lemmas [simp] =
  adm_not_free adm_conj adm_all adm_ball adm_disj adm_imp adm_iff
  adm_below adm_eq adm_not_below
  adm_compact_not_below adm_compact_neq adm_neq_compact adm_not_UU

end
