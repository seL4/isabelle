(*  Title:      HOLCF/Adm.thy
    ID:         $Id$
    Author:     Franz Regensburger
*)

header {* Admissibility and compactness *}

theory Adm
imports Cont
begin

defaultsort cpo

subsection {* Definitions *}

constdefs
  adm :: "('a::cpo \<Rightarrow> bool) \<Rightarrow> bool"
  "adm P \<equiv> \<forall>Y. chain Y \<longrightarrow> (\<forall>i. P (Y i)) \<longrightarrow> P (\<Squnion>i. Y i)"

  compact :: "'a::cpo \<Rightarrow> bool"
  "compact k \<equiv> adm (\<lambda>x. \<not> k \<sqsubseteq> x)"

lemma admI:
   "(\<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)) \<Longrightarrow> adm P"
by (unfold adm_def, fast)

lemma triv_admI: "\<forall>x. P x \<Longrightarrow> adm P"
by (rule admI, erule spec)

lemma admD: "\<lbrakk>adm P; chain Y; \<forall>i. P (Y i)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)"
by (unfold adm_def, fast)

lemma compactI: "adm (\<lambda>x. \<not> k \<sqsubseteq> x) \<Longrightarrow> compact k"
by (unfold compact_def)

lemma compactD: "compact k \<Longrightarrow> adm (\<lambda>x. \<not> k \<sqsubseteq> x)"
by (unfold compact_def)

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

lemma adm_max_in_chain: 
  "\<forall>Y. chain (Y::nat \<Rightarrow> 'a) \<longrightarrow> (\<exists>n. max_in_chain n Y)
    \<Longrightarrow> adm (P::'a \<Rightarrow> bool)"
by (auto simp add: adm_def maxinch_is_thelub)

lemmas adm_chfin = chfin [THEN adm_max_in_chain, standard]

lemma compact_chfin: "compact (x::'a::chfin)"
by (rule compactI, rule adm_chfin)

subsection {* Admissibility of special formulae and propagation *}

lemma adm_not_free: "adm (\<lambda>x. t)"
by (rule admI, simp)

lemma adm_conj: "\<lbrakk>adm P; adm Q\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<and> Q x)"
by (fast elim: admD intro: admI)

lemma adm_all: "\<forall>y. adm (P y) \<Longrightarrow> adm (\<lambda>x. \<forall>y. P y x)"
by (fast intro: admI elim: admD)

lemma adm_ball: "\<forall>y\<in>A. adm (P y) \<Longrightarrow> adm (\<lambda>x. \<forall>y\<in>A. P y x)"
by (fast intro: admI elim: admD)

lemmas adm_all2 = adm_all [rule_format]
lemmas adm_ball2 = adm_ball [rule_format]

text {* Admissibility for disjunction is hard to prove. It takes 5 Lemmas *}

lemma adm_disj_lemma1: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk>
    \<Longrightarrow> chain (\<lambda>i. Y (LEAST j. i \<le> j \<and> P (Y j)))"
apply (rule chainI)
apply (erule chain_mono3)
apply (rule Least_le)
apply (rule LeastI2_ex)
apply simp_all
done

lemmas adm_disj_lemma2 = LeastI_ex [of "\<lambda>j. i \<le> j \<and> P (Y j)", standard]

lemma adm_disj_lemma3: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk> \<Longrightarrow> 
    (\<Squnion>i. Y i) = (\<Squnion>i. Y (LEAST j. i \<le> j \<and> P (Y j)))"
 apply (frule (1) adm_disj_lemma1)
 apply (rule antisym_less)
  apply (rule lub_mono [rule_format], assumption+)
  apply (erule chain_mono3)
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
apply (simp add: le_maxI1 le_maxI2)
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

lemma adm_less: "\<lbrakk>cont u; cont v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<sqsubseteq> v x)"
apply (rule admI)
apply (simp add: cont2contlubE)
apply (rule lub_mono)
apply (erule (1) ch2ch_cont)
apply (erule (1) ch2ch_cont)
apply assumption
done

lemma adm_eq: "\<lbrakk>cont u; cont v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x = v x)"
by (simp add: po_eq_conv adm_conj adm_less)

lemma adm_subst: "\<lbrakk>cont t; adm P\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P (t x))"
apply (rule admI)
apply (simp add: cont2contlubE)
apply (erule admD)
apply (erule (1) ch2ch_cont)
apply assumption
done

lemma adm_not_less: "cont t \<Longrightarrow> adm (\<lambda>x. \<not> t x \<sqsubseteq> u)"
apply (rule admI)
apply (drule_tac x=0 in spec)
apply (erule contrapos_nn)
apply (erule rev_trans_less)
apply (erule cont2mono [THEN monofun_fun_arg])
apply (erule is_ub_thelub)
done

text {* admissibility and compactness *}

lemma adm_compact_not_less: "\<lbrakk>compact k; cont t\<rbrakk> \<Longrightarrow> adm (\<lambda>x. \<not> k \<sqsubseteq> t x)"
by (unfold compact_def, erule adm_subst)

lemma adm_neq_compact: "\<lbrakk>compact k; cont t\<rbrakk> \<Longrightarrow> adm (\<lambda>x. t x \<noteq> k)"
by (simp add: po_eq_conv adm_imp adm_not_less adm_compact_not_less)

lemma adm_compact_neq: "\<lbrakk>compact k; cont t\<rbrakk> \<Longrightarrow> adm (\<lambda>x. k \<noteq> t x)"
by (simp add: po_eq_conv adm_imp adm_not_less adm_compact_not_less)

lemma compact_UU [simp, intro]: "compact \<bottom>"
by (rule compactI, simp add: adm_not_free)

lemma adm_not_UU: "cont t \<Longrightarrow> adm (\<lambda>x. t x \<noteq> \<bottom>)"
by (simp add: adm_neq_compact)

lemmas adm_lemmas [simp] =
  adm_not_free adm_conj adm_all2 adm_ball2 adm_disj adm_imp adm_iff
  adm_less adm_eq adm_not_less
  adm_compact_not_less adm_compact_neq adm_neq_compact adm_not_UU

(* legacy ML bindings *)
ML
{*
val adm_def = thm "adm_def";
val admI = thm "admI";
val triv_admI = thm "triv_admI";
val admD = thm "admD";
val adm_max_in_chain = thm "adm_max_in_chain";
val adm_chfin = thm "adm_chfin";
val admI2 = thm "admI2";
val adm_less = thm "adm_less";
val adm_conj = thm "adm_conj";
val adm_not_free = thm "adm_not_free";
val adm_not_less = thm "adm_not_less";
val adm_all = thm "adm_all";
val adm_all2 = thm "adm_all2";
val adm_ball = thm "adm_ball";
val adm_ball2 = thm "adm_ball2";
val adm_subst = thm "adm_subst";
val adm_not_UU = thm "adm_not_UU";
val adm_eq = thm "adm_eq";
val adm_disj_lemma1 = thm "adm_disj_lemma1";
val adm_disj_lemma2 = thm "adm_disj_lemma2";
val adm_disj_lemma3 = thm "adm_disj_lemma3";
val adm_disj_lemma4 = thm "adm_disj_lemma4";
val adm_disj_lemma5 = thm "adm_disj_lemma5";
val adm_disj = thm "adm_disj";
val adm_imp = thm "adm_imp";
val adm_iff = thm "adm_iff";
val adm_not_conj = thm "adm_not_conj";
val adm_lemmas = thms "adm_lemmas";
*}

end
