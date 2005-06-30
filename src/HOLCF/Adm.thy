(*  Title:      HOLCF/Adm.thy
    ID:         $Id$
    Author:     Franz Regensburger
*)

header {* Admissibility *}

theory Adm
imports Cont
begin

defaultsort cpo

subsection {* Definitions *}

constdefs
  adm :: "('a::cpo \<Rightarrow> bool) \<Rightarrow> bool"
  "adm P \<equiv> \<forall>Y. chain Y \<longrightarrow> (\<forall>i. P (Y i)) \<longrightarrow> P (\<Squnion>i. Y i)"

lemma admI:
   "(\<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)) \<Longrightarrow> adm P"
apply (unfold adm_def)
apply blast
done

lemma triv_admI: "\<forall>x. P x \<Longrightarrow> adm P"
apply (rule admI)
apply (erule spec)
done

lemma admD: "\<lbrakk>adm P; chain Y; \<forall>i. P (Y i)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)"
apply (unfold adm_def)
apply blast
done

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
apply (unfold adm_def)
apply (intro strip)
apply (drule spec)
apply (drule mp)
apply assumption
apply (erule exE)
apply (simp add: maxinch_is_thelub)
done

lemmas adm_chfin = chfin [THEN adm_max_in_chain, standard]

subsection {* Admissibility of special formulae and propagation *}

lemma adm_less: "\<lbrakk>cont u; cont v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<sqsubseteq> v x)"
apply (rule admI)
apply (simp add: cont2contlub [THEN contlubE])
apply (rule lub_mono)
apply (erule (1) cont2mono [THEN ch2ch_monofun])
apply (erule (1) cont2mono [THEN ch2ch_monofun])
apply assumption
done

lemma adm_conj: "\<lbrakk>adm P; adm Q\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<and> Q x)"
by (fast elim: admD intro: admI)

lemma adm_not_free: "adm (\<lambda>x. t)"
by (rule admI, simp)

lemma adm_not_less: "cont t \<Longrightarrow> adm (\<lambda>x. \<not> t x \<sqsubseteq> u)"
apply (rule admI)
apply (drule_tac x=0 in spec)
apply (erule contrapos_nn)
apply (rule trans_less)
prefer 2 apply (assumption)
apply (erule cont2mono [THEN monofun_fun_arg])
apply (erule is_ub_thelub)
done

lemma adm_all: "\<forall>y. adm (P y) \<Longrightarrow> adm (\<lambda>x. \<forall>y. P y x)"
by (fast intro: admI elim: admD)

lemmas adm_all2 = adm_all [rule_format]

lemma adm_subst: "\<lbrakk>cont t; adm P\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P (t x))"
apply (rule admI)
apply (simp add: cont2contlub [THEN contlubE])
apply (erule admD)
apply (erule (1) cont2mono [THEN ch2ch_monofun])
apply assumption
done

lemma adm_UU_not_less: "adm (\<lambda>x. \<not> \<bottom> \<sqsubseteq> t x)"
by (simp add: adm_not_free)

lemma adm_not_UU: "cont t \<Longrightarrow> adm (\<lambda>x. \<not> t x = \<bottom>)"
by (simp add: eq_UU_iff adm_not_less)

lemma adm_eq: "\<lbrakk>cont u; cont v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x = v x)"
by (simp add: po_eq_conv adm_conj adm_less)

text {* admissibility for disjunction is hard to prove. It takes 7 Lemmas *}

lemma adm_disj_lemma1:
  "\<forall>n::nat. P n \<or> Q n \<Longrightarrow> (\<forall>i. \<exists>j\<ge>i. P j) \<or> (\<forall>i. \<exists>j\<ge>i. Q j)"
apply (erule contrapos_pp)
apply clarsimp
apply (rule exI)
apply (rule conjI)
apply (drule spec, erule mp)
apply (rule le_maxI1)
apply (drule spec, erule mp)
apply (rule le_maxI2)
done

lemma adm_disj_lemma2:
  "\<lbrakk>adm P; \<exists>X. chain X \<and> (\<forall>n. P (X n)) \<and> (\<Squnion>i. Y i) = (\<Squnion>i. X i)\<rbrakk>
    \<Longrightarrow> P (\<Squnion>i. Y i)"
by (force elim: admD)

lemma adm_disj_lemma3: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk>
    \<Longrightarrow> chain (\<lambda>m. Y (LEAST j. m \<le> j \<and> P (Y j)))"
apply (rule chainI)
apply (erule chain_mono3)
apply (rule Least_le)
apply (drule_tac x="Suc i" in spec)
apply (rule conjI)
apply (rule Suc_leD)
apply (erule LeastI_ex [THEN conjunct1])
apply (erule LeastI_ex [THEN conjunct2])
done

lemma adm_disj_lemma4: 
  "\<lbrakk>\<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk> \<Longrightarrow> \<forall>m. P (Y (LEAST j::nat. m \<le> j \<and> P (Y j)))"
apply (rule allI)
apply (drule_tac x=m in spec)
apply (erule LeastI_ex [THEN conjunct2])
done

lemma adm_disj_lemma5: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk> \<Longrightarrow> 
    (\<Squnion>m. Y m) = (\<Squnion>m. Y (LEAST j. m \<le> j \<and> P (Y j)))"
 apply (rule antisym_less)
  apply (rule lub_mono)
    apply assumption
   apply (erule (1) adm_disj_lemma3)
  apply (rule allI)
  apply (erule chain_mono3)
  apply (drule_tac x=k in spec)
  apply (erule LeastI_ex [THEN conjunct1])
 apply (rule lub_mono3)
   apply (erule (1) adm_disj_lemma3)
  apply assumption
 apply (rule allI)
 apply (rule exI)
 apply (rule refl_less)
done

lemma adm_disj_lemma6:
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); \<forall>i. \<exists>j\<ge>i. P(Y j)\<rbrakk> \<Longrightarrow>
    \<exists>X. chain X \<and> (\<forall>n. P (X n)) \<and> (\<Squnion>i. Y i) = (\<Squnion>i. X i)"
apply (rule_tac x = "\<lambda>m. Y (LEAST j. m \<le> j \<and> P (Y j))" in exI)
apply (fast intro!: adm_disj_lemma3 adm_disj_lemma4 adm_disj_lemma5)
done

lemma adm_disj_lemma7:
  "\<lbrakk>adm P; chain Y; \<forall>i. \<exists>j\<ge>i. P (Y j)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)"
apply (erule adm_disj_lemma2)
apply (erule (1) adm_disj_lemma6)
done

lemma adm_disj: "\<lbrakk>adm P; adm Q\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<or> Q x)"
apply (rule admI)
apply (erule adm_disj_lemma1 [THEN disjE])
apply (rule disjI1)
apply (erule (2) adm_disj_lemma7)
apply (rule disjI2)
apply (erule (2) adm_disj_lemma7)
done

lemma adm_imp: "\<lbrakk>adm (\<lambda>x. \<not> P x); adm Q\<rbrakk> \<Longrightarrow> adm (\<lambda>x. P x \<longrightarrow> Q x)"
by (subst imp_conv_disj, rule adm_disj)

lemma adm_iff:
  "\<lbrakk>adm (\<lambda>x. P x \<longrightarrow> Q x); adm (\<lambda>x. Q x \<longrightarrow> P x)\<rbrakk>  
    \<Longrightarrow> adm (\<lambda>x. P x = Q x)"
by (subst iff_conv_conj_imp, rule adm_conj)

lemma adm_not_conj:
  "\<lbrakk>adm (\<lambda>x. \<not> P x); adm (\<lambda>x. \<not> Q x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. \<not> (P x \<and> Q x))"
by (subst de_Morgan_conj, rule adm_disj)

lemmas adm_lemmas =
  adm_less adm_conj adm_not_free adm_imp adm_disj adm_eq adm_not_UU
  adm_UU_not_less adm_all2 adm_not_less adm_not_conj adm_iff

declare adm_lemmas [simp]

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
val adm_subst = thm "adm_subst";
val adm_UU_not_less = thm "adm_UU_not_less";
val adm_not_UU = thm "adm_not_UU";
val adm_eq = thm "adm_eq";
val adm_disj_lemma1 = thm "adm_disj_lemma1";
val adm_disj_lemma2 = thm "adm_disj_lemma2";
val adm_disj_lemma3 = thm "adm_disj_lemma3";
val adm_disj_lemma4 = thm "adm_disj_lemma4";
val adm_disj_lemma5 = thm "adm_disj_lemma5";
val adm_disj_lemma6 = thm "adm_disj_lemma6";
val adm_disj_lemma7 = thm "adm_disj_lemma7";
val adm_disj = thm "adm_disj";
val adm_imp = thm "adm_imp";
val adm_iff = thm "adm_iff";
val adm_not_conj = thm "adm_not_conj";
val adm_lemmas = thms "adm_lemmas";
*}

end

