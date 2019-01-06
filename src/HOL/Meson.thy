(*  Title:      HOL/Meson.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Tobias Nipkow, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2001  University of Cambridge
*)

section \<open>MESON Proof Method\<close>

theory Meson
imports Nat
begin

subsection \<open>Negation Normal Form\<close>

text \<open>de Morgan laws\<close>

lemma not_conjD: "\<not>(P\<and>Q) \<Longrightarrow> \<not>P \<or> \<not>Q"
  and not_disjD: "\<not>(P\<or>Q) \<Longrightarrow> \<not>P \<and> \<not>Q"
  and not_notD: "\<not>\<not>P \<Longrightarrow> P"
  and not_allD: "\<And>P. \<not>(\<forall>x. P(x)) \<Longrightarrow> \<exists>x. \<not>P(x)"
  and not_exD: "\<And>P. \<not>(\<exists>x. P(x)) \<Longrightarrow> \<forall>x. \<not>P(x)"
  by fast+

text \<open>Removal of \<open>\<longrightarrow>\<close> and \<open>\<longleftrightarrow>\<close> (positive and negative occurrences)\<close>

lemma imp_to_disjD: "P\<longrightarrow>Q \<Longrightarrow> \<not>P \<or> Q"
  and not_impD: "\<not>(P\<longrightarrow>Q) \<Longrightarrow> P \<and> \<not>Q"
  and iff_to_disjD: "P=Q \<Longrightarrow> (\<not>P \<or> Q) \<and> (\<not>Q \<or> P)"
  and not_iffD: "\<not>(P=Q) \<Longrightarrow> (P \<or> Q) \<and> (\<not>P \<or> \<not>Q)"
    \<comment> \<open>Much more efficient than \<^prop>\<open>(P \<and> \<not>Q) \<or> (Q \<and> \<not>P)\<close> for computing CNF\<close>
  and not_refl_disj_D: "x \<noteq> x \<or> P \<Longrightarrow> P"
  by fast+


subsection \<open>Pulling out the existential quantifiers\<close>

text \<open>Conjunction\<close>

lemma conj_exD1: "\<And>P Q. (\<exists>x. P(x)) \<and> Q \<Longrightarrow> \<exists>x. P(x) \<and> Q"
  and conj_exD2: "\<And>P Q. P \<and> (\<exists>x. Q(x)) \<Longrightarrow> \<exists>x. P \<and> Q(x)"
  by fast+


text \<open>Disjunction\<close>

lemma disj_exD: "\<And>P Q. (\<exists>x. P(x)) \<or> (\<exists>x. Q(x)) \<Longrightarrow> \<exists>x. P(x) \<or> Q(x)"
  \<comment> \<open>DO NOT USE with forall-Skolemization: makes fewer schematic variables!!\<close>
  \<comment> \<open>With ex-Skolemization, makes fewer Skolem constants\<close>
  and disj_exD1: "\<And>P Q. (\<exists>x. P(x)) \<or> Q \<Longrightarrow> \<exists>x. P(x) \<or> Q"
  and disj_exD2: "\<And>P Q. P \<or> (\<exists>x. Q(x)) \<Longrightarrow> \<exists>x. P \<or> Q(x)"
  by fast+

lemma disj_assoc: "(P\<or>Q)\<or>R \<Longrightarrow> P\<or>(Q\<or>R)"
  and disj_comm: "P\<or>Q \<Longrightarrow> Q\<or>P"
  and disj_FalseD1: "False\<or>P \<Longrightarrow> P"
  and disj_FalseD2: "P\<or>False \<Longrightarrow> P"
  by fast+


text\<open>Generation of contrapositives\<close>

text\<open>Inserts negated disjunct after removing the negation; P is a literal.
  Model elimination requires assuming the negation of every attempted subgoal,
  hence the negated disjuncts.\<close>
lemma make_neg_rule: "\<not>P\<or>Q \<Longrightarrow> ((\<not>P\<Longrightarrow>P) \<Longrightarrow> Q)"
by blast

text\<open>Version for Plaisted's "Postive refinement" of the Meson procedure\<close>
lemma make_refined_neg_rule: "\<not>P\<or>Q \<Longrightarrow> (P \<Longrightarrow> Q)"
by blast

text\<open>\<^term>\<open>P\<close> should be a literal\<close>
lemma make_pos_rule: "P\<or>Q \<Longrightarrow> ((P\<Longrightarrow>\<not>P) \<Longrightarrow> Q)"
by blast

text\<open>Versions of \<open>make_neg_rule\<close> and \<open>make_pos_rule\<close> that don't
insert new assumptions, for ordinary resolution.\<close>

lemmas make_neg_rule' = make_refined_neg_rule

lemma make_pos_rule': "\<lbrakk>P\<or>Q; \<not>P\<rbrakk> \<Longrightarrow> Q"
by blast

text\<open>Generation of a goal clause -- put away the final literal\<close>

lemma make_neg_goal: "\<not>P \<Longrightarrow> ((\<not>P\<Longrightarrow>P) \<Longrightarrow> False)"
by blast

lemma make_pos_goal: "P \<Longrightarrow> ((P\<Longrightarrow>\<not>P) \<Longrightarrow> False)"
by blast


subsection \<open>Lemmas for Forward Proof\<close>

text\<open>There is a similarity to congruence rules. They are also useful in ordinary proofs.\<close>

(*NOTE: could handle conjunctions (faster?) by
    nf(th RS conjunct2) RS (nf(th RS conjunct1) RS conjI) *)
lemma conj_forward: "\<lbrakk>P'\<and>Q';  P' \<Longrightarrow> P;  Q' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> P\<and>Q"
by blast

lemma disj_forward: "\<lbrakk>P'\<or>Q';  P' \<Longrightarrow> P;  Q' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> P\<or>Q"
by blast

lemma imp_forward: "\<lbrakk>P' \<longrightarrow> Q';  P \<Longrightarrow> P';  Q' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> P \<longrightarrow> Q"
by blast

lemma imp_forward2: "\<lbrakk>P' \<longrightarrow> Q';  P \<Longrightarrow> P';  P' \<Longrightarrow> Q' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> P \<longrightarrow> Q"
  by blast

(*Version of @{text disj_forward} for removal of duplicate literals*)
lemma disj_forward2: "\<lbrakk> P'\<or>Q';  P' \<Longrightarrow> P;  \<lbrakk>Q'; P\<Longrightarrow>False\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> P\<or>Q"
apply blast 
done

lemma all_forward: "[| \<forall>x. P'(x);  !!x. P'(x) ==> P(x) |] ==> \<forall>x. P(x)"
by blast

lemma ex_forward: "[| \<exists>x. P'(x);  !!x. P'(x) ==> P(x) |] ==> \<exists>x. P(x)"
by blast


subsection \<open>Clausification helper\<close>

lemma TruepropI: "P \<equiv> Q \<Longrightarrow> Trueprop P \<equiv> Trueprop Q"
by simp

lemma ext_cong_neq: "F g \<noteq> F h \<Longrightarrow> F g \<noteq> F h \<and> (\<exists>x. g x \<noteq> h x)"
apply (erule contrapos_np)
apply clarsimp
apply (rule cong[where f = F])
by auto


text\<open>Combinator translation helpers\<close>

definition COMBI :: "'a \<Rightarrow> 'a" where
"COMBI P = P"

definition COMBK :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
"COMBK P Q = P"

definition COMBB :: "('b => 'c) \<Rightarrow> ('a => 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
"COMBB P Q R = P (Q R)"

definition COMBC :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
"COMBC P Q R = P R Q"

definition COMBS :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
"COMBS P Q R = P R (Q R)"

lemma abs_S: "\<lambda>x. (f x) (g x) \<equiv> COMBS f g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBS_def) 
done

lemma abs_I: "\<lambda>x. x \<equiv> COMBI"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBI_def) 
done

lemma abs_K: "\<lambda>x. y \<equiv> COMBK y"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBK_def) 
done

lemma abs_B: "\<lambda>x. a (g x) \<equiv> COMBB a g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBB_def) 
done

lemma abs_C: "\<lambda>x. (f x) b \<equiv> COMBC f b"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBC_def) 
done


subsection \<open>Skolemization helpers\<close>

definition skolem :: "'a \<Rightarrow> 'a" where
"skolem = (\<lambda>x. x)"

lemma skolem_COMBK_iff: "P \<longleftrightarrow> skolem (COMBK P (i::nat))"
unfolding skolem_def COMBK_def by (rule refl)

lemmas skolem_COMBK_I = iffD1 [OF skolem_COMBK_iff]
lemmas skolem_COMBK_D = iffD2 [OF skolem_COMBK_iff]


subsection \<open>Meson package\<close>

ML_file \<open>Tools/Meson/meson.ML\<close>
ML_file \<open>Tools/Meson/meson_clausify.ML\<close>
ML_file \<open>Tools/Meson/meson_tactic.ML\<close>

hide_const (open) COMBI COMBK COMBB COMBC COMBS skolem
hide_fact (open) not_conjD not_disjD not_notD not_allD not_exD imp_to_disjD
    not_impD iff_to_disjD not_iffD not_refl_disj_D conj_exD1 conj_exD2 disj_exD
    disj_exD1 disj_exD2 disj_assoc disj_comm disj_FalseD1 disj_FalseD2 TruepropI
    ext_cong_neq COMBI_def COMBK_def COMBB_def COMBC_def COMBS_def abs_I abs_K
    abs_B abs_C abs_S skolem_def skolem_COMBK_iff skolem_COMBK_I skolem_COMBK_D

end
