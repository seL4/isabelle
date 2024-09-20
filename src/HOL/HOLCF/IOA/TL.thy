(*  Title:      HOL/HOLCF/IOA/TL.thy
    Author:     Olaf Müller
*)

section \<open>A General Temporal Logic\<close>

theory TL
imports Pred Sequence
begin

default_sort type

type_synonym 'a temporal = "'a Seq predicate"

definition validT :: "'a Seq predicate \<Rightarrow> bool"    (\<open>\<^bold>\<TTurnstile> _\<close> [9] 8)
  where "(\<^bold>\<TTurnstile> P) \<longleftrightarrow> (\<forall>s. s \<noteq> UU \<and> s \<noteq> nil \<longrightarrow> (s \<Turnstile> P))"

definition unlift :: "'a lift \<Rightarrow> 'a"
  where "unlift x = (case x of Def y \<Rightarrow> y)"

definition Init :: "'a predicate \<Rightarrow> 'a temporal"  (\<open>\<langle>_\<rangle>\<close> [0] 1000)
  where "Init P s = P (unlift (HD \<cdot> s))"
    \<comment> \<open>this means that for \<open>nil\<close> and \<open>UU\<close> the effect is unpredictable\<close>

definition Next :: "'a temporal \<Rightarrow> 'a temporal"  (\<open>\<circle>(_)\<close> [80] 80)
  where "(\<circle>P) s \<longleftrightarrow> (if TL \<cdot> s = UU \<or> TL \<cdot> s = nil then P s else P (TL \<cdot> s))"

definition suffix :: "'a Seq \<Rightarrow> 'a Seq \<Rightarrow> bool"
  where "suffix s2 s \<longleftrightarrow> (\<exists>s1. Finite s1 \<and> s = s1 @@ s2)"

definition tsuffix :: "'a Seq \<Rightarrow> 'a Seq \<Rightarrow> bool"
  where "tsuffix s2 s \<longleftrightarrow> s2 \<noteq> nil \<and> s2 \<noteq> UU \<and> suffix s2 s"

definition Box :: "'a temporal \<Rightarrow> 'a temporal"  (\<open>\<box>(_)\<close> [80] 80)
  where "(\<box>P) s \<longleftrightarrow> (\<forall>s2. tsuffix s2 s \<longrightarrow> P s2)"

definition Diamond :: "'a temporal \<Rightarrow> 'a temporal"  (\<open>\<diamond>(_)\<close> [80] 80)
  where "\<diamond>P = (\<^bold>\<not> (\<box>(\<^bold>\<not> P)))"

definition Leadsto :: "'a temporal \<Rightarrow> 'a temporal \<Rightarrow> 'a temporal"  (infixr \<open>\<leadsto>\<close> 22)
  where "(P \<leadsto> Q) = (\<box>(P \<^bold>\<longrightarrow> (\<diamond>Q)))"


lemma simple: "\<box>\<diamond>(\<^bold>\<not> P) = (\<^bold>\<not> \<diamond>\<box>P)"
  by (auto simp add: Diamond_def NOT_def Box_def)

lemma Boxnil: "nil \<Turnstile> \<box>P"
  by (simp add: satisfies_def Box_def tsuffix_def suffix_def nil_is_Conc)

lemma Diamondnil: "\<not> (nil \<Turnstile> \<diamond>P)"
  using Boxnil by (simp add: Diamond_def satisfies_def NOT_def)

lemma Diamond_def2: "(\<diamond>F) s \<longleftrightarrow> (\<exists>s2. tsuffix s2 s \<and> F s2)"
  by (simp add: Diamond_def NOT_def Box_def)


subsection \<open>TLA Axiomatization by Merz\<close>

lemma suffix_refl: "suffix s s"
  apply (simp add: suffix_def)
  apply (rule_tac x = "nil" in exI)
  apply auto
  done

lemma reflT: "s \<noteq> UU \<and> s \<noteq> nil \<longrightarrow> (s \<Turnstile> \<box>F \<^bold>\<longrightarrow> F)"
  apply (simp add: satisfies_def IMPLIES_def Box_def)
  apply (rule impI)+
  apply (erule_tac x = "s" in allE)
  apply (simp add: tsuffix_def suffix_refl)
  done

lemma suffix_trans: "suffix y x \<Longrightarrow> suffix z y \<Longrightarrow> suffix z x"
  apply (simp add: suffix_def)
  apply auto
  apply (rule_tac x = "s1 @@ s1a" in exI)
  apply auto
  apply (simp add: Conc_assoc)
  done

lemma transT: "s \<Turnstile> \<box>F \<^bold>\<longrightarrow> \<box>\<box>F"
  apply (simp add: satisfies_def IMPLIES_def Box_def tsuffix_def)
  apply auto
  apply (drule suffix_trans)
  apply assumption
  apply (erule_tac x = "s2a" in allE)
  apply auto
  done

lemma normalT: "s \<Turnstile> \<box>(F \<^bold>\<longrightarrow> G) \<^bold>\<longrightarrow> \<box>F \<^bold>\<longrightarrow> \<box>G"
  by (simp add: satisfies_def IMPLIES_def Box_def)


subsection \<open>TLA Rules by Lamport\<close>

lemma STL1a: "\<^bold>\<TTurnstile> P \<Longrightarrow> \<^bold>\<TTurnstile> (\<box>P)"
  by (simp add: validT_def satisfies_def Box_def tsuffix_def)

lemma STL1b: "\<TTurnstile> P \<Longrightarrow> \<^bold>\<TTurnstile> (Init P)"
  by (simp add: valid_def validT_def satisfies_def Init_def)

lemma STL1: "\<TTurnstile> P \<Longrightarrow> \<^bold>\<TTurnstile> (\<box>(Init P))"
  apply (rule STL1a)
  apply (erule STL1b)
  done

(*Note that unlift and HD is not at all used!*)
lemma STL4: "\<TTurnstile> (P \<^bold>\<longrightarrow> Q) \<Longrightarrow> \<^bold>\<TTurnstile> (\<box>(Init P) \<^bold>\<longrightarrow> \<box>(Init Q))"
  by (simp add: valid_def validT_def satisfies_def IMPLIES_def Box_def Init_def)


subsection \<open>LTL Axioms by Manna/Pnueli\<close>

lemma tsuffix_TL [rule_format]: "s \<noteq> UU \<and> s \<noteq> nil \<longrightarrow> tsuffix s2 (TL \<cdot> s) \<longrightarrow> tsuffix s2 s"
  apply (unfold tsuffix_def suffix_def)
  apply auto
  apply (Seq_case_simp s)
  apply (rule_tac x = "a \<leadsto> s1" in exI)
  apply auto
  done

lemmas tsuffix_TL2 = conjI [THEN tsuffix_TL]

lemma LTL1: "s \<noteq> UU \<and> s \<noteq> nil \<longrightarrow> (s \<Turnstile> \<box>F \<^bold>\<longrightarrow> (F \<^bold>\<and> (\<circle>(\<box>F))))"
  supply if_split [split del] 
  apply (unfold Next_def satisfies_def NOT_def IMPLIES_def AND_def Box_def)
  apply auto
  text \<open>\<open>\<box>F \<^bold>\<longrightarrow> F\<close>\<close>
  apply (erule_tac x = "s" in allE)
  apply (simp add: tsuffix_def suffix_refl)
  text \<open>\<open>\<box>F \<^bold>\<longrightarrow> \<circle>\<box>F\<close>\<close>
  apply (simp split: if_split)
  apply auto
  apply (drule tsuffix_TL2)
  apply assumption+
  apply auto
  done

lemma LTL2a: "s \<Turnstile> \<^bold>\<not> (\<circle>F) \<^bold>\<longrightarrow> (\<circle>(\<^bold>\<not> F))"
  by (simp add: Next_def satisfies_def NOT_def IMPLIES_def)

lemma LTL2b: "s \<Turnstile> (\<circle>(\<^bold>\<not> F)) \<^bold>\<longrightarrow> (\<^bold>\<not> (\<circle>F))"
  by (simp add: Next_def satisfies_def NOT_def IMPLIES_def)

lemma LTL3: "ex \<Turnstile> (\<circle>(F \<^bold>\<longrightarrow> G)) \<^bold>\<longrightarrow> (\<circle>F) \<^bold>\<longrightarrow> (\<circle>G)"
  by (simp add: Next_def satisfies_def NOT_def IMPLIES_def)

lemma ModusPonens: "\<^bold>\<TTurnstile> (P \<^bold>\<longrightarrow> Q) \<Longrightarrow> \<^bold>\<TTurnstile> P \<Longrightarrow> \<^bold>\<TTurnstile> Q"
  by (simp add: validT_def satisfies_def IMPLIES_def)

end
