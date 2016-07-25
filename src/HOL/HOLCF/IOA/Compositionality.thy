(*  Title:      HOL/HOLCF/IOA/Compositionality.thy
    Author:     Olaf Müller
*)

section \<open>Compositionality of I/O automata\<close>
theory Compositionality
imports CompoTraces
begin

lemma compatibility_consequence3: "eA \<longrightarrow> A \<Longrightarrow> eB \<and> \<not> eA \<longrightarrow> \<not> A \<Longrightarrow> (eA \<or> eB) \<longrightarrow> A = eA"
  by auto

lemma Filter_actAisFilter_extA:
  "compatible A B \<Longrightarrow> Forall (\<lambda>a. a \<in> ext A \<or> a \<in> ext B) tr \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act A) \<cdot> tr = Filter (\<lambda>a. a \<in> ext A) \<cdot> tr"
  apply (rule ForallPFilterQR)
  text \<open>i.e.: \<open>(\<forall>x. P x \<longrightarrow> (Q x = R x)) \<Longrightarrow> Forall P tr \<Longrightarrow> Filter Q \<cdot> tr = Filter R \<cdot> tr\<close>\<close>
  prefer 2 apply assumption
  apply (rule compatibility_consequence3)
  apply (simp_all add: ext_is_act ext1_ext2_is_not_act1)
  done


text \<open>
  The next two theorems are only necessary, as there is no theorem
  \<open>ext (A \<parallel> B) = ext (B \<parallel> A)\<close>
\<close>

lemma compatibility_consequence4: "eA \<longrightarrow> A \<Longrightarrow> eB \<and> \<not> eA \<longrightarrow> \<not> A \<Longrightarrow> (eB \<or> eA) \<longrightarrow> A = eA"
  by auto

lemma Filter_actAisFilter_extA2:
  "compatible A B \<Longrightarrow> Forall (\<lambda>a. a \<in> ext B \<or> a \<in> ext A) tr \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act A) \<cdot> tr = Filter (\<lambda>a. a \<in> ext A) \<cdot> tr"
  apply (rule ForallPFilterQR)
  prefer 2 apply (assumption)
  apply (rule compatibility_consequence4)
  apply (simp_all add: ext_is_act ext1_ext2_is_not_act1)
  done


subsection \<open>Main Compositionality Theorem\<close>

lemma compositionality:
  assumes "is_trans_of A1" and "is_trans_of A2"
    and "is_trans_of B1" and "is_trans_of B2"
    and "is_asig_of A1" and "is_asig_of A2"
    and "is_asig_of B1" and "is_asig_of B2"
    and "compatible A1 B1" and "compatible A2 B2"
    and "A1 =<| A2" and "B1 =<| B2"
  shows "(A1 \<parallel> B1) =<| (A2 \<parallel> B2)"
  apply (insert assms)
  apply (simp add: is_asig_of_def)
  apply (frule_tac A1 = "A1" in compat_commute [THEN iffD1])
  apply (frule_tac A1 = "A2" in compat_commute [THEN iffD1])
  apply (simp add: ioa_implements_def inputs_of_par outputs_of_par externals_of_par)
  apply auto
  apply (simp add: compositionality_tr)
  apply (subgoal_tac "ext A1 = ext A2 \<and> ext B1 = ext B2")
  prefer 2
  apply (simp add: externals_def)
  apply (erule conjE)+
  text \<open>rewrite with proven subgoal\<close>
  apply (simp add: externals_of_par)
  apply auto
  text \<open>2 goals, the 3rd has been solved automatically\<close>
  text \<open>1: \<open>Filter A2 x \<in> traces A2\<close>\<close>
  apply (drule_tac A = "traces A1" in subsetD)
  apply assumption
  apply (simp add: Filter_actAisFilter_extA)
  text \<open>2: \<open>Filter B2 x \<in> traces B2\<close>\<close>
  apply (drule_tac A = "traces B1" in subsetD)
  apply assumption
  apply (simp add: Filter_actAisFilter_extA2)
  done

end
