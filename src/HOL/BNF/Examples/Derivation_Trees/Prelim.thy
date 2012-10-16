(*  Title:      HOL/BNF/Examples/Derivation_Trees/Prelim.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Preliminaries.
*)

header {* Preliminaries *}

theory Prelim
imports "../../BNF" "../../More_BNFs"
begin

declare fset_to_fset[simp]

lemma fst_snd_convol_o[simp]: "<fst o s, snd o s> = s"
apply(rule ext) by (simp add: convol_def)

abbreviation sm_abbrev (infix "\<oplus>" 60)
where "f \<oplus> g \<equiv> Sum_Type.sum_map f g"

lemma sum_map_InlD: "(f \<oplus> g) z = Inl x \<Longrightarrow> \<exists>y. z = Inl y \<and> f y = x"
by (cases z) auto

lemma sum_map_InrD: "(f \<oplus> g) z = Inr x \<Longrightarrow> \<exists>y. z = Inr y \<and> g y = x"
by (cases z) auto

abbreviation sum_case_abbrev ("[[_,_]]" 800)
where "[[f,g]] \<equiv> Sum_Type.sum_case f g"

lemma inj_Inl[simp]: "inj Inl" unfolding inj_on_def by auto
lemma inj_Inr[simp]: "inj Inr" unfolding inj_on_def by auto

lemma Inl_oplus_elim:
assumes "Inl tr \<in> (id \<oplus> f) ` tns"
shows "Inl tr \<in> tns"
using assms apply clarify by (case_tac x, auto)

lemma Inl_oplus_iff[simp]: "Inl tr \<in> (id \<oplus> f) ` tns \<longleftrightarrow> Inl tr \<in> tns"
using Inl_oplus_elim
by (metis id_def image_iff sum_map.simps(1))

lemma Inl_m_oplus[simp]: "Inl -` (id \<oplus> f) ` tns = Inl -` tns"
using Inl_oplus_iff unfolding vimage_def by auto

lemma Inr_oplus_elim:
assumes "Inr tr \<in> (id \<oplus> f) ` tns"
shows "\<exists> n. Inr n \<in> tns \<and> f n = tr"
using assms apply clarify by (case_tac x, auto)

lemma Inr_oplus_iff[simp]:
"Inr tr \<in> (id \<oplus> f) ` tns \<longleftrightarrow> (\<exists> n. Inr n \<in> tns \<and> f n = tr)"
apply (rule iffI)
 apply (metis Inr_oplus_elim)
by (metis image_iff sum_map.simps(2))

lemma Inr_m_oplus[simp]: "Inr -` (id \<oplus> f) ` tns = f ` (Inr -` tns)"
using Inr_oplus_iff unfolding vimage_def by auto

lemma Inl_Inr_image_cong:
assumes "Inl -` A = Inl -` B" and "Inr -` A = Inr -` B"
shows "A = B"
apply safe using assms apply(case_tac x, auto) by(case_tac x, auto)

end