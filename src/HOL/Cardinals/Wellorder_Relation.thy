(*  Title:      HOL/Cardinals/Wellorder_Relation.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Well-order relations.
*)

section \<open>Well-Order Relations\<close>

theory Wellorder_Relation
  imports Wellfounded_More
begin

context wo_rel
begin

subsection \<open>Auxiliaries\<close>

lemma PREORD: "Preorder r"
  using WELL order_on_defs[of _ r] by auto

lemma PARORD: "Partial_order r"
  using WELL order_on_defs[of _ r] by auto

lemma cases_Total2:
  "\<And> phi a b. \<lbrakk>{a,b} \<le> Field r; ((a,b) \<in> r - Id \<Longrightarrow> phi a b);
              ((b,a) \<in> r - Id \<Longrightarrow> phi a b); (a = b \<Longrightarrow> phi a b)\<rbrakk>
             \<Longrightarrow> phi a b"
  using TOTALS by auto


subsection \<open>Well-founded induction and recursion adapted to non-strict well-order relations\<close>

lemma worec_unique_fixpoint:
  assumes ADM: "adm_wo H" and fp: "f = H f"
  shows "f = worec H"
proof-
  have "adm_wf (r - Id) H"
    unfolding adm_wf_def
    using ADM adm_wo_def[of H] underS_def[of r] by auto
  hence "f = wfrec (r - Id) H"
    using fp WF wfrec_unique_fixpoint[of "r - Id" H] by simp
  thus ?thesis unfolding worec_def .
qed


subsubsection \<open>Properties of max2\<close>

lemma max2_iff:
  assumes "a \<in> Field r" and "b \<in> Field r"
  shows "((max2 a b, c) \<in> r) = ((a,c) \<in> r \<and> (b,c) \<in> r)"
proof
  assume "(max2 a b, c) \<in> r"
  thus "(a,c) \<in> r \<and> (b,c) \<in> r"
    using assms max2_greater[of a b] TRANS trans_def[of r] by blast
next
  assume "(a,c) \<in> r \<and> (b,c) \<in> r"
  thus "(max2 a b, c) \<in> r"
    using assms max2_among[of a b] by auto
qed


subsubsection \<open>Properties of minim\<close>

lemma minim_Under:
  "\<lbrakk>B \<le> Field r; B \<noteq> {}\<rbrakk> \<Longrightarrow> minim B \<in> Under B"
  by(auto simp add: Under_def minim_inField minim_least)

lemma equals_minim_Under:
  "\<lbrakk>B \<le> Field r; a \<in> B; a \<in> Under B\<rbrakk>
 \<Longrightarrow> a = minim B"
  by(auto simp add: Under_def equals_minim)

lemma minim_iff_In_Under:
  assumes SUB: "B \<le> Field r" and NE: "B \<noteq> {}"
  shows "(a = minim B) = (a \<in> B \<and> a \<in> Under B)"
proof
  assume "a = minim B"
  thus "a \<in> B \<and> a \<in> Under B"
    using assms minim_in minim_Under by simp
next
  assume "a \<in> B \<and> a \<in> Under B"
  thus "a = minim B"
    using assms equals_minim_Under by simp
qed

lemma minim_Under_under:
  assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
  shows "Under A = under (minim A)"
proof-
  have "minim A \<in> A"
    using assms minim_in by auto
  then have "Under A \<le> under (minim A)"
    by (simp add: Under_decr under_Under_singl)
  moreover have "under (minim A) \<le> Under A"
    by (meson NE SUB TRANS minim_Under subset_eq under_Under_trans)
  ultimately show ?thesis by blast
qed

lemma minim_UnderS_underS:
  assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
  shows "UnderS A = underS (minim A)"
proof-
  have "minim A \<in> A"
    using assms minim_in by auto
  then have "UnderS A \<le> underS (minim A)"
    by (simp add: UnderS_decr underS_UnderS_singl)
  moreover have "underS (minim A) \<le> UnderS A"
    by (meson ANTISYM NE SUB TRANS minim_Under subset_eq underS_Under_trans)
  ultimately show ?thesis by blast
qed


subsubsection \<open>Properties of supr\<close>

lemma supr_Above:
  assumes "Above B \<noteq> {}"
  shows "supr B \<in> Above B"
  by (simp add: assms Above_Field minim_in supr_def)

lemma supr_greater:
  assumes "Above B \<noteq> {}" "b \<in> B"
  shows "(b, supr B) \<in> r"
  using assms Above_def supr_Above by fastforce

lemma supr_least_Above:
  assumes "a \<in> Above B"
  shows "(supr B, a) \<in> r"
  by (simp add: assms Above_Field minim_least supr_def)

lemma supr_least:
  "\<lbrakk>B \<le> Field r; a \<in> Field r; (\<And> b. b \<in> B \<Longrightarrow> (b,a) \<in> r)\<rbrakk>
 \<Longrightarrow> (supr B, a) \<in> r"
  by(auto simp add: supr_least_Above Above_def)

lemma equals_supr_Above:
  assumes "a \<in> Above B" "\<And> a'. a' \<in> Above B \<Longrightarrow> (a,a') \<in> r"
  shows "a = supr B"
  by (simp add: assms Above_Field equals_minim supr_def)

lemma equals_supr:
  assumes SUB: "B \<le> Field r" and IN: "a \<in> Field r" and
    ABV: "\<And> b. b \<in> B \<Longrightarrow> (b,a) \<in> r" and
    MINIM: "\<And> a'. \<lbrakk> a' \<in> Field r; \<And> b. b \<in> B \<Longrightarrow> (b,a') \<in> r\<rbrakk> \<Longrightarrow> (a,a') \<in> r"
  shows "a = supr B"
proof-
  have "a \<in> Above B"
    unfolding Above_def using ABV IN by simp
  moreover
  have "\<And> a'. a' \<in> Above B \<Longrightarrow> (a,a') \<in> r"
    unfolding Above_def using MINIM by simp
  ultimately show ?thesis
    using equals_supr_Above SUB by auto
qed

lemma supr_inField:
  assumes "Above B \<noteq> {}"
  shows "supr B \<in> Field r"
  by (simp add: Above_Field assms minim_inField supr_def)

lemma supr_above_Above:
  assumes SUB: "B \<le> Field r" and  ABOVE: "Above B \<noteq> {}"
  shows "Above B = above (supr B)"
  apply (clarsimp simp: Above_def above_def set_eq_iff)
  by (meson ABOVE FieldI2 SUB TRANS supr_greater supr_least transD)

lemma supr_under:
  assumes "a \<in> Field r"
  shows "a = supr (under a)"
proof-
  have "under a \<le> Field r"
    using under_Field[of r] by auto
  moreover
  have "under a \<noteq> {}"
    using assms Refl_under_in[of r] REFL by auto
  moreover
  have "a \<in> Above (under a)"
    using in_Above_under[of _ r] assms by auto
  moreover
  have "\<forall>a' \<in> Above (under a). (a,a') \<in> r"
    by (auto simp: Above_def above_def REFL Refl_under_in assms)
  ultimately show ?thesis
    using equals_supr_Above by auto
qed


subsubsection \<open>Properties of successor\<close>

lemma suc_least:
  "\<lbrakk>B \<le> Field r; a \<in> Field r; (\<And> b. b \<in> B \<Longrightarrow> a \<noteq> b \<and> (b,a) \<in> r)\<rbrakk>
 \<Longrightarrow> (suc B, a) \<in> r"
  by(auto simp add: suc_least_AboveS AboveS_def)

lemma equals_suc:
  assumes SUB: "B \<le> Field r" and IN: "a \<in> Field r" and
    ABVS: "\<And> b. b \<in> B \<Longrightarrow> a \<noteq> b \<and> (b,a) \<in> r" and
    MINIM: "\<And> a'. \<lbrakk>a' \<in> Field r; \<And> b. b \<in> B \<Longrightarrow> a' \<noteq> b \<and> (b,a') \<in> r\<rbrakk> \<Longrightarrow> (a,a') \<in> r"
  shows "a = suc B"
proof-
  have "a \<in> AboveS B"
    unfolding AboveS_def using ABVS IN by simp
  moreover
  have "\<And> a'. a' \<in> AboveS B \<Longrightarrow> (a,a') \<in> r"
    unfolding AboveS_def using MINIM by simp
  ultimately show ?thesis
    using equals_suc_AboveS SUB by auto
qed

lemma suc_above_AboveS:
  assumes SUB: "B \<le> Field r" and
    ABOVE: "AboveS B \<noteq> {}"
  shows "AboveS B = above (suc B)"
  using assms
proof(unfold AboveS_def above_def, auto)
  fix a assume "a \<in> Field r" "\<forall>b \<in> B. a \<noteq> b \<and> (b,a) \<in> r"
  with suc_least assms
  show "(suc B,a) \<in> r" by auto
next
  fix b assume "(suc B, b) \<in> r"
  thus "b \<in> Field r"
    by (simp add: FieldI2)
next
  fix a b
  assume 1: "(suc B, b) \<in> r" and 2: "a \<in> B"
  with assms suc_greater[of B a]
  have "(a,suc B) \<in> r" by auto
  thus "(a,b) \<in> r"
    using 1 TRANS trans_def[of r] by blast
next
  fix a
  assume "(suc B, a) \<in> r" and 2: "a \<in> B"
  thus False
    by (metis ABOVE ANTISYM SUB antisymD suc_greater)
qed

lemma suc_singl_pred:
  assumes IN: "a \<in> Field r" and ABOVE_NE: "aboveS a \<noteq> {}" and
    REL: "(a',suc {a}) \<in> r" and DIFF: "a' \<noteq> suc {a}"
  shows "a' = a \<or> (a',a) \<in> r"
proof-
  have *: "suc {a} \<in> Field r \<and> a' \<in> Field r"
    using WELL REL well_order_on_domain by metis
  {assume **: "a' \<noteq> a"
    hence "(a,a') \<in> r \<or> (a',a) \<in> r"
      using TOTAL IN * by (auto simp add: total_on_def)
    moreover
    {assume "(a,a') \<in> r"
      with ** * assms WELL suc_least[of "{a}" a']
      have "(suc {a},a') \<in> r" by auto
      with REL DIFF * ANTISYM antisym_def[of r]
      have False by simp
    }
    ultimately have "(a',a) \<in> r"
      by blast
  }
  thus ?thesis by blast
qed

lemma under_underS_suc:
  assumes IN: "a \<in> Field r" and ABV: "aboveS a \<noteq> {}"
  shows "underS (suc {a}) = under a"
proof -
  have "AboveS {a} \<noteq> {}"
    using ABV aboveS_AboveS_singl[of r] by auto
  then have 2: "a \<noteq> suc {a} \<and> (a,suc {a}) \<in> r"
    using suc_greater[of "{a}" a] IN  by auto
  have "underS (suc {a}) \<le> under a"
    using ABV IN REFL Refl_under_in underS_E under_def wo_rel.suc_singl_pred wo_rel_axioms by fastforce
  moreover
  have "under a \<le> underS (suc {a})"
    by (simp add: "2" ANTISYM TRANS subsetI underS_I under_underS_trans)
  ultimately show ?thesis by blast
qed


subsubsection \<open>Properties of order filters\<close>

lemma ofilter_Under[simp]:
  assumes "A \<le> Field r"
  shows "ofilter(Under A)"
  by (clarsimp simp: ofilter_def) (meson TRANS Under_Field subset_eq under_Under_trans)

lemma ofilter_UnderS[simp]:
  assumes "A \<le> Field r"
  shows "ofilter(UnderS A)"
  by (clarsimp simp: ofilter_def) (meson ANTISYM TRANS UnderS_Field subset_eq under_UnderS_trans)

lemma ofilter_Int[simp]: "\<lbrakk>ofilter A; ofilter B\<rbrakk> \<Longrightarrow> ofilter(A Int B)"
  unfolding ofilter_def by blast

lemma ofilter_Un[simp]: "\<lbrakk>ofilter A; ofilter B\<rbrakk> \<Longrightarrow> ofilter(A \<union> B)"
  unfolding ofilter_def by blast

lemma ofilter_INTER:
  "\<lbrakk>I \<noteq> {}; \<And> i. i \<in> I \<Longrightarrow> ofilter(A i)\<rbrakk> \<Longrightarrow> ofilter (\<Inter>i \<in> I. A i)"
  unfolding ofilter_def by blast

lemma ofilter_Inter:
  "\<lbrakk>S \<noteq> {}; \<And> A. A \<in> S \<Longrightarrow> ofilter A\<rbrakk> \<Longrightarrow> ofilter (\<Inter>S)"
  unfolding ofilter_def by blast

lemma ofilter_Union:
  "(\<And> A. A \<in> S \<Longrightarrow> ofilter A) \<Longrightarrow> ofilter (\<Union>S)"
  unfolding ofilter_def by blast

lemma ofilter_under_Union:
  "ofilter A \<Longrightarrow> A = \<Union>{under a| a. a \<in> A}"
  using ofilter_under_UNION [of A] by auto


subsubsection \<open>Other properties\<close>

lemma Trans_Under_regressive:
  assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
  shows "Under(Under A) \<le> Under A"
  by (metis INT_E NE REFL Refl_under_Under SUB empty_iff minim_Under minim_Under_under subsetI)

lemma ofilter_suc_Field:
  assumes OF: "ofilter A" and NE: "A \<noteq> Field r"
  shows "ofilter (A \<union> {suc A})"
  by (metis NE OF REFL Refl_under_underS ofilter_underS_Field suc_underS under_ofilter)

(* FIXME: needed? *)
declare
  minim_in[simp]
  minim_inField[simp]
  minim_least[simp]
  under_ofilter[simp]
  underS_ofilter[simp]
  Field_ofilter[simp]

end

abbreviation "worec \<equiv> wo_rel.worec"
abbreviation "adm_wo \<equiv> wo_rel.adm_wo"
abbreviation "isMinim \<equiv> wo_rel.isMinim"
abbreviation "minim \<equiv> wo_rel.minim"
abbreviation "max2 \<equiv> wo_rel.max2"
abbreviation "supr \<equiv> wo_rel.supr"
abbreviation "suc \<equiv> wo_rel.suc"

end
