(*  Title:      HOL/Ordinals_and_Cardinals/Wellorder_Relation.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Well-order relations.
*)

header {* Well-Order Relations *}

theory Wellorder_Relation
imports Wellorder_Relation_Base Wellfounded_More
begin


subsection {* Auxiliaries *}

lemma (in wo_rel) PREORD: "Preorder r"
using WELL order_on_defs[of _ r] by auto

lemma (in wo_rel) PARORD: "Partial_order r"
using WELL order_on_defs[of _ r] by auto

lemma (in wo_rel) cases_Total2:
"\<And> phi a b. \<lbrakk>{a,b} \<le> Field r; ((a,b) \<in> r - Id \<Longrightarrow> phi a b);
              ((b,a) \<in> r - Id \<Longrightarrow> phi a b); (a = b \<Longrightarrow> phi a b)\<rbrakk>
             \<Longrightarrow> phi a b"
using TOTALS by auto


subsection {* Well-founded induction and recursion adapted to non-strict well-order relations  *}

lemma (in wo_rel) worec_unique_fixpoint:
assumes ADM: "adm_wo H" and fp: "f = H f"
shows "f = worec H"
proof-
  have "adm_wf (r - Id) H"
  unfolding adm_wf_def
  using ADM adm_wo_def[of H] underS_def by auto
  hence "f = wfrec (r - Id) H"
  using fp WF wfrec_unique_fixpoint[of "r - Id" H] by simp
  thus ?thesis unfolding worec_def .
qed


subsubsection {* Properties of max2 *}

lemma (in wo_rel) max2_iff:
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


subsubsection{* Properties of minim *}

lemma (in wo_rel) minim_Under:
"\<lbrakk>B \<le> Field r; B \<noteq> {}\<rbrakk> \<Longrightarrow> minim B \<in> Under B"
by(auto simp add: Under_def
minim_in
minim_inField
minim_least
under_ofilter
underS_ofilter
Field_ofilter
ofilter_Under
ofilter_UnderS
ofilter_Un
)

lemma (in wo_rel) equals_minim_Under:
"\<lbrakk>B \<le> Field r; a \<in> B; a \<in> Under B\<rbrakk>
 \<Longrightarrow> a = minim B"
by(auto simp add: Under_def equals_minim)

lemma (in wo_rel) minim_iff_In_Under:
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

lemma (in wo_rel) minim_Under_under:
assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
shows "Under A = under (minim A)"
proof-
  (* Preliminary facts *)
  have 1: "minim A \<in> A"
  using assms minim_in by auto
  have 2: "\<forall>x \<in> A. (minim A, x) \<in> r"
  using assms minim_least by auto
  (* Main proof *)
  have "Under A \<le> under (minim A)"
  proof
    fix x assume "x \<in> Under A"
    with 1 Under_def have "(x,minim A) \<in> r" by auto
    thus "x \<in> under(minim A)" unfolding under_def by simp
  qed
  (*  *)
  moreover
  (*  *)
  have "under (minim A) \<le> Under A"
  proof
    fix x assume "x \<in> under(minim A)"
    hence 11: "(x,minim A) \<in> r" unfolding under_def by simp
    hence "x \<in> Field r" unfolding Field_def by auto
    moreover
    {fix a assume "a \<in> A"
     with 2 have "(minim A, a) \<in> r" by simp
     with 11 have "(x,a) \<in> r"
     using TRANS trans_def[of r] by blast
    }
    ultimately show "x \<in> Under A" by (unfold Under_def, auto)
  qed
  (*  *)
  ultimately show ?thesis by blast
qed

lemma (in wo_rel) minim_UnderS_underS:
assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
shows "UnderS A = underS (minim A)"
proof-
  (* Preliminary facts *)
  have 1: "minim A \<in> A"
  using assms minim_in by auto
  have 2: "\<forall>x \<in> A. (minim A, x) \<in> r"
  using assms minim_least by auto
  (* Main proof *)
  have "UnderS A \<le> underS (minim A)"
  proof
    fix x assume "x \<in> UnderS A"
    with 1 UnderS_def have "x \<noteq> minim A \<and> (x,minim A) \<in> r" by auto
    thus "x \<in> underS(minim A)" unfolding underS_def by simp
  qed
  (*  *)
  moreover
  (*  *)
  have "underS (minim A) \<le> UnderS A"
  proof
    fix x assume "x \<in> underS(minim A)"
    hence 11: "x \<noteq> minim A \<and> (x,minim A) \<in> r" unfolding underS_def by simp
    hence "x \<in> Field r" unfolding Field_def by auto
    moreover
    {fix a assume "a \<in> A"
     with 2 have 3: "(minim A, a) \<in> r" by simp
     with 11 have "(x,a) \<in> r"
     using TRANS trans_def[of r] by blast
     moreover
     have "x \<noteq> a"
     proof
       assume "x = a"
       with 11 3 ANTISYM antisym_def[of r]
       show False by auto
     qed
     ultimately
     have "x \<noteq> a \<and> (x,a) \<in> r" by simp
    }
    ultimately show "x \<in> UnderS A" by (unfold UnderS_def, auto)
  qed
  (*  *)
  ultimately show ?thesis by blast
qed


subsubsection{* Properties of supr *}

lemma (in wo_rel) supr_Above:
assumes SUB: "B \<le> Field r" and ABOVE: "Above B \<noteq> {}"
shows "supr B \<in> Above B"
proof(unfold supr_def)
  have "Above B \<le> Field r"
  using Above_Field by auto
  thus "minim (Above B) \<in> Above B"
  using assms by (simp add: minim_in)
qed

lemma (in wo_rel) supr_greater:
assumes SUB: "B \<le> Field r" and ABOVE: "Above B \<noteq> {}" and
        IN: "b \<in> B"
shows "(b, supr B) \<in> r"
proof-
  from assms supr_Above
  have "supr B \<in> Above B" by simp
  with IN Above_def show ?thesis by simp
qed

lemma (in wo_rel) supr_least_Above:
assumes SUB: "B \<le> Field r" and
        ABOVE: "a \<in> Above B"
shows "(supr B, a) \<in> r"
proof(unfold supr_def)
  have "Above B \<le> Field r"
  using Above_Field by auto
  thus "(minim (Above B), a) \<in> r"
  using assms minim_least
  by simp
qed

lemma (in wo_rel) supr_least:
"\<lbrakk>B \<le> Field r; a \<in> Field r; (\<And> b. b \<in> B \<Longrightarrow> (b,a) \<in> r)\<rbrakk>
 \<Longrightarrow> (supr B, a) \<in> r"
by(auto simp add: supr_least_Above Above_def)

lemma (in wo_rel) equals_supr_Above:
assumes SUB: "B \<le> Field r" and ABV: "a \<in> Above B" and
        MINIM: "\<And> a'. a' \<in> Above B \<Longrightarrow> (a,a') \<in> r"
shows "a = supr B"
proof(unfold supr_def)
  have "Above B \<le> Field r"
  using Above_Field by auto
  thus "a = minim (Above B)"
  using assms equals_minim by simp
qed

lemma (in wo_rel) equals_supr:
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

lemma (in wo_rel) supr_inField:
assumes "B \<le> Field r" and  "Above B \<noteq> {}"
shows "supr B \<in> Field r"
proof-
  have "supr B \<in> Above B" using supr_Above assms by simp
  thus ?thesis using assms Above_Field by auto
qed

lemma (in wo_rel) supr_above_Above:
assumes SUB: "B \<le> Field r" and  ABOVE: "Above B \<noteq> {}"
shows "Above B = above (supr B)"
proof(unfold Above_def above_def, auto)
  fix a assume "a \<in> Field r" "\<forall>b \<in> B. (b,a) \<in> r"
  with supr_least assms
  show "(supr B, a) \<in> r" by auto
next
  fix b assume "(supr B, b) \<in> r"
  thus "b \<in> Field r"
  using REFL refl_on_def[of _ r] by auto
next
  fix a b
  assume 1: "(supr B, b) \<in> r" and 2: "a \<in> B"
  with assms supr_greater
  have "(a,supr B) \<in> r" by auto
  thus "(a,b) \<in> r"
  using 1 TRANS trans_def[of r] by blast
qed

lemma (in wo_rel) supr_under:
assumes IN: "a \<in> Field r"
shows "a = supr (under a)"
proof-
  have "under a \<le> Field r"
  using under_Field by auto
  moreover
  have "under a \<noteq> {}"
  using IN Refl_under_in REFL by auto
  moreover
  have "a \<in> Above (under a)"
  using in_Above_under IN by auto
  moreover
  have "\<forall>a' \<in> Above (under a). (a,a') \<in> r"
  proof(unfold Above_def under_def, auto)
    fix a'
    assume "\<forall>aa. (aa, a) \<in> r \<longrightarrow> (aa, a') \<in> r"
    hence "(a,a) \<in> r \<longrightarrow> (a,a') \<in> r" by blast
    moreover have "(a,a) \<in> r"
    using REFL IN by (auto simp add: refl_on_def)
    ultimately
    show  "(a, a') \<in> r" by (rule mp)
  qed
  ultimately show ?thesis
  using equals_supr_Above by auto
qed


subsubsection{* Properties of successor *}

lemma (in wo_rel) suc_least:
"\<lbrakk>B \<le> Field r; a \<in> Field r; (\<And> b. b \<in> B \<Longrightarrow> a \<noteq> b \<and> (b,a) \<in> r)\<rbrakk>
 \<Longrightarrow> (suc B, a) \<in> r"
by(auto simp add: suc_least_AboveS AboveS_def)

lemma (in wo_rel) equals_suc:
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

lemma (in wo_rel) suc_above_AboveS:
assumes SUB: "B \<le> Field r" and
        ABOVE: "AboveS B \<noteq> {}"
shows "AboveS B = above (suc B)"
proof(unfold AboveS_def above_def, auto)
  fix a assume "a \<in> Field r" "\<forall>b \<in> B. a \<noteq> b \<and> (b,a) \<in> r"
  with suc_least assms
  show "(suc B,a) \<in> r" by auto
next
  fix b assume "(suc B, b) \<in> r"
  thus "b \<in> Field r"
  using REFL refl_on_def[of _ r] by auto
next
  fix a b
  assume 1: "(suc B, b) \<in> r" and 2: "a \<in> B"
  with assms suc_greater[of B a]
  have "(a,suc B) \<in> r" by auto
  thus "(a,b) \<in> r"
  using 1 TRANS trans_def[of r] by blast
next
  fix a
  assume 1: "(suc B, a) \<in> r" and 2: "a \<in> B"
  with assms suc_greater[of B a]
  have "(a,suc B) \<in> r" by auto
  moreover have "suc B \<in> Field r"
  using assms suc_inField by simp
  ultimately have "a = suc B"
  using 1 2 SUB ANTISYM antisym_def[of r] by auto
  thus False
  using assms suc_greater[of B a] 2 by auto
qed

lemma (in wo_rel) suc_singl_pred:
assumes IN: "a \<in> Field r" and ABOVE_NE: "aboveS a \<noteq> {}" and
        REL: "(a',suc {a}) \<in> r" and DIFF: "a' \<noteq> suc {a}"
shows "a' = a \<or> (a',a) \<in> r"
proof-
  have *: "suc {a} \<in> Field r \<and> a' \<in> Field r"
  using WELL REL well_order_on_domain by auto
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

lemma (in wo_rel) under_underS_suc:
assumes IN: "a \<in> Field r" and ABV: "aboveS a \<noteq> {}"
shows "underS (suc {a}) = under a"
proof-
  have 1: "AboveS {a} \<noteq> {}"
  using ABV aboveS_AboveS_singl by auto
  have 2: "a \<noteq> suc {a} \<and> (a,suc {a}) \<in> r"
  using suc_greater[of "{a}" a] IN 1 by auto
  (*   *)
  have "underS (suc {a}) \<le> under a"
  proof(unfold underS_def under_def, auto)
    fix x assume *: "x \<noteq> suc {a}" and **: "(x,suc {a}) \<in> r"
    with suc_singl_pred[of a x] IN ABV
    have "x = a \<or> (x,a) \<in> r" by auto
    with REFL refl_on_def[of _ r] IN
    show "(x,a) \<in> r" by auto
  qed
  (*  *)
  moreover
  (*   *)
  have "under a \<le> underS (suc {a})"
  proof(unfold underS_def under_def, auto)
    assume "(suc {a}, a) \<in> r"
    with 2 ANTISYM antisym_def[of r]
    show False by auto
  next
    fix x assume *: "(x,a) \<in> r"
    with 2 TRANS trans_def[of r]
    show "(x,suc {a}) \<in> r" by blast
  (*  blast is often better than auto/auto for transitivity-like properties *)
  qed
  (*  *)
  ultimately show ?thesis by blast
qed


subsubsection {* Properties of order filters  *}

lemma (in wo_rel) ofilter_INTER:
"\<lbrakk>I \<noteq> {}; \<And> i. i \<in> I \<Longrightarrow> ofilter(A i)\<rbrakk> \<Longrightarrow> ofilter (\<Inter> i \<in> I. A i)"
unfolding ofilter_def by blast

lemma (in wo_rel) ofilter_Inter:
"\<lbrakk>S \<noteq> {}; \<And> A. A \<in> S \<Longrightarrow> ofilter A\<rbrakk> \<Longrightarrow> ofilter (Inter S)"
unfolding ofilter_def by blast

lemma (in wo_rel) ofilter_Union:
"(\<And> A. A \<in> S \<Longrightarrow> ofilter A) \<Longrightarrow> ofilter (Union S)"
unfolding ofilter_def by blast

lemma (in wo_rel) ofilter_under_Union:
"ofilter A \<Longrightarrow> A = Union {under a| a. a \<in> A}"
using ofilter_under_UNION[of A]
by(unfold Union_eq, auto)


subsubsection{* Other properties *}

lemma (in wo_rel) Trans_Under_regressive:
assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
shows "Under(Under A) \<le> Under A"
proof
  let ?a = "minim A"
  (*  Preliminary facts *)
  have 1: "minim A \<in> Under A"
  using assms minim_Under by auto
  have 2: "\<forall>y \<in> A. (minim A, y) \<in> r"
  using assms minim_least by auto
  (* Main proof *)
  fix x assume "x \<in> Under(Under A)"
  with 1 have 1: "(x,minim A) \<in> r"
  using Under_def by auto
  with Field_def have "x \<in> Field r" by fastforce
  moreover
  {fix y assume *: "y \<in> A"
   hence "(x,y) \<in> r"
   using 1 2 TRANS trans_def[of r] by blast
   with Field_def have "(x,y) \<in> r" by auto
  }
  ultimately
  show "x \<in> Under A" unfolding Under_def by auto
qed

lemma (in wo_rel) ofilter_suc_Field:
assumes OF: "ofilter A" and NE: "A \<noteq> Field r"
shows "ofilter (A \<union> {suc A})"
proof-
  (* Preliminary facts *)
  have 1: "A \<le> Field r" using OF ofilter_def by auto
  hence 2: "AboveS A \<noteq> {}"
  using ofilter_AboveS_Field NE OF by blast
  from 1 2 suc_inField
  have 3: "suc A \<in> Field r" by auto
  (* Main proof *)
  show ?thesis
  proof(unfold ofilter_def, auto simp add: 1 3)
    fix a x
    assume "a \<in> A" "x \<in> under a" "x \<notin> A"
    with OF ofilter_def have False by auto
    thus "x = suc A" by simp
  next
    fix x assume *: "x \<in> under (suc A)" and **: "x \<notin> A"
    hence "x \<in> Field r" using under_def Field_def by fastforce
    with ** have "x \<in> AboveS A"
    using ofilter_AboveS_Field[of A] OF by auto
    hence "(suc A,x) \<in> r"
    using suc_least_AboveS by auto
    moreover
    have "(x,suc A) \<in> r" using * under_def by auto
    ultimately show "x = suc A"
    using ANTISYM antisym_def[of r] by auto
  qed
qed

(* FIXME: needed? *)
declare (in wo_rel)
  minim_in[simp]
  minim_inField[simp]
  minim_least[simp]
  under_ofilter[simp]
  underS_ofilter[simp]
  Field_ofilter[simp]
  ofilter_Under[simp]
  ofilter_UnderS[simp]
  ofilter_Int[simp]
  ofilter_Un[simp]

abbreviation "worec \<equiv> wo_rel.worec"
abbreviation "adm_wo \<equiv> wo_rel.adm_wo"
abbreviation "isMinim \<equiv> wo_rel.isMinim"
abbreviation "minim \<equiv> wo_rel.minim"
abbreviation "max2 \<equiv> wo_rel.max2"
abbreviation "supr \<equiv> wo_rel.supr"
abbreviation "suc \<equiv> wo_rel.suc"
abbreviation "ofilter \<equiv> wo_rel.ofilter"

end
