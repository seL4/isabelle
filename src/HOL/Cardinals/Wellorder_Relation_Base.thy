(*  Title:      HOL/Cardinals/Wellorder_Relation_Base.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Well-order relations (base).
*)

header {* Well-Order Relations (Base) *}

theory Wellorder_Relation_Base
imports Wellfounded_More_Base
begin


text{* In this section, we develop basic concepts and results pertaining
to well-order relations.  Note that we consider well-order relations
as {\em non-strict relations},
i.e., as containing the diagonals of their fields. *}


locale wo_rel = rel + assumes WELL: "Well_order r"
begin

text{* The following context encompasses all this section. In other words,
for the whole section, we consider a fixed well-order relation @{term "r"}. *}

(* context wo_rel  *)


subsection {* Auxiliaries *}


lemma REFL: "Refl r"
using WELL order_on_defs[of _ r] by auto


lemma TRANS: "trans r"
using WELL order_on_defs[of _ r] by auto


lemma ANTISYM: "antisym r"
using WELL order_on_defs[of _ r] by auto


lemma TOTAL: "Total r"
using WELL order_on_defs[of _ r] by auto


lemma TOTALS: "\<forall>a \<in> Field r. \<forall>b \<in> Field r. (a,b) \<in> r \<or> (b,a) \<in> r"
using REFL TOTAL refl_on_def[of _ r] total_on_def[of _ r] by force


lemma LIN: "Linear_order r"
using WELL well_order_on_def[of _ r] by auto


lemma WF: "wf (r - Id)"
using WELL well_order_on_def[of _ r] by auto


lemma cases_Total:
"\<And> phi a b. \<lbrakk>{a,b} <= Field r; ((a,b) \<in> r \<Longrightarrow> phi a b); ((b,a) \<in> r \<Longrightarrow> phi a b)\<rbrakk>
             \<Longrightarrow> phi a b"
using TOTALS by auto


lemma cases_Total3:
"\<And> phi a b. \<lbrakk>{a,b} \<le> Field r; ((a,b) \<in> r - Id \<or> (b,a) \<in> r - Id \<Longrightarrow> phi a b);
              (a = b \<Longrightarrow> phi a b)\<rbrakk>  \<Longrightarrow> phi a b"
using TOTALS by auto


subsection {* Well-founded induction and recursion adapted to non-strict well-order relations  *}


text{* Here we provide induction and recursion principles specific to {\em non-strict}
well-order relations.
Although minor variations of those for well-founded relations, they will be useful
for doing away with the tediousness of
having to take out the diagonal each time in order to switch to a well-founded relation. *}


lemma well_order_induct:
assumes IND: "\<And>x. \<forall>y. y \<noteq> x \<and> (y, x) \<in> r \<longrightarrow> P y \<Longrightarrow> P x"
shows "P a"
proof-
  have "\<And>x. \<forall>y. (y, x) \<in> r - Id \<longrightarrow> P y \<Longrightarrow> P x"
  using IND by blast
  thus "P a" using WF wf_induct[of "r - Id" P a] by blast
qed


definition
worec :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where
"worec F \<equiv> wfrec (r - Id) F"


definition
adm_wo :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool"
where
"adm_wo H \<equiv> \<forall>f g x. (\<forall>y \<in> underS x. f y = g y) \<longrightarrow> H f x = H g x"


lemma worec_fixpoint:
assumes ADM: "adm_wo H"
shows "worec H = H (worec H)"
proof-
  let ?rS = "r - Id"
  have "adm_wf (r - Id) H"
  unfolding adm_wf_def
  using ADM adm_wo_def[of H] underS_def by auto
  hence "wfrec ?rS H = H (wfrec ?rS H)"
  using WF wfrec_fixpoint[of ?rS H] by simp
  thus ?thesis unfolding worec_def .
qed


subsection {* The notions of maximum, minimum, supremum, successor and order filter  *}


text{*
We define the successor {\em of a set}, and not of an element (the latter is of course
a particular case).  Also, we define the maximum {\em of two elements}, @{text "max2"},
and the minimum {\em of a set}, @{text "minim"} -- we chose these variants since we
consider them the most useful for well-orders.  The minimum is defined in terms of the
auxiliary relational operator @{text "isMinim"}.  Then, supremum and successor are
defined in terms of minimum as expected.
The minimum is only meaningful for non-empty sets, and the successor is only
meaningful for sets for which strict upper bounds exist.
Order filters for well-orders are also known as ``initial segments". *}


definition max2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where "max2 a b \<equiv> if (a,b) \<in> r then b else a"


definition isMinim :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
where "isMinim A b \<equiv> b \<in> A \<and> (\<forall>a \<in> A. (b,a) \<in> r)"

definition minim :: "'a set \<Rightarrow> 'a"
where "minim A \<equiv> THE b. isMinim A b"


definition supr :: "'a set \<Rightarrow> 'a"
where "supr A \<equiv> minim (Above A)"

definition suc :: "'a set \<Rightarrow> 'a"
where "suc A \<equiv> minim (AboveS A)"

definition ofilter :: "'a set \<Rightarrow> bool"
where
"ofilter A \<equiv> (A \<le> Field r) \<and> (\<forall>a \<in> A. under a \<le> A)"


subsubsection {* Properties of max2 *}


lemma max2_greater_among:
assumes "a \<in> Field r" and "b \<in> Field r"
shows "(a, max2 a b) \<in> r \<and> (b, max2 a b) \<in> r \<and> max2 a b \<in> {a,b}"
proof-
  {assume "(a,b) \<in> r"
   hence ?thesis using max2_def assms REFL refl_on_def
   by (auto simp add: refl_on_def)
  }
  moreover
  {assume "a = b"
   hence "(a,b) \<in> r" using REFL  assms
   by (auto simp add: refl_on_def)
  }
  moreover
  {assume *: "a \<noteq> b \<and> (b,a) \<in> r"
   hence "(a,b) \<notin> r" using ANTISYM
   by (auto simp add: antisym_def)
   hence ?thesis using * max2_def assms REFL refl_on_def
   by (auto simp add: refl_on_def)
  }
  ultimately show ?thesis using assms TOTAL
  total_on_def[of "Field r" r] by blast
qed


lemma max2_greater:
assumes "a \<in> Field r" and "b \<in> Field r"
shows "(a, max2 a b) \<in> r \<and> (b, max2 a b) \<in> r"
using assms by (auto simp add: max2_greater_among)


lemma max2_among:
assumes "a \<in> Field r" and "b \<in> Field r"
shows "max2 a b \<in> {a, b}"
using assms max2_greater_among[of a b] by simp


lemma max2_equals1:
assumes "a \<in> Field r" and "b \<in> Field r"
shows "(max2 a b = a) = ((b,a) \<in> r)"
using assms ANTISYM unfolding antisym_def using TOTALS
by(auto simp add: max2_def max2_among)


lemma max2_equals2:
assumes "a \<in> Field r" and "b \<in> Field r"
shows "(max2 a b = b) = ((a,b) \<in> r)"
using assms ANTISYM unfolding antisym_def using TOTALS
unfolding max2_def by auto


subsubsection {* Existence and uniqueness for isMinim and well-definedness of minim *}


lemma isMinim_unique:
assumes MINIM: "isMinim B a" and MINIM': "isMinim B a'"
shows "a = a'"
proof-
  {have "a \<in> B"
   using MINIM isMinim_def by simp
   hence "(a',a) \<in> r"
   using MINIM' isMinim_def by simp
  }
  moreover
  {have "a' \<in> B"
   using MINIM' isMinim_def by simp
   hence "(a,a') \<in> r"
   using MINIM isMinim_def by simp
  }
  ultimately
  show ?thesis using ANTISYM antisym_def[of r] by blast
qed


lemma Well_order_isMinim_exists:
assumes SUB: "B \<le> Field r" and NE: "B \<noteq> {}"
shows "\<exists>b. isMinim B b"
proof-
  from WF wf_eq_minimal[of "r - Id"] NE Id_def obtain b where
  *: "b \<in> B \<and> (\<forall>b'. b' \<noteq> b \<and> (b',b) \<in> r \<longrightarrow> b' \<notin> B)" by force
  show ?thesis
  proof(simp add: isMinim_def, rule exI[of _ b], auto)
    show "b \<in> B" using * by simp
  next
    fix b' assume As: "b' \<in> B"
    hence **: "b \<in> Field r \<and> b' \<in> Field r" using As SUB * by auto
    (*  *)
    from As  * have "b' = b \<or> (b',b) \<notin> r" by auto
    moreover
    {assume "b' = b"
     hence "(b,b') \<in> r"
     using ** REFL by (auto simp add: refl_on_def)
    }
    moreover
    {assume "b' \<noteq> b \<and> (b',b) \<notin> r"
     hence "(b,b') \<in> r"
     using ** TOTAL by (auto simp add: total_on_def)
    }
    ultimately show "(b,b') \<in> r" by blast
  qed
qed


lemma minim_isMinim:
assumes SUB: "B \<le> Field r" and NE: "B \<noteq> {}"
shows "isMinim B (minim B)"
proof-
  let ?phi = "(\<lambda> b. isMinim B b)"
  from assms Well_order_isMinim_exists
  obtain b where *: "?phi b" by blast
  moreover
  have "\<And> b'. ?phi b' \<Longrightarrow> b' = b"
  using isMinim_unique * by auto
  ultimately show ?thesis
  unfolding minim_def using theI[of ?phi b] by blast
qed


subsubsection{* Properties of minim *}


lemma minim_in:
assumes "B \<le> Field r" and "B \<noteq> {}"
shows "minim B \<in> B"
proof-
  from minim_isMinim[of B] assms
  have "isMinim B (minim B)" by simp
  thus ?thesis by (simp add: isMinim_def)
qed


lemma minim_inField:
assumes "B \<le> Field r" and "B \<noteq> {}"
shows "minim B \<in> Field r"
proof-
  have "minim B \<in> B" using assms by (simp add: minim_in)
  thus ?thesis using assms by blast
qed


lemma minim_least:
assumes  SUB: "B \<le> Field r" and IN: "b \<in> B"
shows "(minim B, b) \<in> r"
proof-
  from minim_isMinim[of B] assms
  have "isMinim B (minim B)" by auto
  thus ?thesis by (auto simp add: isMinim_def IN)
qed


lemma equals_minim:
assumes SUB: "B \<le> Field r" and IN: "a \<in> B" and
        LEAST: "\<And> b. b \<in> B \<Longrightarrow> (a,b) \<in> r"
shows "a = minim B"
proof-
  from minim_isMinim[of B] assms
  have "isMinim B (minim B)" by auto
  moreover have "isMinim B a" using IN LEAST isMinim_def by auto
  ultimately show ?thesis
  using isMinim_unique by auto
qed


subsubsection{* Properties of successor *}


lemma suc_AboveS:
assumes SUB: "B \<le> Field r" and ABOVES: "AboveS B \<noteq> {}"
shows "suc B \<in> AboveS B"
proof(unfold suc_def)
  have "AboveS B \<le> Field r"
  using AboveS_Field by auto
  thus "minim (AboveS B) \<in> AboveS B"
  using assms by (simp add: minim_in)
qed


lemma suc_greater:
assumes SUB: "B \<le> Field r" and ABOVES: "AboveS B \<noteq> {}" and
        IN: "b \<in> B"
shows "suc B \<noteq> b \<and> (b,suc B) \<in> r"
proof-
  from assms suc_AboveS
  have "suc B \<in> AboveS B" by simp
  with IN AboveS_def show ?thesis by simp
qed


lemma suc_least_AboveS:
assumes ABOVES: "a \<in> AboveS B"
shows "(suc B,a) \<in> r"
proof(unfold suc_def)
  have "AboveS B \<le> Field r"
  using AboveS_Field by auto
  thus "(minim (AboveS B),a) \<in> r"
  using assms minim_least by simp
qed


lemma suc_inField:
assumes "B \<le> Field r" and "AboveS B \<noteq> {}"
shows "suc B \<in> Field r"
proof-
  have "suc B \<in> AboveS B" using suc_AboveS assms by simp
  thus ?thesis
  using assms AboveS_Field by auto
qed


lemma equals_suc_AboveS:
assumes SUB: "B \<le> Field r" and ABV: "a \<in> AboveS B" and
        MINIM: "\<And> a'. a' \<in> AboveS B \<Longrightarrow> (a,a') \<in> r"
shows "a = suc B"
proof(unfold suc_def)
  have "AboveS B \<le> Field r"
  using AboveS_Field[of B] by auto
  thus "a = minim (AboveS B)"
  using assms equals_minim
  by simp
qed


lemma suc_underS:
assumes IN: "a \<in> Field r"
shows "a = suc (underS a)"
proof-
  have "underS a \<le> Field r"
  using underS_Field by auto
  moreover
  have "a \<in> AboveS (underS a)"
  using in_AboveS_underS IN by auto
  moreover
  have "\<forall>a' \<in> AboveS (underS a). (a,a') \<in> r"
  proof(clarify)
    fix a'
    assume *: "a' \<in> AboveS (underS a)"
    hence **: "a' \<in> Field r"
    using AboveS_Field by auto
    {assume "(a,a') \<notin> r"
     hence "a' = a \<or> (a',a) \<in> r"
     using TOTAL IN ** by (auto simp add: total_on_def)
     moreover
     {assume "a' = a"
      hence "(a,a') \<in> r"
      using REFL IN ** by (auto simp add: refl_on_def)
     }
     moreover
     {assume "a' \<noteq> a \<and> (a',a) \<in> r"
      hence "a' \<in> underS a"
      unfolding underS_def by simp
      hence "a' \<notin> AboveS (underS a)"
      using AboveS_disjoint by blast
      with * have False by simp
     }
     ultimately have "(a,a') \<in> r" by blast
    }
    thus  "(a, a') \<in> r" by blast
  qed
  ultimately show ?thesis
  using equals_suc_AboveS by auto
qed


subsubsection {* Properties of order filters  *}


lemma under_ofilter:
"ofilter (under a)"
proof(unfold ofilter_def under_def, auto simp add: Field_def)
  fix aa x
  assume "(aa,a) \<in> r" "(x,aa) \<in> r"
  thus "(x,a) \<in> r"
  using TRANS trans_def[of r] by blast
qed


lemma underS_ofilter:
"ofilter (underS a)"
proof(unfold ofilter_def underS_def under_def, auto simp add: Field_def)
  fix aa assume "(a, aa) \<in> r" "(aa, a) \<in> r" and DIFF: "aa \<noteq> a"
  thus False
  using ANTISYM antisym_def[of r] by blast
next
  fix aa x
  assume "(aa,a) \<in> r" "aa \<noteq> a" "(x,aa) \<in> r"
  thus "(x,a) \<in> r"
  using TRANS trans_def[of r] by blast
qed


lemma Field_ofilter:
"ofilter (Field r)"
by(unfold ofilter_def under_def, auto simp add: Field_def)


lemma ofilter_underS_Field:
"ofilter A = ((\<exists>a \<in> Field r. A = underS a) \<or> (A = Field r))"
proof
  assume "(\<exists>a\<in>Field r. A = underS a) \<or> A = Field r"
  thus "ofilter A"
  by (auto simp: underS_ofilter Field_ofilter)
next
  assume *: "ofilter A"
  let ?One = "(\<exists>a\<in>Field r. A = underS a)"
  let ?Two = "(A = Field r)"
  show "?One \<or> ?Two"
  proof(cases ?Two, simp)
    let ?B = "(Field r) - A"
    let ?a = "minim ?B"
    assume "A \<noteq> Field r"
    moreover have "A \<le> Field r" using * ofilter_def by simp
    ultimately have 1: "?B \<noteq> {}" by blast
    hence 2: "?a \<in> Field r" using minim_inField[of ?B] by blast
    have 3: "?a \<in> ?B" using minim_in[of ?B] 1 by blast
    hence 4: "?a \<notin> A" by blast
    have 5: "A \<le> Field r" using * ofilter_def[of A] by auto
    (*  *)
    moreover
    have "A = underS ?a"
    proof
      show "A \<le> underS ?a"
      proof(unfold underS_def, auto simp add: 4)
        fix x assume **: "x \<in> A"
        hence 11: "x \<in> Field r" using 5 by auto
        have 12: "x \<noteq> ?a" using 4 ** by auto
        have 13: "under x \<le> A" using * ofilter_def ** by auto
        {assume "(x,?a) \<notin> r"
         hence "(?a,x) \<in> r"
         using TOTAL total_on_def[of "Field r" r]
               2 4 11 12 by auto
         hence "?a \<in> under x" using under_def by auto
         hence "?a \<in> A" using ** 13 by blast
         with 4 have False by simp
        }
        thus "(x,?a) \<in> r" by blast
      qed
    next
      show "underS ?a \<le> A"
      proof(unfold underS_def, auto)
        fix x
        assume **: "x \<noteq> ?a" and ***: "(x,?a) \<in> r"
        hence 11: "x \<in> Field r" using Field_def by fastforce
         {assume "x \<notin> A"
          hence "x \<in> ?B" using 11 by auto
          hence "(?a,x) \<in> r" using 3 minim_least[of ?B x] by blast
          hence False
          using ANTISYM antisym_def[of r] ** *** by auto
         }
        thus "x \<in> A" by blast
      qed
    qed
    ultimately have ?One using 2 by blast
    thus ?thesis by simp
  qed
qed


lemma ofilter_Under:
assumes "A \<le> Field r"
shows "ofilter(Under A)"
proof(unfold ofilter_def, auto)
  fix x assume "x \<in> Under A"
  thus "x \<in> Field r"
  using Under_Field assms by auto
next
  fix a x
  assume "a \<in> Under A" and "x \<in> under a"
  thus "x \<in> Under A"
  using TRANS under_Under_trans by auto
qed


lemma ofilter_UnderS:
assumes "A \<le> Field r"
shows "ofilter(UnderS A)"
proof(unfold ofilter_def, auto)
  fix x assume "x \<in> UnderS A"
  thus "x \<in> Field r"
  using UnderS_Field assms by auto
next
  fix a x
  assume "a \<in> UnderS A" and "x \<in> under a"
  thus "x \<in> UnderS A"
  using TRANS ANTISYM under_UnderS_trans by auto
qed


lemma ofilter_Int: "\<lbrakk>ofilter A; ofilter B\<rbrakk> \<Longrightarrow> ofilter(A Int B)"
unfolding ofilter_def by blast


lemma ofilter_Un: "\<lbrakk>ofilter A; ofilter B\<rbrakk> \<Longrightarrow> ofilter(A \<union> B)"
unfolding ofilter_def by blast


lemma ofilter_UNION:
"(\<And> i. i \<in> I \<Longrightarrow> ofilter(A i)) \<Longrightarrow> ofilter (\<Union> i \<in> I. A i)"
unfolding ofilter_def by blast


lemma ofilter_under_UNION:
assumes "ofilter A"
shows "A = (\<Union> a \<in> A. under a)"
proof
  have "\<forall>a \<in> A. under a \<le> A"
  using assms ofilter_def by auto
  thus "(\<Union> a \<in> A. under a) \<le> A" by blast
next
  have "\<forall>a \<in> A. a \<in> under a"
  using REFL Refl_under_in assms ofilter_def by blast
  thus "A \<le> (\<Union> a \<in> A. under a)" by blast
qed


subsubsection{* Other properties *}


lemma ofilter_linord:
assumes OF1: "ofilter A" and OF2: "ofilter B"
shows "A \<le> B \<or> B \<le> A"
proof(cases "A = Field r")
  assume Case1: "A = Field r"
  hence "B \<le> A" using OF2 ofilter_def by auto
  thus ?thesis by simp
next
  assume Case2: "A \<noteq> Field r"
  with ofilter_underS_Field OF1 obtain a where
  1: "a \<in> Field r \<and> A = underS a" by auto
  show ?thesis
  proof(cases "B = Field r")
    assume Case21: "B = Field r"
    hence "A \<le> B" using OF1 ofilter_def by auto
    thus ?thesis by simp
  next
    assume Case22: "B \<noteq> Field r"
    with ofilter_underS_Field OF2 obtain b where
    2: "b \<in> Field r \<and> B = underS b" by auto
    have "a = b \<or> (a,b) \<in> r \<or> (b,a) \<in> r"
    using 1 2 TOTAL total_on_def[of _ r] by auto
    moreover
    {assume "a = b" with 1 2 have ?thesis by auto
    }
    moreover
    {assume "(a,b) \<in> r"
     with underS_incr TRANS ANTISYM 1 2
     have "A \<le> B" by auto
     hence ?thesis by auto
    }
    moreover
     {assume "(b,a) \<in> r"
     with underS_incr TRANS ANTISYM 1 2
     have "B \<le> A" by auto
     hence ?thesis by auto
    }
    ultimately show ?thesis by blast
  qed
qed


lemma ofilter_AboveS_Field:
assumes "ofilter A"
shows "A \<union> (AboveS A) = Field r"
proof
  show "A \<union> (AboveS A) \<le> Field r"
  using assms ofilter_def AboveS_Field by auto
next
  {fix x assume *: "x \<in> Field r" and **: "x \<notin> A"
   {fix y assume ***: "y \<in> A"
    with ** have 1: "y \<noteq> x" by auto
    {assume "(y,x) \<notin> r"
     moreover
     have "y \<in> Field r" using assms ofilter_def *** by auto
     ultimately have "(x,y) \<in> r"
     using 1 * TOTAL total_on_def[of _ r] by auto
     with *** assms ofilter_def under_def have "x \<in> A" by auto
     with ** have False by contradiction
    }
    hence "(y,x) \<in> r" by blast
    with 1 have "y \<noteq> x \<and> (y,x) \<in> r" by auto
   }
   with * have "x \<in> AboveS A" unfolding AboveS_def by auto
  }
  thus "Field r \<le> A \<union> (AboveS A)" by blast
qed


lemma suc_ofilter_in:
assumes OF: "ofilter A" and ABOVE_NE: "AboveS A \<noteq> {}" and
        REL: "(b,suc A) \<in> r" and DIFF: "b \<noteq> suc A"
shows "b \<in> A"
proof-
  have *: "suc A \<in> Field r \<and> b \<in> Field r"
  using WELL REL well_order_on_domain by auto
  {assume **: "b \<notin> A"
   hence "b \<in> AboveS A"
   using OF * ofilter_AboveS_Field by auto
   hence "(suc A, b) \<in> r"
   using suc_least_AboveS by auto
   hence False using REL DIFF ANTISYM *
   by (auto simp add: antisym_def)
  }
  thus ?thesis by blast
qed



end (* context wo_rel *)



end
