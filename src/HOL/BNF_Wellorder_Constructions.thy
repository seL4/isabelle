(*  Title:      HOL/BNF_Wellorder_Constructions.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Constructions on wellorders as needed by bounded natural functors.
*)

section \<open>Constructions on Wellorders as Needed by Bounded Natural Functors\<close>

theory BNF_Wellorder_Constructions
  imports BNF_Wellorder_Embedding
begin

text \<open>In this section, we study basic constructions on well-orders, such as restriction to
a set/order filter, copy via direct images, ordinal-like sum of disjoint well-orders,
and bounded square.  We also define between well-orders
the relations \<open>ordLeq\<close>, of being embedded (abbreviated \<open>\<le>o\<close>),
\<open>ordLess\<close>, of being strictly embedded (abbreviated \<open><o\<close>), and
\<open>ordIso\<close>, of being isomorphic (abbreviated \<open>=o\<close>).  We study the
connections between these relations, order filters, and the aforementioned constructions.
A main result of this section is that \<open><o\<close> is well-founded.\<close>


subsection \<open>Restriction to a set\<close>

abbreviation Restr :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel"
  where "Restr r A \<equiv> r Int (A \<times> A)"

lemma Restr_subset:
  "A \<le> B \<Longrightarrow> Restr (Restr r B) A = Restr r A"
  by blast

lemma Restr_Field: "Restr r (Field r) = r"
  unfolding Field_def by auto

lemma Refl_Restr: "Refl r \<Longrightarrow> Refl(Restr r A)"
  unfolding refl_on_def Field_def by auto

lemma linear_order_on_Restr:
  "linear_order_on A r \<Longrightarrow> linear_order_on (A \<inter> above r x) (Restr r (above r x))"
  by(simp add: order_on_defs refl_on_def trans_def antisym_def total_on_def)(safe; blast)

lemma antisym_Restr:
  "antisym r \<Longrightarrow> antisym(Restr r A)"
  unfolding antisym_def Field_def by auto

lemma Total_Restr:
  "Total r \<Longrightarrow> Total(Restr r A)"
  unfolding total_on_def Field_def by auto

lemma total_on_imp_Total_Restr: "total_on A r \<Longrightarrow> Total (Restr r A)"
  by (auto simp: Field_def total_on_def)

lemma trans_Restr:
  "trans r \<Longrightarrow> trans(Restr r A)"
  unfolding trans_def Field_def by blast

lemma Preorder_Restr:
  assumes "Preorder r"
  shows "Preorder(Restr r A)"
  unfolding preorder_on_def
proof (intro conjI)
  have "r \<subseteq> Field r \<times> Field r" and "Refl r" and "trans r"
    using \<open>Preorder r\<close>
    by (simp_all only: preorder_on_def)

  show "Restr r A \<subseteq> Field (Restr r A) \<times> Field (Restr r A)"
    using \<open>r \<subseteq> Field r \<times> Field r\<close>
    by (auto simp add: Field_def)

  show "Refl (Restr r A)"
    using Refl_Restr[OF \<open>Refl r\<close>] .

  show "trans (Restr r A)"
    using trans_Restr[OF \<open>trans r\<close>] .
qed

lemma Partial_order_Restr:
  "Partial_order r \<Longrightarrow> Partial_order(Restr r A)"
  unfolding partial_order_on_def by (simp add: Preorder_Restr antisym_Restr)

lemma Linear_order_Restr:
  "Linear_order r \<Longrightarrow> Linear_order(Restr r A)"
  unfolding linear_order_on_def by (simp add: Partial_order_Restr Total_Restr)

lemma Well_order_Restr:
  assumes "Well_order r"
  shows "Well_order(Restr r A)"
  using assms  
  by (auto simp: well_order_on_def Linear_order_Restr elim: wf_subset)

lemma Field_Restr_subset: "Field(Restr r A) \<le> A"
  by (auto simp add: Field_def)

lemma Refl_Field_Restr:
  "Refl r \<Longrightarrow> Field(Restr r A) = (Field r) Int A"
  unfolding refl_on_def Field_def by blast

lemma Refl_Field_Restr2:
  "\<lbrakk>Refl r; A \<le> Field r\<rbrakk> \<Longrightarrow> Field(Restr r A) = A"
  by (auto simp add: Refl_Field_Restr)

lemma well_order_on_Restr:
  assumes WELL: "Well_order r" and SUB: "A \<le> Field r"
  shows "well_order_on A (Restr r A)"
  using assms 
  using Well_order_Restr[of r A] Refl_Field_Restr2[of r A]
    order_on_defs[of "Field r" r] by auto


subsection \<open>Order filters versus restrictions and embeddings\<close>

lemma Field_Restr_ofilter:
  "\<lbrakk>Well_order r; wo_rel.ofilter r A\<rbrakk> \<Longrightarrow> Field(Restr r A) = A"
  by (auto simp add: wo_rel_def wo_rel.ofilter_def wo_rel.REFL Refl_Field_Restr2)

lemma ofilter_Restr_under:
  assumes WELL: "Well_order r" and OF: "wo_rel.ofilter r A" and IN: "a \<in> A"
  shows "under (Restr r A) a = under r a"
  unfolding wo_rel.ofilter_def under_def
proof
  show "{b. (b, a) \<in> Restr r A} \<subseteq> {b. (b, a) \<in> r}"
    by auto
next
  have "under r a \<subseteq> A"
  proof
    fix x
    assume *: "x \<in> under r a"
    then have "a \<in> Field r"
      unfolding under_def using Field_def by fastforce
    then show "x \<in> A" using IN assms *
      by (auto simp add: wo_rel_def wo_rel.ofilter_def)
  qed
  then show "{b. (b, a) \<in> r} \<subseteq> {b. (b, a) \<in> Restr r A}"
    unfolding under_def using assms by auto
qed

lemma ofilter_embed:
  assumes "Well_order r"
  shows "wo_rel.ofilter r A = (A \<le> Field r \<and> embed (Restr r A) r id)"
proof
  assume *: "wo_rel.ofilter r A"
  show "A \<le> Field r \<and> embed (Restr r A) r id"
    unfolding embed_def
  proof safe
    fix a assume "a \<in> A" thus "a \<in> Field r" using assms *
      by (auto simp add: wo_rel_def wo_rel.ofilter_def)
  next
    fix a assume "a \<in> Field (Restr r A)"
    thus "bij_betw id (under (Restr r A) a) (under r (id a))" using assms *
      by (simp add: ofilter_Restr_under Field_Restr_ofilter)
  qed
next
  assume *: "A \<le> Field r \<and> embed (Restr r A) r id"
  hence "Field(Restr r A) \<le> Field r"
    using assms  embed_Field[of "Restr r A" r id] id_def
      Well_order_Restr[of r] by auto
  {fix a assume "a \<in> A"
    hence "a \<in> Field(Restr r A)" using * assms
      by (simp add: order_on_defs Refl_Field_Restr2)
    hence "bij_betw id (under (Restr r A) a) (under r a)"
      using * unfolding embed_def by auto
    hence "under r a \<le> under (Restr r A) a"
      unfolding bij_betw_def by auto
    also have "\<dots> \<le> Field(Restr r A)" by (simp add: under_Field)
    also have "\<dots> \<le> A" by (simp add: Field_Restr_subset)
    finally have "under r a \<le> A" .
  }
  thus "wo_rel.ofilter r A" using assms * by (simp add: wo_rel_def wo_rel.ofilter_def)
qed

lemma ofilter_Restr_Int:
  assumes WELL: "Well_order r" and OFA: "wo_rel.ofilter r A"
  shows "wo_rel.ofilter (Restr r B) (A Int B)"
proof-
  let ?rB = "Restr r B"
  have Well: "wo_rel r" unfolding wo_rel_def using WELL .
  hence Refl: "Refl r" by (simp add: wo_rel.REFL)
  hence Field: "Field ?rB = Field r Int B"
    using Refl_Field_Restr by blast
  have WellB: "wo_rel ?rB \<and> Well_order ?rB" using WELL
    by (simp add: Well_order_Restr wo_rel_def)
      (* Main proof *)
  show ?thesis using WellB assms
    unfolding wo_rel.ofilter_def under_def ofilter_def
  proof safe
    fix a assume "a \<in> A" and *: "a \<in> B"
    hence "a \<in> Field r" using OFA Well by (auto simp add: wo_rel.ofilter_def)
    with * show "a \<in> Field ?rB" using Field by auto
  next
    fix a b assume "a \<in> A" and "(b,a) \<in> r"
    thus "b \<in> A" using Well OFA by (auto simp add: wo_rel.ofilter_def under_def)
  qed
qed

lemma ofilter_Restr_subset:
  assumes WELL: "Well_order r" and OFA: "wo_rel.ofilter r A" and SUB: "A \<le> B"
  shows "wo_rel.ofilter (Restr r B) A"
proof-
  have "A Int B = A" using SUB by blast
  thus ?thesis using assms ofilter_Restr_Int[of r A B] by auto
qed

lemma ofilter_subset_embed:
  assumes WELL: "Well_order r" and
    OFA: "wo_rel.ofilter r A" and OFB: "wo_rel.ofilter r B"
  shows "(A \<le> B) = (embed (Restr r A) (Restr r B) id)"
proof-
  let ?rA = "Restr r A"  let ?rB = "Restr r B"
  have Well: "wo_rel r" unfolding wo_rel_def using WELL .
  hence Refl: "Refl r" by (simp add: wo_rel.REFL)
  hence FieldA: "Field ?rA = Field r Int A"
    using Refl_Field_Restr by blast
  have FieldB: "Field ?rB = Field r Int B"
    using Refl Refl_Field_Restr by blast
  have WellA: "wo_rel ?rA \<and> Well_order ?rA" using WELL
    by (simp add: Well_order_Restr wo_rel_def)
  have WellB: "wo_rel ?rB \<and> Well_order ?rB" using WELL
    by (simp add: Well_order_Restr wo_rel_def)
      (* Main proof *)
  show ?thesis
  proof
    assume *: "A \<le> B"
    hence "wo_rel.ofilter (Restr r B) A" using assms
      by (simp add: ofilter_Restr_subset)
    hence "embed (Restr ?rB A) (Restr r B) id"
      using WellB ofilter_embed[of "?rB" A] by auto
    thus "embed (Restr r A) (Restr r B) id"
      using * by (simp add: Restr_subset)
  next
    assume *: "embed (Restr r A) (Restr r B) id"
    {fix a assume **: "a \<in> A"
      hence "a \<in> Field r" using Well OFA by (auto simp add: wo_rel.ofilter_def)
      with ** FieldA have "a \<in> Field ?rA" by auto
      hence "a \<in> Field ?rB" using * WellA embed_Field[of ?rA ?rB id] by auto
      hence "a \<in> B" using FieldB by auto
    }
    thus "A \<le> B" by blast
  qed
qed

lemma ofilter_subset_embedS_iso:
  assumes WELL: "Well_order r" and
    OFA: "wo_rel.ofilter r A" and OFB: "wo_rel.ofilter r B"
  shows "((A < B) = (embedS (Restr r A) (Restr r B) id)) \<and>
       ((A = B) = (iso (Restr r A) (Restr r B) id))"
proof-
  let ?rA = "Restr r A"  let ?rB = "Restr r B"
  have Well: "wo_rel r" unfolding wo_rel_def using WELL .
  hence Refl: "Refl r" by (simp add: wo_rel.REFL)
  hence "Field ?rA = Field r Int A"
    using Refl_Field_Restr by blast
  hence FieldA: "Field ?rA = A" using OFA Well
    by (auto simp add: wo_rel.ofilter_def)
  have "Field ?rB = Field r Int B"
    using Refl Refl_Field_Restr by blast
  hence FieldB: "Field ?rB = B" using OFB Well
    by (auto simp add: wo_rel.ofilter_def)
      (* Main proof *)
  show ?thesis unfolding embedS_def iso_def
    using assms ofilter_subset_embed[of r A B]
      FieldA FieldB bij_betw_id_iff[of A B] by auto
qed

lemma ofilter_subset_embedS:
  assumes WELL: "Well_order r" and
    OFA: "wo_rel.ofilter r A" and OFB: "wo_rel.ofilter r B"
  shows "(A < B) = embedS (Restr r A) (Restr r B) id"
  using assms by (simp add: ofilter_subset_embedS_iso)

lemma embed_implies_iso_Restr:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMB: "embed r' r f"
  shows "iso r' (Restr r (f ` (Field r'))) f"
proof-
  let ?A' = "Field r'"
  let ?r'' = "Restr r (f ` ?A')"
  have 0: "Well_order ?r''" using WELL Well_order_Restr by blast
  have 1: "wo_rel.ofilter r (f ` ?A')" using assms embed_Field_ofilter  by blast
  hence "Field ?r'' = f ` (Field r')" using WELL Field_Restr_ofilter by blast
  hence "bij_betw f ?A' (Field ?r'')"
    using EMB embed_inj_on WELL' unfolding bij_betw_def by blast
  moreover
  {have "\<forall>a b. (a,b) \<in> r' \<longrightarrow> a \<in> Field r' \<and> b \<in> Field r'"
      unfolding Field_def by auto
    hence "compat r' ?r'' f"
      using assms embed_iff_compat_inj_on_ofilter
      unfolding compat_def by blast
  }
  ultimately show ?thesis using WELL' 0 iso_iff3 by blast
qed


subsection \<open>The strict inclusion on proper ofilters is well-founded\<close>

definition ofilterIncl :: "'a rel \<Rightarrow> 'a set rel"
  where
    "ofilterIncl r \<equiv> {(A,B). wo_rel.ofilter r A \<and> A \<noteq> Field r \<and>
                         wo_rel.ofilter r B \<and> B \<noteq> Field r \<and> A < B}"

lemma wf_ofilterIncl:
  assumes WELL: "Well_order r"
  shows "wf(ofilterIncl r)"
proof-
  have Well: "wo_rel r" using WELL by (simp add: wo_rel_def)
  hence Lo: "Linear_order r" by (simp add: wo_rel.LIN)
  let ?h = "(\<lambda> A. wo_rel.suc r A)"
  let ?rS = "r - Id"
  have "wf ?rS" using WELL by (simp add: order_on_defs)
  moreover
  have "compat (ofilterIncl r) ?rS ?h"
  proof(unfold compat_def ofilterIncl_def,
      intro allI impI, simp, elim conjE)
    fix A B
    assume *: "wo_rel.ofilter r A" "A \<noteq> Field r" and
      **: "wo_rel.ofilter r B" "B \<noteq> Field r" and ***: "A < B"
    then obtain a and b where 0: "a \<in> Field r \<and> b \<in> Field r" and
      1: "A = underS r a \<and> B = underS r b"
      using Well by (auto simp add: wo_rel.ofilter_underS_Field)
    hence "a \<noteq> b" using *** by auto
    moreover
    have "(a,b) \<in> r" using 0 1 Lo ***
      by (auto simp add: underS_incl_iff)
    moreover
    have "a = wo_rel.suc r A \<and> b = wo_rel.suc r B"
      using Well 0 1 by (simp add: wo_rel.suc_underS)
    ultimately
    show "(wo_rel.suc r A, wo_rel.suc r B) \<in> r \<and> wo_rel.suc r A \<noteq> wo_rel.suc r B"
      by simp
  qed
  ultimately show "wf (ofilterIncl r)" by (simp add: compat_wf)
qed


subsection \<open>Ordering the well-orders by existence of embeddings\<close>

text \<open>We define three relations between well-orders:
\begin{itemize}
\item \<open>ordLeq\<close>, of being embedded (abbreviated \<open>\<le>o\<close>);
\item \<open>ordLess\<close>, of being strictly embedded (abbreviated \<open><o\<close>);
\item \<open>ordIso\<close>, of being isomorphic (abbreviated \<open>=o\<close>).
\end{itemize}
%
The prefix "ord" and the index "o" in these names stand for "ordinal-like".
These relations shall be proved to be inter-connected in a similar fashion as the trio
\<open>\<le>\<close>, \<open><\<close>, \<open>=\<close> associated to a total order on a set.
\<close>

definition ordLeq :: "('a rel * 'a' rel) set"
  where
    "ordLeq = {(r,r'). Well_order r \<and> Well_order r' \<and> (\<exists>f. embed r r' f)}"

abbreviation ordLeq2 :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> bool" (infix \<open><=o\<close> 50)
  where "r <=o r' \<equiv> (r,r') \<in> ordLeq"

abbreviation ordLeq3 :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> bool" (infix \<open>\<le>o\<close> 50)
  where "r \<le>o r' \<equiv> r <=o r'"

definition ordLess :: "('a rel * 'a' rel) set"
  where
    "ordLess = {(r,r'). Well_order r \<and> Well_order r' \<and> (\<exists>f. embedS r r' f)}"

abbreviation ordLess2 :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> bool" (infix \<open><o\<close> 50)
  where "r <o r' \<equiv> (r,r') \<in> ordLess"

definition ordIso :: "('a rel * 'a' rel) set"
  where
    "ordIso = {(r,r'). Well_order r \<and> Well_order r' \<and> (\<exists>f. iso r r' f)}"

abbreviation ordIso2 :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> bool" (infix \<open>=o\<close> 50)
  where "r =o r' \<equiv> (r,r') \<in> ordIso"

lemmas ordRels_def = ordLeq_def ordLess_def ordIso_def

lemma ordLeq_Well_order_simp:
  assumes "r \<le>o r'"
  shows "Well_order r \<and> Well_order r'"
  using assms unfolding ordLeq_def by simp

text\<open>Notice that the relations \<open>\<le>o\<close>, \<open><o\<close>, \<open>=o\<close> connect well-orders
on potentially {\em distinct} types. However, some of the lemmas below, including the next one,
restrict implicitly the type of these relations to \<open>(('a rel) * ('a rel)) set\<close> , i.e.,
to \<open>'a rel rel\<close>.\<close>

lemma ordLeq_reflexive:
  "Well_order r \<Longrightarrow> r \<le>o r"
  unfolding ordLeq_def using id_embed[of r] by blast

lemma ordLeq_transitive[trans]:
  assumes "r \<le>o r'" and "r' \<le>o r''"
  shows "r \<le>o r''"
  using assms by (auto simp: ordLeq_def intro: comp_embed)

lemma ordLeq_total:
  "\<lbrakk>Well_order r; Well_order r'\<rbrakk> \<Longrightarrow> r \<le>o r' \<or> r' \<le>o r"
  unfolding ordLeq_def using wellorders_totally_ordered by blast

lemma ordIso_reflexive:
  "Well_order r \<Longrightarrow> r =o r"
  unfolding ordIso_def using id_iso[of r] by blast

lemma ordIso_transitive[trans]:
  assumes *: "r =o r'" and **: "r' =o r''"
  shows "r =o r''"
  using assms by (auto simp: ordIso_def intro: comp_iso)

lemma ordIso_symmetric:
  assumes *: "r =o r'"
  shows "r' =o r"
proof-
  obtain f where 1: "Well_order r \<and> Well_order r'" and
    2: "embed r r' f \<and> bij_betw f (Field r) (Field r')"
    using * by (auto simp add: ordIso_def iso_def)
  let ?f' = "inv_into (Field r) f"
  have "embed r' r ?f' \<and> bij_betw ?f' (Field r') (Field r)"
    using 1 2 by (simp add: bij_betw_inv_into inv_into_Field_embed_bij_betw)
  thus "r' =o r" unfolding ordIso_def using 1 by (auto simp add: iso_def)
qed

lemma ordLeq_ordLess_trans[trans]:
  assumes "r \<le>o r'" and " r' <o r''"
  shows "r <o r''"
proof-
  have "Well_order r \<and> Well_order r''"
    using assms unfolding ordLeq_def ordLess_def by auto
  thus ?thesis using assms unfolding ordLeq_def ordLess_def
    using embed_comp_embedS by blast
qed

lemma ordLess_ordLeq_trans[trans]:
  assumes "r <o r'" and " r' \<le>o r''"
  shows "r <o r''"
  using embedS_comp_embed assms by (force simp: ordLeq_def ordLess_def)

lemma ordLeq_ordIso_trans[trans]:
  assumes "r \<le>o r'" and " r' =o r''"
  shows "r \<le>o r''"
  using embed_comp_iso assms by (force simp: ordLeq_def ordIso_def)

lemma ordIso_ordLeq_trans[trans]:
  assumes "r =o r'" and " r' \<le>o r''"
  shows "r \<le>o r''"
  using iso_comp_embed assms by (force simp: ordLeq_def ordIso_def)

lemma ordLess_ordIso_trans[trans]:
  assumes "r <o r'" and " r' =o r''"
  shows "r <o r''"
  using embedS_comp_iso assms by (force simp: ordLess_def ordIso_def)

lemma ordIso_ordLess_trans[trans]:
  assumes "r =o r'" and " r' <o r''"
  shows "r <o r''"
  using iso_comp_embedS assms by (force simp: ordLess_def ordIso_def)

lemma ordLess_not_embed:
  assumes "r <o r'"
  shows "\<not>(\<exists>f'. embed r' r f')"
proof-
  obtain f where 1: "Well_order r \<and> Well_order r'" and 2: "embed r r' f" and
    3: " \<not> bij_betw f (Field r) (Field r')"
    using assms unfolding ordLess_def by (auto simp add: embedS_def)
  {fix f' assume *: "embed r' r f'"
    hence "bij_betw f (Field r) (Field r')" using 1 2
      by (simp add: embed_bothWays_Field_bij_betw)
    with 3 have False by contradiction
  }
  thus ?thesis by blast
qed

lemma ordLess_Field:
  assumes OL: "r1 <o r2" and EMB: "embed r1 r2 f"
  shows "\<not> (f`(Field r1) = Field r2)"
proof-
  let ?A1 = "Field r1"  let ?A2 = "Field r2"
  obtain g where
    0: "Well_order r1 \<and> Well_order r2" and
    1: "embed r1 r2 g \<and> \<not>(bij_betw g ?A1 ?A2)"
    using OL unfolding ordLess_def by (auto simp add: embedS_def)
  hence "\<forall>a \<in> ?A1. f a = g a"
    using 0 EMB embed_unique[of r1] by auto
  hence "\<not>(bij_betw f ?A1 ?A2)"
    using 1 bij_betw_cong[of ?A1] by blast
  moreover
  have "inj_on f ?A1" using EMB 0 by (simp add: embed_inj_on)
  ultimately show ?thesis by (simp add: bij_betw_def)
qed

lemma ordLess_iff:
  "r <o r' = (Well_order r \<and> Well_order r' \<and> \<not>(\<exists>f'. embed r' r f'))"
proof
  assume *: "r <o r'"
  hence "\<not>(\<exists>f'. embed r' r f')" using ordLess_not_embed[of r r'] by simp
  with * show "Well_order r \<and> Well_order r' \<and> \<not> (\<exists>f'. embed r' r f')"
    unfolding ordLess_def by auto
next
  assume *: "Well_order r \<and> Well_order r' \<and> \<not> (\<exists>f'. embed r' r f')"
  then obtain f where 1: "embed r r' f"
    using wellorders_totally_ordered[of r r'] by blast
  moreover
  {assume "bij_betw f (Field r) (Field r')"
    with * 1 have "embed r' r (inv_into (Field r) f) "
      using inv_into_Field_embed_bij_betw[of r r' f] by auto
    with * have False by blast
  }
  ultimately show "(r,r') \<in> ordLess"
    unfolding ordLess_def using * by (fastforce simp add: embedS_def)
qed

lemma ordLess_irreflexive: "\<not> r <o r"
  using id_embed[of r] by (auto simp: ordLess_iff)

lemma ordLeq_iff_ordLess_or_ordIso:
  "r \<le>o r' = (r <o r' \<or> r =o r')"
  unfolding ordRels_def embedS_defs iso_defs by blast

lemma ordIso_iff_ordLeq:
  "(r =o r') = (r \<le>o r' \<and> r' \<le>o r)"
proof
  assume "r =o r'"
  then obtain f where 1: "Well_order r \<and> Well_order r' \<and>
                     embed r r' f \<and> bij_betw f (Field r) (Field r')"
    unfolding ordIso_def iso_defs by auto
  hence "embed r r' f \<and> embed r' r (inv_into (Field r) f)"
    by (simp add: inv_into_Field_embed_bij_betw)
  thus  "r \<le>o r' \<and> r' \<le>o r"
    unfolding ordLeq_def using 1 by auto
next
  assume "r \<le>o r' \<and> r' \<le>o r"
  then obtain f and g where 1: "Well_order r \<and> Well_order r' \<and>
                           embed r r' f \<and> embed r' r g"
    unfolding ordLeq_def by auto
  hence "iso r r' f" by (auto simp add: embed_bothWays_iso)
  thus "r =o r'" unfolding ordIso_def using 1 by auto
qed

lemma not_ordLess_ordLeq:
  "r <o r' \<Longrightarrow> \<not> r' \<le>o r"
  using ordLess_ordLeq_trans ordLess_irreflexive by blast

lemma not_ordLeq_ordLess:
  "r \<le>o r' \<Longrightarrow> \<not> r' <o r"
  using not_ordLess_ordLeq by blast

lemma ordLess_or_ordLeq:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "r <o r' \<or> r' \<le>o r"
proof-
  have "r \<le>o r' \<or> r' \<le>o r"
    using assms by (simp add: ordLeq_total)
  moreover
  {assume "\<not> r <o r' \<and> r \<le>o r'"
    hence "r =o r'" using ordLeq_iff_ordLess_or_ordIso by blast
    hence "r' \<le>o r" using ordIso_symmetric ordIso_iff_ordLeq by blast
  }
  ultimately show ?thesis by blast
qed

lemma not_ordLess_ordIso:
  "r <o r' \<Longrightarrow> \<not> r =o r'"
  using ordLess_ordIso_trans ordIso_symmetric ordLess_irreflexive by blast

lemma not_ordLeq_iff_ordLess:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "(\<not> r' \<le>o r) = (r <o r')"
  using assms not_ordLess_ordLeq ordLess_or_ordLeq by blast

lemma not_ordLess_iff_ordLeq:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "(\<not> r' <o r) = (r \<le>o r')"
  using assms not_ordLess_ordLeq ordLess_or_ordLeq by blast

lemma ordLess_transitive[trans]:
  "\<lbrakk>r <o r'; r' <o r''\<rbrakk> \<Longrightarrow> r <o r''"
  using ordLess_ordLeq_trans ordLeq_iff_ordLess_or_ordIso by blast

corollary ordLess_trans: "trans ordLess"
  unfolding trans_def using ordLess_transitive by blast

lemmas ordIso_equivalence = ordIso_transitive ordIso_reflexive ordIso_symmetric

lemma ordIso_imp_ordLeq:
  "r =o r' \<Longrightarrow> r \<le>o r'"
  using ordIso_iff_ordLeq by blast

lemma ordLess_imp_ordLeq:
  "r <o r' \<Longrightarrow> r \<le>o r'"
  using ordLeq_iff_ordLess_or_ordIso by blast

lemma ofilter_subset_ordLeq:
  assumes WELL: "Well_order r" and
    OFA: "wo_rel.ofilter r A" and OFB: "wo_rel.ofilter r B"
  shows "(A \<le> B) = (Restr r A \<le>o Restr r B)"
proof
  assume "A \<le> B"
  thus "Restr r A \<le>o Restr r B"
    unfolding ordLeq_def using assms
      Well_order_Restr Well_order_Restr ofilter_subset_embed by blast
next
  assume *: "Restr r A \<le>o Restr r B"
  then obtain f where "embed (Restr r A) (Restr r B) f"
    unfolding ordLeq_def by blast
  {assume "B < A"
    hence "Restr r B <o Restr r A"
      unfolding ordLess_def using assms
        Well_order_Restr Well_order_Restr ofilter_subset_embedS by blast
    hence False using * not_ordLess_ordLeq by blast
  }
  thus "A \<le> B" using OFA OFB WELL
      wo_rel_def[of r] wo_rel.ofilter_linord[of r A B] by blast
qed

lemma ofilter_subset_ordLess:
  assumes WELL: "Well_order r" and
    OFA: "wo_rel.ofilter r A" and OFB: "wo_rel.ofilter r B"
  shows "(A < B) = (Restr r A <o Restr r B)"
proof-
  let ?rA = "Restr r A" let ?rB = "Restr r B"
  have 1: "Well_order ?rA \<and> Well_order ?rB"
    using WELL Well_order_Restr by blast
  have "(A < B) = (\<not> B \<le> A)" using assms
      wo_rel_def wo_rel.ofilter_linord[of r A B] by blast
  also have "\<dots> = (\<not> Restr r B \<le>o Restr r A)"
    using assms ofilter_subset_ordLeq by blast
  also have "\<dots> = (Restr r A <o Restr r B)"
    using 1 not_ordLeq_iff_ordLess by blast
  finally show ?thesis .
qed

lemma ofilter_ordLess:
  "\<lbrakk>Well_order r; wo_rel.ofilter r A\<rbrakk> \<Longrightarrow> (A < Field r) = (Restr r A <o r)"
  by (simp add: ofilter_subset_ordLess wo_rel.Field_ofilter
      wo_rel_def Restr_Field)

corollary underS_Restr_ordLess:
  assumes "Well_order r" and "Field r \<noteq> {}"
  shows "Restr r (underS r a) <o r"
proof-
  have "underS r a < Field r" using assms
    by (simp add: underS_Field3)
  thus ?thesis using assms
    by (simp add: ofilter_ordLess wo_rel.underS_ofilter wo_rel_def)
qed

lemma embed_ordLess_ofilterIncl:
  assumes
    OL12: "r1 <o r2" and OL23: "r2 <o r3" and
    EMB13: "embed r1 r3 f13" and EMB23: "embed r2 r3 f23"
  shows "(f13`(Field r1), f23`(Field r2)) \<in> (ofilterIncl r3)"
proof-
  have OL13: "r1 <o r3"
    using OL12 OL23 using ordLess_transitive by auto
  let ?A1 = "Field r1"  let ?A2 ="Field r2" let ?A3 ="Field r3"
  obtain f12 g23 where
    0: "Well_order r1 \<and> Well_order r2 \<and> Well_order r3" and
    1: "embed r1 r2 f12 \<and> \<not>(bij_betw f12 ?A1 ?A2)" and
    2: "embed r2 r3 g23 \<and> \<not>(bij_betw g23 ?A2 ?A3)"
    using OL12 OL23 by (auto simp add: ordLess_def embedS_def)
  hence "\<forall>a \<in> ?A2. f23 a = g23 a"
    using EMB23 embed_unique[of r2 r3] by blast
  hence 3: "\<not>(bij_betw f23 ?A2 ?A3)"
    using 2 bij_betw_cong[of ?A2 f23 g23] by blast
      (*  *)
  have 4: "wo_rel.ofilter r2 (f12 ` ?A1) \<and> f12 ` ?A1 \<noteq> ?A2"
    using 0 1 OL12 by (simp add: embed_Field_ofilter ordLess_Field)
  have 5: "wo_rel.ofilter r3 (f23 ` ?A2) \<and> f23 ` ?A2 \<noteq> ?A3"
    using 0 EMB23 OL23 by (simp add: embed_Field_ofilter ordLess_Field)
  have 6: "wo_rel.ofilter r3 (f13 ` ?A1)  \<and> f13 ` ?A1 \<noteq> ?A3"
    using 0 EMB13 OL13 by (simp add: embed_Field_ofilter ordLess_Field)
      (*  *)
  have "f12 ` ?A1 < ?A2"
    using 0 4 by (auto simp add: wo_rel_def wo_rel.ofilter_def)
  moreover have "inj_on f23 ?A2"
    using EMB23 0 by (simp add: wo_rel_def embed_inj_on)
  ultimately
  have "f23 ` (f12 ` ?A1) < f23 ` ?A2" by (simp add: image_strict_mono)
  moreover
  {have "embed r1 r3 (f23 \<circ> f12)"
      using 1 EMB23 0 by (auto simp add: comp_embed)
    hence "\<forall>a \<in> ?A1. f23(f12 a) = f13 a"
      using EMB13 0 embed_unique[of r1 r3 "f23 \<circ> f12" f13] by auto
    hence "f23 ` (f12 ` ?A1) = f13 ` ?A1" by force
  }
  ultimately
  have "f13 ` ?A1 < f23 ` ?A2" by simp
      (*  *)
  with 5 6 show ?thesis
    unfolding ofilterIncl_def by auto
qed

lemma ordLess_iff_ordIso_Restr:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "(r' <o r) = (\<exists>a \<in> Field r. r' =o Restr r (underS r a))"
proof safe
  fix a assume *: "a \<in> Field r" and **: "r' =o Restr r (underS r a)"
  hence "Restr r (underS r a) <o r" using WELL underS_Restr_ordLess[of r] by blast
  thus "r' <o r" using ** ordIso_ordLess_trans by blast
next
  assume "r' <o r"
  then obtain f where 1: "Well_order r \<and> Well_order r'" and
    2: "embed r' r f \<and> f ` (Field r') \<noteq> Field r"
    unfolding ordLess_def embedS_def[abs_def] bij_betw_def using embed_inj_on by blast
  hence "wo_rel.ofilter r (f ` (Field r'))" using embed_Field_ofilter by blast
  then obtain a where 3: "a \<in> Field r" and 4: "underS r a = f ` (Field r')"
    using 1 2 by (auto simp add: wo_rel.ofilter_underS_Field wo_rel_def)
  have "iso r' (Restr r (f ` (Field r'))) f"
    using embed_implies_iso_Restr 2 assms by blast
  moreover have "Well_order (Restr r (f ` (Field r')))"
    using WELL Well_order_Restr by blast
  ultimately have "r' =o Restr r (f ` (Field r'))"
    using WELL' unfolding ordIso_def by auto
  hence "r' =o Restr r (underS r a)" using 4 by auto
  thus "\<exists>a \<in> Field r. r' =o Restr r (underS r a)" using 3 by auto
qed

lemma internalize_ordLess:
  "(r' <o r) = (\<exists>p. Field p < Field r \<and> r' =o p \<and> p <o r)"
proof
  assume *: "r' <o r"
  hence 0: "Well_order r \<and> Well_order r'" unfolding ordLess_def by auto
  with * obtain a where 1: "a \<in> Field r" and 2: "r' =o Restr r (underS r a)"
    using ordLess_iff_ordIso_Restr by blast
  let ?p = "Restr r (underS r a)"
  have "wo_rel.ofilter r (underS r a)" using 0
    by (simp add: wo_rel_def wo_rel.underS_ofilter)
  hence "Field ?p = underS r a" using 0 Field_Restr_ofilter by blast
  hence "Field ?p < Field r" using underS_Field2 1 by fast
  moreover have "?p <o r" using underS_Restr_ordLess[of r a] 0 1 by blast
  ultimately show "\<exists>p. Field p < Field r \<and> r' =o p \<and> p <o r" using 2 by blast
next
  assume "\<exists>p. Field p < Field r \<and> r' =o p \<and> p <o r"
  thus "r' <o r" using ordIso_ordLess_trans by blast
qed

lemma internalize_ordLeq:
  "(r' \<le>o r) = (\<exists>p. Field p \<le> Field r \<and> r' =o p \<and> p \<le>o r)"
proof
  assume *: "r' \<le>o r"
  moreover
  have "r' <o r \<Longrightarrow> \<exists>p. Field p \<le> Field r \<and> r' =o p \<and> p \<le>o r"
    using ordLeq_iff_ordLess_or_ordIso internalize_ordLess[of r' r] by blast
  moreover
  have "r \<le>o r" using * ordLeq_def ordLeq_reflexive by blast
  ultimately show "\<exists>p. Field p \<le> Field r \<and> r' =o p \<and> p \<le>o r"
    using ordLeq_iff_ordLess_or_ordIso by blast
next
  assume "\<exists>p. Field p \<le> Field r \<and> r' =o p \<and> p \<le>o r"
  thus "r' \<le>o r" using ordIso_ordLeq_trans by blast
qed

lemma ordLeq_iff_ordLess_Restr:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "(r \<le>o r') = (\<forall>a \<in> Field r. Restr r (underS r a) <o r')"
proof safe
  assume *: "r \<le>o r'"
  fix a assume "a \<in> Field r"
  hence "Restr r (underS r a) <o r"
    using WELL underS_Restr_ordLess[of r] by blast
  thus "Restr r (underS r a) <o r'"
    using * ordLess_ordLeq_trans by blast
next
  assume *: "\<forall>a \<in> Field r. Restr r (underS r a) <o r'"
  {assume "r' <o r"
    then obtain a where "a \<in> Field r \<and> r' =o Restr r (underS r a)"
      using assms ordLess_iff_ordIso_Restr by blast
    hence False using * not_ordLess_ordIso ordIso_symmetric by blast
  }
  thus "r \<le>o r'" using ordLess_or_ordLeq assms by blast
qed

lemma finite_ordLess_infinite:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    FIN: "finite(Field r)" and INF: "\<not>finite(Field r')"
  shows "r <o r'"
proof-
  {assume "r' \<le>o r"
    then obtain h where "inj_on h (Field r') \<and> h ` (Field r') \<le> Field r"
      unfolding ordLeq_def using assms embed_inj_on embed_Field by blast
    hence False using finite_imageD finite_subset FIN INF by blast
  }
  thus ?thesis using WELL WELL' ordLess_or_ordLeq by blast
qed

lemma finite_well_order_on_ordIso:
  assumes FIN: "finite A" and
    WELL: "well_order_on A r" and WELL': "well_order_on A r'"
  shows "r =o r'"
proof-
  have 0: "Well_order r \<and> Well_order r' \<and> Field r = A \<and> Field r' = A"
    using assms well_order_on_Well_order by blast
  moreover
  have "\<forall>r r'. well_order_on A r \<and> well_order_on A r' \<and> r \<le>o r'
                  \<longrightarrow> r =o r'"
  proof(clarify)
    fix r r' assume *: "well_order_on A r" and **: "well_order_on A r'"
    have 2: "Well_order r \<and> Well_order r' \<and> Field r = A \<and> Field r' = A"
      using * ** well_order_on_Well_order by blast
    assume "r \<le>o r'"
    then obtain f where 1: "embed r r' f" and
      "inj_on f A \<and> f ` A \<le> A"
      unfolding ordLeq_def using 2 embed_inj_on embed_Field by blast
    hence "bij_betw f A A" unfolding bij_betw_def using FIN endo_inj_surj by blast
    thus "r =o r'" unfolding ordIso_def iso_def[abs_def] using 1 2 by auto
  qed
  ultimately show ?thesis using assms ordLeq_total ordIso_symmetric by blast
qed

subsection\<open>\<open><o\<close> is well-founded\<close>

text \<open>Of course, it only makes sense to state that the \<open><o\<close> is well-founded
on the restricted type \<open>'a rel rel\<close>.  We prove this by first showing that, for any set
of well-orders all embedded in a fixed well-order, the function mapping each well-order
in the set to an order filter of the fixed well-order is compatible w.r.t. to \<open><o\<close> versus
{\em strict inclusion}; and we already know that strict inclusion of order filters is well-founded.\<close>

definition ord_to_filter :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set"
  where "ord_to_filter r0 r \<equiv> (SOME f. embed r r0 f) ` (Field r)"

lemma ord_to_filter_compat:
  "compat (ordLess Int (ordLess\<inverse>``{r0} \<times> ordLess\<inverse>``{r0}))
        (ofilterIncl r0)
        (ord_to_filter r0)"
proof(unfold compat_def ord_to_filter_def, clarify)
  fix r1::"'a rel" and r2::"'a rel"
  let ?A1 = "Field r1"  let ?A2 ="Field r2" let ?A0 ="Field r0"
  let ?phi10 = "\<lambda> f10. embed r1 r0 f10" let ?f10 = "SOME f. ?phi10 f"
  let ?phi20 = "\<lambda> f20. embed r2 r0 f20" let ?f20 = "SOME f. ?phi20 f"
  assume *: "r1 <o r0" "r2 <o r0" and **: "r1 <o r2"
  hence "(\<exists>f. ?phi10 f) \<and> (\<exists>f. ?phi20 f)"
    by (auto simp add: ordLess_def embedS_def)
  hence "?phi10 ?f10 \<and> ?phi20 ?f20" by (auto simp add: someI_ex)
  thus "(?f10 ` ?A1, ?f20 ` ?A2) \<in> ofilterIncl r0"
    using * ** by (simp add: embed_ordLess_ofilterIncl)
qed

theorem wf_ordLess: "wf ordLess"
proof-
  {fix r0 :: "('a \<times> 'a) set"
      (* need to annotate here!*)
    let ?ordLess = "ordLess::('d rel * 'd rel) set"
    let ?R = "?ordLess Int (?ordLess\<inverse>``{r0} \<times> ?ordLess\<inverse>``{r0})"
    {assume Case1: "Well_order r0"
      hence "wf ?R"
        using wf_ofilterIncl[of r0]
          compat_wf[of ?R "ofilterIncl r0" "ord_to_filter r0"]
          ord_to_filter_compat[of r0] by auto
    }
    moreover
    {assume Case2: "\<not> Well_order r0"
      hence "?R = {}" unfolding ordLess_def by auto
      hence "wf ?R" by simp
    }
    ultimately have "wf ?R" by blast
  }
  thus ?thesis by (simp add: trans_wf_iff ordLess_trans)
qed

corollary exists_minim_Well_order:
  assumes NE: "R \<noteq> {}" and WELL: "\<forall>r \<in> R. Well_order r"
  shows "\<exists>r \<in> R. \<forall>r' \<in> R. r \<le>o r'"
proof-
  obtain r where "r \<in> R \<and> (\<forall>r' \<in> R. \<not> r' <o r)"
    using NE spec[OF spec[OF subst[OF wf_eq_minimal, of "%x. x", OF wf_ordLess]], of _ R]
      equals0I[of R] by blast
  with not_ordLeq_iff_ordLess WELL show ?thesis by blast
qed


subsection \<open>Copy via direct images\<close>

text\<open>The direct image operator is the dual of the inverse image operator \<open>inv_image\<close>
from \<open>Relation.thy\<close>.  It is useful for transporting a well-order between
different types.\<close>

definition dir_image :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'a') \<Rightarrow> 'a' rel"
  where
    "dir_image r f = {(f a, f b)| a b. (a,b) \<in> r}"

lemma dir_image_Field:
  "Field(dir_image r f) = f ` (Field r)"
  unfolding dir_image_def Field_def Range_def Domain_def by fast

lemma dir_image_minus_Id:
  "inj_on f (Field r) \<Longrightarrow> (dir_image r f) - Id = dir_image (r - Id) f"
  unfolding inj_on_def Field_def dir_image_def by auto

lemma dir_image_subset:
  assumes "r \<subseteq> A \<times> B"
  shows "dir_image r f \<subseteq> f ` A \<times> f ` B"
proof (rule subsetI)
  fix x
  assume "x \<in> dir_image r f"
  then obtain a b where "x = (f a, f b)" and "(a, b) \<in> r"
    unfolding dir_image_def by blast
  thus "x \<in> f ` A \<times> f ` B"
    using \<open>r \<subseteq> A \<times> B\<close> by auto
qed

lemma Refl_dir_image:
  assumes "Refl r"
  shows "Refl(dir_image r f)"
proof-
  {fix a' b'
    assume "(a',b') \<in> dir_image r f"
    then obtain a b where 1: "a' = f a \<and> b' = f b \<and> (a,b) \<in> r"
      unfolding dir_image_def by blast
    hence "a \<in> Field r \<and> b \<in> Field r" using Field_def by fastforce
    hence "(a,a) \<in> r \<and> (b,b) \<in> r" using assms by (simp add: refl_on_def)
    with 1 have "(a',a') \<in> dir_image r f \<and> (b',b') \<in> dir_image r f"
      unfolding dir_image_def by auto
  }
  thus ?thesis
    by(unfold refl_on_def Field_def Domain_def Range_def, auto)
qed

lemma trans_dir_image:
  assumes TRANS: "trans r" and INJ: "inj_on f (Field r)"
  shows "trans(dir_image r f)"
  unfolding trans_def
proof safe
  fix a' b' c'
  assume "(a',b') \<in> dir_image r f" "(b',c') \<in> dir_image r f"
  then obtain a b1 b2 c where 1: "a' = f a \<and> b' = f b1 \<and> b' = f b2 \<and> c' = f c" and
    2: "(a,b1) \<in> r \<and> (b2,c) \<in> r"
    unfolding dir_image_def by blast
  hence "b1 \<in> Field r \<and> b2 \<in> Field r"
    unfolding Field_def by auto
  hence "b1 = b2" using 1 INJ unfolding inj_on_def by auto
  hence "(a,c) \<in> r" using 2 TRANS unfolding trans_def by blast
  thus "(a',c') \<in> dir_image r f"
    unfolding dir_image_def using 1 by auto
qed

lemma Preorder_dir_image:
  assumes "Preorder r" and inj: "inj_on f (Field r)"
  shows "Preorder (dir_image r f)"
  unfolding preorder_on_def
proof (intro conjI)
  have "r \<subseteq> Field r \<times> Field r" and "Refl r" and "trans r"
    using \<open>Preorder r\<close> by (simp_all only: preorder_on_def)

  show "dir_image r f \<subseteq> Field (dir_image r f) \<times> Field (dir_image r f)"
    using dir_image_subset[OF \<open>r \<subseteq> Field r \<times> Field r\<close>]
    unfolding dir_image_Field .

  show "Refl (dir_image r f)"
    using Refl_dir_image[OF \<open>Refl r\<close>] .

  show "trans (dir_image r f)"
    using trans_dir_image[OF \<open>trans r\<close> inj] .
qed

lemma antisym_dir_image:
  assumes AN: "antisym r" and INJ: "inj_on f (Field r)"
  shows "antisym(dir_image r f)"
  unfolding antisym_def
proof safe
  fix a' b'
  assume "(a',b') \<in> dir_image r f" "(b',a') \<in> dir_image r f"
  then obtain a1 b1 a2 b2 where 1: "a' = f a1 \<and> a' = f a2 \<and> b' = f b1 \<and> b' = f b2" and
    2: "(a1,b1) \<in> r \<and> (b2,a2) \<in> r " and
    3: "{a1,a2,b1,b2} \<le> Field r"
    unfolding dir_image_def Field_def by blast
  hence "a1 = a2 \<and> b1 = b2" using INJ unfolding inj_on_def by auto
  hence "a1 = b2" using 2 AN unfolding antisym_def by auto
  thus "a' = b'" using 1 by auto
qed

lemma Partial_order_dir_image:
  "\<lbrakk>Partial_order r; inj_on f (Field r)\<rbrakk> \<Longrightarrow> Partial_order (dir_image r f)"
  by (simp add: partial_order_on_def Preorder_dir_image antisym_dir_image)

lemma Total_dir_image:
  assumes TOT: "Total r" and INJ: "inj_on f (Field r)"
  shows "Total(dir_image r f)"
proof(unfold total_on_def, intro ballI impI)
  fix a' b'
  assume "a' \<in> Field (dir_image r f)" "b' \<in> Field (dir_image r f)"
  then obtain a and b where 1: "a \<in> Field r \<and> b \<in> Field r \<and> f a = a' \<and> f b = b'"
    unfolding dir_image_Field[of r f] by blast
  moreover assume "a' \<noteq> b'"
  ultimately have "a \<noteq> b" using INJ unfolding inj_on_def by auto
  hence "(a,b) \<in> r \<or> (b,a) \<in> r" using 1 TOT unfolding total_on_def by auto
  thus "(a',b') \<in> dir_image r f \<or> (b',a') \<in> dir_image r f"
    using 1 unfolding dir_image_def by auto
qed

lemma Linear_order_dir_image:
  "\<lbrakk>Linear_order r; inj_on f (Field r)\<rbrakk> \<Longrightarrow> Linear_order (dir_image r f)"
  by (simp add: linear_order_on_def Partial_order_dir_image Total_dir_image)

lemma wf_dir_image:
  assumes WF: "wf r" and INJ: "inj_on f (Field r)"
  shows "wf(dir_image r f)"
proof(unfold wf_eq_minimal2, intro allI impI, elim conjE)
  fix A'::"'b set"
  assume SUB: "A' \<le> Field(dir_image r f)" and NE: "A' \<noteq> {}"
  obtain A where A_def: "A = {a \<in> Field r. f a \<in> A'}" by blast
  have "A \<noteq> {} \<and> A \<le> Field r" using A_def SUB NE by (auto simp: dir_image_Field)
  then obtain a where 1: "a \<in> A \<and> (\<forall>b \<in> A. (b,a) \<notin> r)"
    using spec[OF WF[unfolded wf_eq_minimal2], of A] by blast
  have "\<forall>b' \<in> A'. (b',f a) \<notin> dir_image r f"
  proof(clarify)
    fix b' assume *: "b' \<in> A'" and **: "(b',f a) \<in> dir_image r f"
    obtain b1 a1 where 2: "b' = f b1 \<and> f a = f a1" and
      3: "(b1,a1) \<in> r \<and> {a1,b1} \<le> Field r"
      using ** unfolding dir_image_def Field_def by blast
    hence "a = a1" using 1 A_def INJ unfolding inj_on_def by auto
    hence "b1 \<in> A \<and> (b1,a) \<in> r" using 2 3 A_def * by auto
    with 1 show False by auto
  qed
  thus "\<exists>a'\<in>A'. \<forall>b'\<in>A'. (b', a') \<notin> dir_image r f"
    using A_def 1 by blast
qed

lemma Well_order_dir_image:
  "\<lbrakk>Well_order r; inj_on f (Field r)\<rbrakk> \<Longrightarrow> Well_order (dir_image r f)"
  unfolding well_order_on_def
  using Linear_order_dir_image[of r f] wf_dir_image[of "r - Id" f]
    dir_image_minus_Id[of f r]
    inj_on_subset[of f "Field r" "Field(r - Id)"]
    mono_Field[of "r - Id" r] by auto

lemma dir_image_bij_betw:
  "\<lbrakk>inj_on f (Field r)\<rbrakk> \<Longrightarrow> bij_betw f (Field r) (Field (dir_image r f))"
  unfolding bij_betw_def by (simp add: dir_image_Field order_on_defs)

lemma dir_image_compat:
  "compat r (dir_image r f) f"
  unfolding compat_def dir_image_def by auto

lemma dir_image_iso:
  "\<lbrakk>Well_order r; inj_on f (Field r)\<rbrakk>  \<Longrightarrow> iso r (dir_image r f) f"
  using iso_iff3 dir_image_compat dir_image_bij_betw Well_order_dir_image by blast

lemma dir_image_ordIso:
  "\<lbrakk>Well_order r; inj_on f (Field r)\<rbrakk>  \<Longrightarrow> r =o dir_image r f"
  unfolding ordIso_def using dir_image_iso Well_order_dir_image by blast

lemma Well_order_iso_copy:
  assumes WELL: "well_order_on A r" and BIJ: "bij_betw f A A'"
  shows "\<exists>r'. well_order_on A' r' \<and> r =o r'"
proof-
  let ?r' = "dir_image r f"
  have 1: "A = Field r \<and> Well_order r"
    using WELL well_order_on_Well_order by blast
  hence 2: "iso r ?r' f"
    using dir_image_iso using BIJ unfolding bij_betw_def by auto
  hence "f ` (Field r) = Field ?r'" using 1 iso_iff[of r ?r'] by blast
  hence "Field ?r' = A'"
    using 1 BIJ unfolding bij_betw_def by auto
  moreover have "Well_order ?r'"
    using 1 Well_order_dir_image BIJ unfolding bij_betw_def by blast
  ultimately show ?thesis unfolding ordIso_def using 1 2 by blast
qed


subsection \<open>Bounded square\<close>

text\<open>This construction essentially defines, for an order relation \<open>r\<close>, a lexicographic
order \<open>bsqr r\<close> on \<open>(Field r) \<times> (Field r)\<close>, applying the
following criteria (in this order):
\begin{itemize}
\item compare the maximums;
\item compare the first components;
\item compare the second components.
\end{itemize}
%
The only application of this construction that we are aware of is
at proving that the square of an infinite set has the same cardinal
as that set. The essential property required there (and which is ensured by this
construction) is that any proper order filter of the product order is included in a rectangle, i.e.,
in a product of proper filters on the original relation (assumed to be a well-order).\<close>

definition bsqr :: "'a rel => ('a * 'a)rel"
  where
    "bsqr r = {((a1,a2),(b1,b2)).
           {a1,a2,b1,b2} \<le> Field r \<and>
           (a1 = b1 \<and> a2 = b2 \<or>
            (wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2) \<in> r - Id \<or>
            wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> (a1,b1) \<in> r - Id \<or>
            wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> a1 = b1  \<and> (a2,b2) \<in> r - Id
           )}"

lemma Field_bsqr:
  "Field (bsqr r) = Field r \<times> Field r"
proof
  show "Field (bsqr r) \<le> Field r \<times> Field r"
  proof-
    {fix a1 a2 assume "(a1,a2) \<in> Field (bsqr r)"
      moreover
      have "\<And> b1 b2. ((a1,a2),(b1,b2)) \<in> bsqr r \<or> ((b1,b2),(a1,a2)) \<in> bsqr r \<Longrightarrow>
                      a1 \<in> Field r \<and> a2 \<in> Field r" unfolding bsqr_def by auto
      ultimately have "a1 \<in> Field r \<and> a2 \<in> Field r" unfolding Field_def by auto
    }
    thus ?thesis unfolding Field_def by force
  qed
next
  show "Field r \<times> Field r \<le> Field (bsqr r)"
  proof safe
    fix a1 a2 assume "a1 \<in> Field r" and "a2 \<in> Field r"
    hence "((a1,a2),(a1,a2)) \<in> bsqr r" unfolding bsqr_def by blast
    thus "(a1,a2) \<in> Field (bsqr r)" unfolding Field_def by auto
  qed
qed

lemma bsqr_subset:
  assumes "r \<subseteq> Field r \<times> Field r"
  shows "bsqr r \<subseteq> Field (bsqr r) \<times> Field (bsqr r)"
  using \<open>r \<subseteq> Field r \<times> Field r\<close>
  unfolding Field_bsqr
  by (auto simp add: bsqr_def)

lemma bsqr_Refl: "Refl(bsqr r)"
  by(unfold refl_on_def Field_bsqr, auto simp add: bsqr_def)

lemma bsqr_Trans:
  assumes "Well_order r"
  shows "trans (bsqr r)"
  unfolding trans_def
proof safe
  (* Preliminary facts *)
  have Well: "wo_rel r" using assms wo_rel_def by auto
  hence Trans: "trans r" using wo_rel.TRANS by auto
  have Anti: "antisym r" using wo_rel.ANTISYM Well by auto
  hence TransS: "trans(r - Id)" using Trans by (simp add: trans_diff_Id)
      (* Main proof *)
  fix a1 a2 b1 b2 c1 c2
  assume *: "((a1,a2),(b1,b2)) \<in> bsqr r" and **: "((b1,b2),(c1,c2)) \<in> bsqr r"
  hence 0: "{a1,a2,b1,b2,c1,c2} \<le> Field r" unfolding bsqr_def by auto
  have 1: "a1 = b1 \<and> a2 = b2 \<or> (wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2) \<in> r - Id \<or>
           wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> (a1,b1) \<in> r - Id \<or>
           wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> a1 = b1 \<and> (a2,b2) \<in> r - Id"
    using * unfolding bsqr_def by auto
  have 2: "b1 = c1 \<and> b2 = c2 \<or> (wo_rel.max2 r b1 b2, wo_rel.max2 r c1 c2) \<in> r - Id \<or>
           wo_rel.max2 r b1 b2 = wo_rel.max2 r c1 c2 \<and> (b1,c1) \<in> r - Id \<or>
           wo_rel.max2 r b1 b2 = wo_rel.max2 r c1 c2 \<and> b1 = c1 \<and> (b2,c2) \<in> r - Id"
    using ** unfolding bsqr_def by auto
  show "((a1,a2),(c1,c2)) \<in> bsqr r"
  proof-
    {assume Case1: "a1 = b1 \<and> a2 = b2"
      hence ?thesis using ** by simp
    }
    moreover
    {assume Case2: "(wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2) \<in> r - Id"
      {assume Case21: "b1 = c1 \<and> b2 = c2"
        hence ?thesis using * by simp
      }
      moreover
      {assume Case22: "(wo_rel.max2 r b1 b2, wo_rel.max2 r c1 c2) \<in> r - Id"
        hence "(wo_rel.max2 r a1 a2, wo_rel.max2 r c1 c2) \<in> r - Id"
          using Case2 TransS trans_def[of "r - Id"] by blast
        hence ?thesis using 0 unfolding bsqr_def by auto
      }
      moreover
      {assume Case23_4: "wo_rel.max2 r b1 b2 = wo_rel.max2 r c1 c2"
        hence ?thesis using Case2 0 unfolding bsqr_def by auto
      }
      ultimately have ?thesis using 0 2 by auto
    }
    moreover
    {assume Case3: "wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> (a1,b1) \<in> r - Id"
      {assume Case31: "b1 = c1 \<and> b2 = c2"
        hence ?thesis using * by simp
      }
      moreover
      {assume Case32: "(wo_rel.max2 r b1 b2, wo_rel.max2 r c1 c2) \<in> r - Id"
        hence ?thesis using Case3 0 unfolding bsqr_def by auto
      }
      moreover
      {assume Case33: "wo_rel.max2 r b1 b2 = wo_rel.max2 r c1 c2 \<and> (b1,c1) \<in> r - Id"
        hence "(a1,c1) \<in> r - Id"
          using Case3 TransS trans_def[of "r - Id"] by blast
        hence ?thesis using Case3 Case33 0 unfolding bsqr_def by auto
      }
      moreover
      {assume Case33: "wo_rel.max2 r b1 b2 = wo_rel.max2 r c1 c2 \<and> b1 = c1"
        hence ?thesis using Case3 0 unfolding bsqr_def by auto
      }
      ultimately have ?thesis using 0 2 by auto
    }
    moreover
    {assume Case4: "wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> a1 = b1 \<and> (a2,b2) \<in> r - Id"
      {assume Case41: "b1 = c1 \<and> b2 = c2"
        hence ?thesis using * by simp
      }
      moreover
      {assume Case42: "(wo_rel.max2 r b1 b2, wo_rel.max2 r c1 c2) \<in> r - Id"
        hence ?thesis using Case4 0 unfolding bsqr_def by force
      }
      moreover
      {assume Case43: "wo_rel.max2 r b1 b2 = wo_rel.max2 r c1 c2 \<and> (b1,c1) \<in> r - Id"
        hence ?thesis using Case4 0 unfolding bsqr_def by auto
      }
      moreover
      {assume Case44: "wo_rel.max2 r b1 b2 = wo_rel.max2 r c1 c2 \<and> b1 = c1 \<and> (b2,c2) \<in> r - Id"
        hence "(a2,c2) \<in> r - Id"
          using Case4 TransS trans_def[of "r - Id"] by blast
        hence ?thesis using Case4 Case44 0 unfolding bsqr_def by auto
      }
      ultimately have ?thesis using 0 2 by auto
    }
    ultimately show ?thesis using 0 1 by auto
  qed
qed

lemma bsqr_antisym:
  assumes "Well_order r"
  shows "antisym (bsqr r)"
proof(unfold antisym_def, clarify)
  (* Preliminary facts *)
  have Well: "wo_rel r" using assms wo_rel_def by auto
  hence Trans: "trans r" using wo_rel.TRANS by auto
  have Anti: "antisym r" using wo_rel.ANTISYM Well by auto
  hence TransS: "trans(r - Id)" using Trans by (simp add: trans_diff_Id)
  hence IrrS: "\<forall>a b. \<not>((a,b) \<in> r - Id \<and> (b,a) \<in> r - Id)"
    using Anti trans_def[of "r - Id"] antisym_def[of "r - Id"] by blast
      (* Main proof *)
  fix a1 a2 b1 b2
  assume *: "((a1,a2),(b1,b2)) \<in> bsqr r" and **: "((b1,b2),(a1,a2)) \<in> bsqr r"
  hence "{a1,a2,b1,b2} \<le> Field r" unfolding bsqr_def by auto
  moreover
  have "a1 = b1 \<and> a2 = b2 \<or> (wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2) \<in> r - Id \<or>
           wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> (a1,b1) \<in> r - Id \<or>
           wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2 \<and> a1 = b1 \<and> (a2,b2) \<in> r - Id"
    using * unfolding bsqr_def by auto
  moreover
  have "b1 = a1 \<and> b2 = a2 \<or> (wo_rel.max2 r b1 b2, wo_rel.max2 r a1 a2) \<in> r - Id \<or>
           wo_rel.max2 r b1 b2 = wo_rel.max2 r a1 a2 \<and> (b1,a1) \<in> r - Id \<or>
           wo_rel.max2 r b1 b2 = wo_rel.max2 r a1 a2 \<and> b1 = a1 \<and> (b2,a2) \<in> r - Id"
    using ** unfolding bsqr_def by auto
  ultimately show "a1 = b1 \<and> a2 = b2"
    using IrrS by auto
qed

lemma bsqr_Total:
  assumes "Well_order r"
  shows "Total(bsqr r)"
proof-
  (* Preliminary facts *)
  have Well: "wo_rel r" using assms wo_rel_def by auto
  hence Total: "\<forall>a \<in> Field r. \<forall>b \<in> Field r. (a,b) \<in> r \<or> (b,a) \<in> r"
    using wo_rel.TOTALS by auto
      (* Main proof *)
  {fix a1 a2 b1 b2 assume "{(a1,a2), (b1,b2)} \<le> Field(bsqr r)"
    hence 0: "a1 \<in> Field r \<and> a2 \<in> Field r \<and> b1 \<in> Field r \<and> b2 \<in> Field r"
      using Field_bsqr by blast
    have "((a1,a2) = (b1,b2) \<or> ((a1,a2),(b1,b2)) \<in> bsqr r \<or> ((b1,b2),(a1,a2)) \<in> bsqr r)"
    proof(rule wo_rel.cases_Total[of r a1 a2], clarsimp simp add: Well, simp add: 0)
      (* Why didn't clarsimp simp add: Well 0 do the same job? *)
      assume Case1: "(a1,a2) \<in> r"
      hence 1: "wo_rel.max2 r a1 a2 = a2"
        using Well 0 by (simp add: wo_rel.max2_equals2)
      show ?thesis
      proof(rule wo_rel.cases_Total[of r b1 b2], clarsimp simp add: Well, simp add: 0)
        assume Case11: "(b1,b2) \<in> r"
        hence 2: "wo_rel.max2 r b1 b2 = b2"
          using Well 0 by (simp add: wo_rel.max2_equals2)
        show ?thesis
        proof(rule wo_rel.cases_Total3[of r a2 b2], clarsimp simp add: Well, simp add: 0)
          assume Case111: "(a2,b2) \<in> r - Id \<or> (b2,a2) \<in> r - Id"
          thus ?thesis using 0 1 2 unfolding bsqr_def by auto
        next
          assume Case112: "a2 = b2"
          show ?thesis
          proof(rule wo_rel.cases_Total3[of r a1 b1], clarsimp simp add: Well, simp add: 0)
            assume Case1121: "(a1,b1) \<in> r - Id \<or> (b1,a1) \<in> r - Id"
            thus ?thesis using 0 1 2 Case112 unfolding bsqr_def by auto
          next
            assume Case1122: "a1 = b1"
            thus ?thesis using Case112 by auto
          qed
        qed
      next
        assume Case12: "(b2,b1) \<in> r"
        hence 3: "wo_rel.max2 r b1 b2 = b1" using Well 0 by (simp add: wo_rel.max2_equals1)
        show ?thesis
        proof(rule wo_rel.cases_Total3[of r a2 b1], clarsimp simp add: Well, simp add: 0)
          assume Case121: "(a2,b1) \<in> r - Id \<or> (b1,a2) \<in> r - Id"
          thus ?thesis using 0 1 3 unfolding bsqr_def by auto
        next
          assume Case122: "a2 = b1"
          show ?thesis
          proof(rule wo_rel.cases_Total3[of r a1 b1], clarsimp simp add: Well, simp add: 0)
            assume Case1221: "(a1,b1) \<in> r - Id \<or> (b1,a1) \<in> r - Id"
            thus ?thesis using 0 1 3 Case122 unfolding bsqr_def by auto
          next
            assume Case1222: "a1 = b1"
            show ?thesis
            proof(rule wo_rel.cases_Total3[of r a2 b2], clarsimp simp add: Well, simp add: 0)
              assume Case12221: "(a2,b2) \<in> r - Id \<or> (b2,a2) \<in> r - Id"
              thus ?thesis using 0 1 3 Case122 Case1222 unfolding bsqr_def by auto
            next
              assume Case12222: "a2 = b2"
              thus ?thesis using Case122 Case1222 by auto
            qed
          qed
        qed
      qed
    next
      assume Case2: "(a2,a1) \<in> r"
      hence 1: "wo_rel.max2 r a1 a2 = a1" using Well 0 by (simp add: wo_rel.max2_equals1)
      show ?thesis
      proof(rule wo_rel.cases_Total[of r b1 b2], clarsimp simp add: Well, simp add: 0)
        assume Case21: "(b1,b2) \<in> r"
        hence 2: "wo_rel.max2 r b1 b2 = b2" using Well 0 by (simp add: wo_rel.max2_equals2)
        show ?thesis
        proof(rule wo_rel.cases_Total3[of r a1 b2], clarsimp simp add: Well, simp add: 0)
          assume Case211: "(a1,b2) \<in> r - Id \<or> (b2,a1) \<in> r - Id"
          thus ?thesis using 0 1 2 unfolding bsqr_def by auto
        next
          assume Case212: "a1 = b2"
          show ?thesis
          proof(rule wo_rel.cases_Total3[of r a1 b1], clarsimp simp add: Well, simp add: 0)
            assume Case2121: "(a1,b1) \<in> r - Id \<or> (b1,a1) \<in> r - Id"
            thus ?thesis using 0 1 2 Case212 unfolding bsqr_def by auto
          next
            assume Case2122: "a1 = b1"
            show ?thesis
            proof(rule wo_rel.cases_Total3[of r a2 b2], clarsimp simp add: Well, simp add: 0)
              assume Case21221: "(a2,b2) \<in> r - Id \<or> (b2,a2) \<in> r - Id"
              thus ?thesis using 0 1 2 Case212 Case2122 unfolding bsqr_def by auto
            next
              assume Case21222: "a2 = b2"
              thus ?thesis using Case2122 Case212 by auto
            qed
          qed
        qed
      next
        assume Case22: "(b2,b1) \<in> r"
        hence 3: "wo_rel.max2 r b1 b2 = b1"  using Well 0 by (simp add: wo_rel.max2_equals1)
        show ?thesis
        proof(rule wo_rel.cases_Total3[of r a1 b1], clarsimp simp add: Well, simp add: 0)
          assume Case221: "(a1,b1) \<in> r - Id \<or> (b1,a1) \<in> r - Id"
          thus ?thesis using 0 1 3 unfolding bsqr_def by auto
        next
          assume Case222: "a1 = b1"
          show ?thesis
          proof(rule wo_rel.cases_Total3[of r a2 b2], clarsimp simp add: Well, simp add: 0)
            assume Case2221: "(a2,b2) \<in> r - Id \<or> (b2,a2) \<in> r - Id"
            thus ?thesis using 0 1 3 Case222 unfolding bsqr_def by auto
          next
            assume Case2222: "a2 = b2"
            thus ?thesis using Case222 by auto
          qed
        qed
      qed
    qed
  }
  thus ?thesis unfolding total_on_def by fast
qed

lemma bsqr_Linear_order:
  assumes "Well_order r"
  shows "Linear_order(bsqr r)"
proof -
  have "r \<subseteq> Field r \<times> Field r"
    using \<open>Well_order r\<close>
    by (simp only: order_on_defs)

  thus ?thesis
    unfolding order_on_defs
    using assms bsqr_Refl bsqr_Trans bsqr_antisym bsqr_Total bsqr_subset[OF \<open>r \<subseteq> Field r \<times> Field r\<close>]
    by auto
qed

lemma bsqr_Well_order:
  assumes "Well_order r"
  shows "Well_order(bsqr r)"
  using assms
proof(simp add: bsqr_Linear_order Linear_order_Well_order_iff, intro allI impI)
  have 0: "\<forall>A \<le> Field r. A \<noteq> {} \<longrightarrow> (\<exists>a \<in> A. \<forall>a' \<in> A. (a,a') \<in> r)"
    using assms well_order_on_def Linear_order_Well_order_iff by blast
  fix D assume *: "D \<le> Field (bsqr r)" and **: "D \<noteq> {}"
  hence 1: "D \<le> Field r \<times> Field r" unfolding Field_bsqr by simp
      (*  *)
  obtain M where M_def: "M = {wo_rel.max2 r a1 a2| a1 a2. (a1,a2) \<in> D}" by blast
  have "M \<noteq> {}" using 1 M_def ** by auto
  moreover
  have "M \<le> Field r" unfolding M_def
    using 1 assms wo_rel_def[of r] wo_rel.max2_among[of r] by fastforce
  ultimately obtain m where m_min: "m \<in> M \<and> (\<forall>a \<in> M. (m,a) \<in> r)"
    using 0 by blast
      (*  *)
  obtain A1 where A1_def: "A1 = {a1. \<exists>a2. (a1,a2) \<in> D \<and> wo_rel.max2 r a1 a2 = m}" by blast
  have "A1 \<le> Field r" unfolding A1_def using 1 by auto
  moreover have "A1 \<noteq> {}" unfolding A1_def using m_min unfolding M_def by blast
  ultimately obtain a1 where a1_min: "a1 \<in> A1 \<and> (\<forall>a \<in> A1. (a1,a) \<in> r)"
    using 0 by blast
      (*  *)
  obtain A2 where A2_def: "A2 = {a2. (a1,a2) \<in> D \<and> wo_rel.max2 r a1 a2 = m}" by blast
  have "A2 \<le> Field r" unfolding A2_def using 1 by auto
  moreover have "A2 \<noteq> {}" unfolding A2_def
    using m_min a1_min unfolding A1_def M_def by blast
  ultimately obtain a2 where a2_min: "a2 \<in> A2 \<and> (\<forall>a \<in> A2. (a2,a) \<in> r)"
    using 0 by blast
      (*   *)
  have 2: "wo_rel.max2 r a1 a2 = m"
    using a1_min a2_min unfolding A1_def A2_def by auto
  have 3: "(a1,a2) \<in> D" using a2_min unfolding A2_def by auto
      (*  *)
  moreover
  {fix b1 b2 assume ***: "(b1,b2) \<in> D"
    hence 4: "{a1,a2,b1,b2} \<le> Field r" using 1 3 by blast
    have 5: "(wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2) \<in> r"
      using *** a1_min a2_min m_min unfolding A1_def A2_def M_def by auto
    have "((a1,a2),(b1,b2)) \<in> bsqr r"
    proof(cases "wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2")
      assume Case1: "wo_rel.max2 r a1 a2 \<noteq> wo_rel.max2 r b1 b2"
      thus ?thesis unfolding bsqr_def using 4 5 by auto
    next
      assume Case2: "wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2"
      hence "b1 \<in> A1" unfolding A1_def using 2 *** by auto
      hence 6: "(a1,b1) \<in> r" using a1_min by auto
      show ?thesis
      proof(cases "a1 = b1")
        assume Case21: "a1 \<noteq> b1"
        thus ?thesis unfolding bsqr_def using 4 Case2 6 by auto
      next
        assume Case22: "a1 = b1"
        hence "b2 \<in> A2" unfolding A2_def using 2 *** Case2 by auto
        hence 7: "(a2,b2) \<in> r" using a2_min by auto
        thus ?thesis unfolding bsqr_def using 4 7 Case2 Case22 by auto
      qed
    qed
  }
    (*  *)
  ultimately show "\<exists>d \<in> D. \<forall>d' \<in> D. (d,d') \<in> bsqr r" by fastforce
qed

lemma bsqr_max2:
  assumes WELL: "Well_order r" and LEQ: "((a1,a2),(b1,b2)) \<in> bsqr r"
  shows "(wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2) \<in> r"
proof-
  have "{(a1,a2),(b1,b2)} \<le> Field(bsqr r)"
    using LEQ unfolding Field_def by auto
  hence "{a1,a2,b1,b2} \<le> Field r" unfolding Field_bsqr by auto
  hence "{wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2} \<le> Field r"
    using WELL wo_rel_def[of r] wo_rel.max2_among[of r] by fastforce
  moreover have "(wo_rel.max2 r a1 a2, wo_rel.max2 r b1 b2) \<in> r \<or> wo_rel.max2 r a1 a2 = wo_rel.max2 r b1 b2"
    using LEQ unfolding bsqr_def by auto
  ultimately show ?thesis using WELL unfolding order_on_defs refl_on_def by auto
qed

lemma bsqr_ofilter:
  assumes WELL: "Well_order r" and
    OF: "wo_rel.ofilter (bsqr r) D" and SUB: "D < Field r \<times> Field r" and
    NE: "\<not> (\<exists>a. Field r = under r a)"
  shows "\<exists>A. wo_rel.ofilter r A \<and> A < Field r \<and> D \<le> A \<times> A"
proof-
  let ?r' = "bsqr r"
  have Well: "wo_rel r" using WELL wo_rel_def by blast
  hence Trans: "trans r" using wo_rel.TRANS by blast
  have Well': "Well_order ?r' \<and> wo_rel ?r'"
    using WELL bsqr_Well_order wo_rel_def by blast
      (*  *)
  have "D < Field ?r'" unfolding Field_bsqr using SUB .
  with OF obtain a1 and a2 where
    "(a1,a2) \<in> Field ?r'" and 1: "D = underS ?r' (a1,a2)"
    using Well' wo_rel.ofilter_underS_Field[of ?r' D] by auto
  hence 2: "{a1,a2} \<le> Field r" unfolding Field_bsqr by auto
  let ?m = "wo_rel.max2 r a1 a2"
  have "D \<le> (under r ?m) \<times> (under r ?m)"
  proof(unfold 1)
    {fix b1 b2
      let ?n = "wo_rel.max2 r b1 b2"
      assume "(b1,b2) \<in> underS ?r' (a1,a2)"
      hence 3: "((b1,b2),(a1,a2)) \<in> ?r'"
        unfolding underS_def by blast
      hence "(?n,?m) \<in> r" using WELL by (simp add: bsqr_max2)
      moreover
      {have "(b1,b2) \<in> Field ?r'" using 3 unfolding Field_def by auto
        hence "{b1,b2} \<le> Field r" unfolding Field_bsqr by auto
        hence "(b1,?n) \<in> r \<and> (b2,?n) \<in> r"
          using Well by (simp add: wo_rel.max2_greater)
      }
      ultimately have "(b1,?m) \<in> r \<and> (b2,?m) \<in> r"
        using Trans trans_def[of r] by blast
      hence "(b1,b2) \<in> (under r ?m) \<times> (under r ?m)" unfolding under_def by simp}
    thus "underS ?r' (a1,a2) \<le> (under r ?m) \<times> (under r ?m)" by auto
  qed
  moreover have "wo_rel.ofilter r (under r ?m)"
    using Well by (simp add: wo_rel.under_ofilter)
  moreover have "under r ?m < Field r"
    using NE under_Field[of r ?m] by blast
  ultimately show ?thesis by blast
qed

definition Func where
  "Func A B = {f . (\<forall> a \<in> A. f a \<in> B) \<and> (\<forall> a. a \<notin> A \<longrightarrow> f a = undefined)}"

lemma Func_empty:
  "Func {} B = {\<lambda>x. undefined}"
  unfolding Func_def by auto

lemma Func_elim:
  assumes "g \<in> Func A B" and "a \<in> A"
  shows "\<exists> b. b \<in> B \<and> g a = b"
  using assms unfolding Func_def by (cases "g a = undefined") auto

definition curr where
  "curr A f \<equiv> \<lambda> a. if a \<in> A then \<lambda>b. f (a,b) else undefined"

lemma curr_in:
  assumes f: "f \<in> Func (A \<times> B) C"
  shows "curr A f \<in> Func A (Func B C)"
  using assms unfolding curr_def Func_def by auto

lemma curr_inj:
  assumes "f1 \<in> Func (A \<times> B) C" and "f2 \<in> Func (A \<times> B) C"
  shows "curr A f1 = curr A f2 \<longleftrightarrow> f1 = f2"
proof safe
  assume c: "curr A f1 = curr A f2"
  show "f1 = f2"
  proof (rule ext, clarify)
    fix a b show "f1 (a, b) = f2 (a, b)"
    proof (cases "(a,b) \<in> A \<times> B")
      case False
      thus ?thesis using assms unfolding Func_def by auto
    next
      case True hence a: "a \<in> A" and b: "b \<in> B" by auto
      thus ?thesis
        using c unfolding curr_def fun_eq_iff by(elim allE[of _ a]) simp
    qed
  qed
qed

lemma curr_surj:
  assumes "g \<in> Func A (Func B C)"
  shows "\<exists> f \<in> Func (A \<times> B) C. curr A f = g"
proof
  let ?f = "\<lambda> ab. if fst ab \<in> A \<and> snd ab \<in> B then g (fst ab) (snd ab) else undefined"
  show "curr A ?f = g"
  proof (rule ext)
    fix a show "curr A ?f a = g a"
    proof (cases "a \<in> A")
      case False
      hence "g a = undefined" using assms unfolding Func_def by auto
      thus ?thesis unfolding curr_def using False by simp
    next
      case True
      obtain g1 where "g1 \<in> Func B C" and "g a = g1"
        using assms using Func_elim[OF assms True] by blast
      thus ?thesis using True unfolding Func_def curr_def by auto
    qed
  qed
  show "?f \<in> Func (A \<times> B) C" using assms unfolding Func_def mem_Collect_eq by auto
qed

lemma bij_betw_curr:
  "bij_betw (curr A) (Func (A \<times> B) C) (Func A (Func B C))"
  unfolding bij_betw_def inj_on_def 
  using curr_surj curr_in curr_inj by blast

definition Func_map where
  "Func_map B2 f1 f2 g b2 \<equiv> if b2 \<in> B2 then f1 (g (f2 b2)) else undefined"

lemma Func_map:
  assumes g: "g \<in> Func A2 A1" and f1: "f1 ` A1 \<subseteq> B1" and f2: "f2 ` B2 \<subseteq> A2"
  shows "Func_map B2 f1 f2 g \<in> Func B2 B1"
  using assms unfolding Func_def Func_map_def mem_Collect_eq by auto

lemma Func_non_emp:
  assumes "B \<noteq> {}"
  shows "Func A B \<noteq> {}"
proof-
  obtain b where b: "b \<in> B" using assms by auto
  hence "(\<lambda> a. if a \<in> A then b else undefined) \<in> Func A B" unfolding Func_def by auto
  thus ?thesis by blast
qed

lemma Func_is_emp:
  "Func A B = {} \<longleftrightarrow> A \<noteq> {} \<and> B = {}" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then show ?R
    using Func_empty Func_non_emp[of B A] by blast
next
  assume ?R
  then show ?L
    using Func_empty Func_non_emp[of B A] by (auto simp: Func_def)
qed

lemma Func_map_surj:
  assumes B1: "f1 ` A1 = B1" and A2: "inj_on f2 B2" "f2 ` B2 \<subseteq> A2"
    and B2A2: "B2 = {} \<Longrightarrow> A2 = {}"
  shows "Func B2 B1 = Func_map B2 f1 f2 ` Func A2 A1"
proof(cases "B2 = {}")
  case True
  thus ?thesis using B2A2 by (auto simp: Func_empty Func_map_def)
next
  case False note B2 = False
  show ?thesis
  proof safe
    fix h assume h: "h \<in> Func B2 B1"
    define j1 where "j1 = inv_into A1 f1"
    have "\<forall> a2 \<in> f2 ` B2. \<exists> b2. b2 \<in> B2 \<and> f2 b2 = a2" by blast
    then obtain k where k: "\<forall> a2 \<in> f2 ` B2. k a2 \<in> B2 \<and> f2 (k a2) = a2"
      by atomize_elim (rule bchoice)
    {fix b2 assume b2: "b2 \<in> B2"
      hence "f2 (k (f2 b2)) = f2 b2" using k A2(2) by auto
      moreover have "k (f2 b2) \<in> B2" using b2 A2(2) k by auto
      ultimately have "k (f2 b2) = b2" using b2 A2(1) unfolding inj_on_def by blast
    } note kk = this
    obtain b22 where b22: "b22 \<in> B2" using B2 by auto
    define j2 where [abs_def]: "j2 a2 = (if a2 \<in> f2 ` B2 then k a2 else b22)" for a2
    have j2A2: "j2 ` A2 \<subseteq> B2" unfolding j2_def using k b22 by auto
    have j2: "\<And> b2. b2 \<in> B2 \<Longrightarrow> j2 (f2 b2) = b2"
      using kk unfolding j2_def by auto
    define g where "g = Func_map A2 j1 j2 h"
    have "Func_map B2 f1 f2 g = h"
    proof (rule ext)
      fix b2 show "Func_map B2 f1 f2 g b2 = h b2"
      proof(cases "b2 \<in> B2")
        case True
        show ?thesis
        proof (cases "h b2 = undefined")
          case True
          hence b1: "h b2 \<in> f1 ` A1" using h \<open>b2 \<in> B2\<close> unfolding B1 Func_def by auto
          show ?thesis using A2 f_inv_into_f[OF b1]
            unfolding True g_def Func_map_def j1_def j2[OF \<open>b2 \<in> B2\<close>] by auto
        qed(insert A2 True j2[OF True] h B1, unfold j1_def g_def Func_def Func_map_def,
            auto intro: f_inv_into_f)
      qed(insert h, unfold Func_def Func_map_def, auto)
    qed
    moreover have "g \<in> Func A2 A1" unfolding g_def apply(rule Func_map[OF h])
      using j2A2 B1 A2 unfolding j1_def by (fast intro: inv_into_into)+
    ultimately show "h \<in> Func_map B2 f1 f2 ` Func A2 A1"
      unfolding Func_map_def[abs_def] by auto
  qed(use B1 Func_map[OF _ _ A2(2)] in auto)
qed

end
