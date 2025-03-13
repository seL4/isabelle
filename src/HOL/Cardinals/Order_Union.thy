(*  Title:      HOL/Cardinals/Order_Union.thy
    Author:     Andrei Popescu, TU Muenchen

The ordinal-like sum of two orders with disjoint fields
*)

section \<open>Order Union\<close>

theory Order_Union
  imports Main
begin

definition Osum :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel"  (infix \<open>Osum\<close> 60) where
  "r Osum r' = r \<union> r' \<union> {(a, a'). a \<in> Field r \<and> a' \<in> Field r'}"

notation Osum  (infix \<open>\<union>o\<close> 60)

lemma Field_Osum: "Field (r \<union>o r') = Field r \<union> Field r'"
  unfolding Osum_def Field_def by blast

lemma Osum_wf:
  assumes FLD: "Field r Int Field r' = {}" and
    WF: "wf r" and WF': "wf r'"
  shows "wf (r Osum r')"
  unfolding wf_eq_minimal2 unfolding Field_Osum
proof(intro allI impI, elim conjE)
  fix A assume *: "A \<subseteq> Field r \<union> Field r'" and **: "A \<noteq> {}"
  obtain B where B_def: "B = A Int Field r" by blast
  show "\<exists>a\<in>A. \<forall>a'\<in>A. (a', a) \<notin> r \<union>o r'"
  proof(cases "B = {}")
    assume Case1: "B \<noteq> {}"
    hence "B \<noteq> {} \<and> B \<le> Field r" using B_def by auto
    then obtain a where 1: "a \<in> B" and 2: "\<forall>a1 \<in> B. (a1,a) \<notin> r"
      using WF unfolding wf_eq_minimal2 by blast
    hence 3: "a \<in> Field r \<and> a \<notin> Field r'" using B_def FLD by auto
        (*  *)
    have "\<forall>a1 \<in> A. (a1,a) \<notin> r Osum r'"
    proof(intro ballI)
      fix a1 assume **: "a1 \<in> A"
      {assume Case11: "a1 \<in> Field r"
        hence "(a1,a) \<notin> r" using B_def ** 2 by auto
        moreover
        have "(a1,a) \<notin> r'" using 3 by (auto simp add: Field_def)
        ultimately have "(a1,a) \<notin> r Osum r'"
          using 3 unfolding Osum_def by auto
      }
      moreover
      {assume Case12: "a1 \<notin> Field r"
        hence "(a1,a) \<notin> r" unfolding Field_def by auto
        moreover
        have "(a1,a) \<notin> r'" using 3 unfolding Field_def by auto
        ultimately have "(a1,a) \<notin> r Osum r'"
          using 3 unfolding Osum_def by auto
      }
      ultimately show "(a1,a) \<notin> r Osum r'" by blast
    qed
    thus ?thesis using 1 B_def by auto
  next
    assume Case2: "B = {}"
    hence 1: "A \<noteq> {} \<and> A \<le> Field r'" using * ** B_def by auto
    then obtain a' where 2: "a' \<in> A" and 3: "\<forall>a1' \<in> A. (a1',a') \<notin> r'"
      using WF' unfolding wf_eq_minimal2 by blast
    hence 4: "a' \<in> Field r' \<and> a' \<notin> Field r" using 1 FLD by blast
        (*  *)
    have "\<forall>a1' \<in> A. (a1',a') \<notin> r Osum r'"
    proof(unfold Osum_def, auto simp add: 3)
      fix a1' assume "(a1', a') \<in> r"
      thus False using 4 unfolding Field_def by blast
    next
      fix a1' assume "a1' \<in> A" and "a1' \<in> Field r"
      thus False using Case2 B_def by auto
    qed
    thus ?thesis using 2 by blast
  qed
qed

lemma Osum_Refl:
  assumes FLD: "Field r Int Field r' = {}" and
    REFL: "Refl r" and REFL': "Refl r'"
  shows "Refl (r Osum r')"
  using assms
  unfolding refl_on_def Field_Osum unfolding Osum_def by blast

lemma Osum_trans:
  assumes FLD: "Field r Int Field r' = {}" and
    TRANS: "trans r" and TRANS': "trans r'"
  shows "trans (r Osum r')"
  using assms unfolding Osum_def trans_def disjoint_iff Field_iff by blast

lemma Osum_Preorder:
  "\<lbrakk>Field r Int Field r' = {}; Preorder r; Preorder r'\<rbrakk> \<Longrightarrow> Preorder (r Osum r')"
  unfolding preorder_on_def using Osum_Refl Osum_trans Restr_Field by blast

lemma Osum_antisym:
  assumes FLD: "Field r Int Field r' = {}" and
    AN: "antisym r" and AN': "antisym r'"
  shows "antisym (r Osum r')"
  using assms by (auto simp: disjoint_iff antisym_def Osum_def Field_def)

lemma Osum_Partial_order:
  "\<lbrakk>Field r Int Field r' = {}; Partial_order r; Partial_order r'\<rbrakk> \<Longrightarrow>
 Partial_order (r Osum r')"
  unfolding partial_order_on_def using Osum_Preorder Osum_antisym by blast

lemma Osum_Total:
  assumes FLD: "Field r Int Field r' = {}" and
    TOT: "Total r" and TOT': "Total r'"
  shows "Total (r Osum r')"
  using assms
  unfolding total_on_def  Field_Osum unfolding Osum_def by blast

lemma Osum_Linear_order:
  "\<lbrakk>Field r Int Field r' = {}; Linear_order r; Linear_order r'\<rbrakk> \<Longrightarrow> Linear_order (r Osum r')"
  by (simp add: Osum_Partial_order Osum_Total linear_order_on_def)

lemma Osum_minus_Id1:
  assumes "r \<le> Id"
  shows "(r Osum r') - Id \<le> (r' - Id) \<union> (Field r \<times> Field r')"
using assms by (force simp: Osum_def)

lemma Osum_minus_Id2:
  assumes "r' \<le> Id"
  shows "(r Osum r') - Id \<le> (r - Id) \<union> (Field r \<times> Field r')"
using assms by (force simp: Osum_def)

lemma Osum_minus_Id:
  assumes TOT: "Total r" and TOT': "Total r'" and
    NID: "\<not> (r \<le> Id)" and NID': "\<not> (r' \<le> Id)"
  shows "(r Osum r') - Id \<le> (r - Id) Osum (r' - Id)"
  using assms Total_Id_Field by (force simp: Osum_def)

lemma wf_Int_Times:
  assumes "A Int B = {}"
  shows "wf(A \<times> B)"
  unfolding wf_def using assms by blast

lemma Osum_wf_Id:
  assumes TOT: "Total r" and TOT': "Total r'" and
    FLD: "Field r Int Field r' = {}" and
    WF: "wf(r - Id)" and WF': "wf(r' - Id)"
  shows "wf ((r Osum r') - Id)"
proof(cases "r \<le> Id \<or> r' \<le> Id")
  assume Case1: "\<not>(r \<le> Id \<or> r' \<le> Id)"
  have "Field(r - Id) Int Field(r' - Id) = {}"
    using Case1 FLD TOT TOT' Total_Id_Field by blast
  thus ?thesis
    by (meson Case1 Osum_minus_Id Osum_wf TOT TOT' WF WF' wf_subset)
next
  have 1: "wf(Field r \<times> Field r')"
    using FLD by (auto simp add: wf_Int_Times)
  assume Case2: "r \<le> Id \<or> r' \<le> Id"
  moreover
  {assume Case21: "r \<le> Id"
    hence "(r Osum r') - Id \<le> (r' - Id) \<union> (Field r \<times> Field r')"
      using Osum_minus_Id1[of r r'] by simp
    moreover
    {have "Domain(Field r \<times> Field r') Int Range(r' - Id) = {}"
        using FLD unfolding Field_def by blast
      hence "wf((r' - Id) \<union> (Field r \<times> Field r'))"
        using 1 WF' wf_Un[of "Field r \<times> Field r'" "r' - Id"]
        by (auto simp add: Un_commute)
    }
    ultimately have ?thesis using wf_subset by blast
  }
  moreover
  {assume Case22: "r' \<le> Id"
    hence "(r Osum r') - Id \<le> (r - Id) \<union> (Field r \<times> Field r')"
      using Osum_minus_Id2[of r' r] by simp
    moreover
    {have "Range(Field r \<times> Field r') Int Domain(r - Id) = {}"
        using FLD unfolding Field_def by blast
      hence "wf((r - Id) \<union> (Field r \<times> Field r'))"
        using 1 WF wf_Un[of "r - Id" "Field r \<times> Field r'"]
        by (auto simp add: Un_commute)
    }
    ultimately have ?thesis using wf_subset by blast
  }
  ultimately show ?thesis by blast
qed

lemma Osum_Well_order:
  assumes FLD: "Field r Int Field r' = {}" and
    WELL: "Well_order r" and WELL': "Well_order r'"
  shows "Well_order (r Osum r')"
proof-
  have "Total r \<and> Total r'" using WELL WELL'
    by (auto simp add: order_on_defs)
  thus ?thesis using assms unfolding well_order_on_def
    using Osum_Linear_order Osum_wf_Id by blast
qed

end
