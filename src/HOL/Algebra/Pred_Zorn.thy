theory Pred_Zorn
  imports HOL.Zorn

begin

(* ========== *)
lemma partial_order_onE:
  assumes "partial_order_on A r" shows "refl_on A r" and "trans r" and "antisym r"
  using assms unfolding partial_order_on_def preorder_on_def by auto
(* ========== *)

abbreviation rel_of :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set"
  where "rel_of P A \<equiv> { (a, b) \<in> A \<times> A. P a b }"

lemma Field_rel_of:
  assumes "refl_on A (rel_of P A)" shows "Field (rel_of P A) = A"
  using assms unfolding refl_on_def Field_def by auto

(* ========== *)
lemma Chains_rel_of:
  assumes "C \<in> Chains (rel_of P A)" shows "C \<subseteq> A"
  using assms unfolding Chains_def by auto
(* ========== *)

lemma partial_order_on_rel_ofI:
  assumes refl: "\<And>a. a \<in> A \<Longrightarrow> P a a"
    and trans: "\<And>a b c. \<lbrakk> a \<in> A; b \<in> A; c \<in> A \<rbrakk> \<Longrightarrow> P a b \<Longrightarrow> P b c \<Longrightarrow> P a c"
    and antisym: "\<And>a b. \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> P a b \<Longrightarrow> P b a \<Longrightarrow> a = b"
  shows "partial_order_on A (rel_of P A)"
proof -
  from refl have "refl_on A (rel_of P A)"
    unfolding refl_on_def by auto
  moreover have "trans (rel_of P A)" and "antisym (rel_of P A)"
    by (auto intro: transI dest: trans, auto intro: antisymI dest: antisym)
  ultimately show ?thesis
    unfolding partial_order_on_def preorder_on_def by simp
qed

lemma Partial_order_rel_ofI:
  assumes "partial_order_on A (rel_of P A)" shows "Partial_order (rel_of P A)"
  using assms unfolding Field_rel_of[OF partial_order_onE(1)[OF assms]] .

lemma predicate_Zorn:
  assumes "partial_order_on A (rel_of P A)"
    and "\<forall>C \<in> Chains (rel_of P A). \<exists>u \<in> A. \<forall>a \<in> C. P a u"
  shows "\<exists>m \<in> A. \<forall>a \<in> A. P m a \<longrightarrow> a = m"
proof -
  have "a \<in> A" if "a \<in> C" and "C \<in> Chains (rel_of P A)" for C a
    using that Chains_rel_of by auto
  moreover have "(a, u) \<in> rel_of P A" if "a \<in> A" and "u \<in> A" and "P a u" for a u
    using that by auto
  ultimately show ?thesis
    using Zorns_po_lemma[OF Partial_order_rel_ofI[OF assms(1)]] assms(2)
    unfolding Field_rel_of[OF partial_order_onE(1)[OF assms(1)]] by auto
qed

end