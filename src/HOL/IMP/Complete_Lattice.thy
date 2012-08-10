theory Complete_Lattice
imports Main
begin

locale Complete_Lattice =
fixes L :: "'a::order set" and Glb :: "'a set \<Rightarrow> 'a"
assumes Glb_lower: "A \<subseteq> L \<Longrightarrow> a \<in> A \<Longrightarrow> Glb A \<le> a"
and Glb_greatest: "b : L \<Longrightarrow> \<forall>a\<in>A. b \<le> a \<Longrightarrow> b \<le> Glb A"
and Glb_in_L: "A \<subseteq> L \<Longrightarrow> Glb A : L"
begin

definition lfp :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"lfp f = Glb {a : L. f a \<le> a}"

lemma index_lfp: "lfp f : L"
by(auto simp: lfp_def intro: Glb_in_L)

lemma lfp_lowerbound:
  "\<lbrakk> a : L;  f a \<le> a \<rbrakk> \<Longrightarrow> lfp f \<le> a"
by (auto simp add: lfp_def intro: Glb_lower)

lemma lfp_greatest:
  "\<lbrakk> a : L;  \<And>u. \<lbrakk> u : L; f u \<le> u\<rbrakk> \<Longrightarrow> a \<le> u \<rbrakk> \<Longrightarrow> a \<le> lfp f"
by (auto simp add: lfp_def intro: Glb_greatest)

lemma lfp_unfold: assumes "\<And>x. f x : L \<longleftrightarrow> x : L"
and mono: "mono f" shows "lfp f = f (lfp f)"
proof-
  note assms(1)[simp] index_lfp[simp]
  have 1: "f (lfp f) \<le> lfp f"
    apply(rule lfp_greatest)
    apply simp
    by (blast intro: lfp_lowerbound monoD[OF mono] order_trans)
  have "lfp f \<le> f (lfp f)"
    by (fastforce intro: 1 monoD[OF mono] lfp_lowerbound)
  with 1 show ?thesis by(blast intro: order_antisym)
qed

end

end

