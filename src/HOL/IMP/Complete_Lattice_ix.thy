theory Complete_Lattice_ix
imports Main
begin

text{* A complete lattice is an ordered type where every set of elements has
a greatest lower (and thus also a leats upper) bound. Sets are the
prototypical complete lattice where the greatest lower bound is
intersection. Sometimes that set of all elements of a type is not a complete
lattice although all elements of the same shape form a complete lattice, for
example lists of the same length, where the list elements come from a
complete lattice. We will have exactly this situation with annotated
commands. This theory introduces a slightly generalised version of complete
lattices where elements have an ``index'' and only the set of elements with
the same index form a complete lattice; the type as a whole is a disjoint
union of complete lattices. Because sets are not types, this requires a
special treatment. *}

locale Complete_Lattice_ix =
fixes L :: "'i \<Rightarrow> 'a::order set"
and Glb :: "'i \<Rightarrow> 'a set \<Rightarrow> 'a"
assumes Glb_lower: "A \<subseteq> L i \<Longrightarrow> a \<in> A \<Longrightarrow> (Glb i A) \<le> a"
and Glb_greatest: "b : L i \<Longrightarrow> \<forall>a\<in>A. b \<le> a \<Longrightarrow> b \<le> (Glb i A)"
and Glb_in_L: "A \<subseteq> L i \<Longrightarrow> Glb i A : L i"
begin

definition lfp :: "'i \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"lfp i f = Glb i {a : L i. f a \<le> a}"

lemma index_lfp: "lfp i f : L i"
by(auto simp: lfp_def intro: Glb_in_L)

lemma lfp_lowerbound:
  "\<lbrakk> a : L i;  f a \<le> a \<rbrakk> \<Longrightarrow> lfp i f \<le> a"
by (auto simp add: lfp_def intro: Glb_lower)

lemma lfp_greatest:
  "\<lbrakk> a : L i;  \<And>u. \<lbrakk> u : L i; f u \<le> u\<rbrakk> \<Longrightarrow> a \<le> u \<rbrakk> \<Longrightarrow> a \<le> lfp i f"
by (auto simp add: lfp_def intro: Glb_greatest)

lemma lfp_unfold: assumes "\<And>x i. f x : L i \<longleftrightarrow> x : L i"
and mono: "mono f" shows "lfp i f = f (lfp i f)"
proof-
  note assms(1)[simp] index_lfp[simp]
  have 1: "f (lfp i f) \<le> lfp i f"
    apply(rule lfp_greatest)
    apply simp
    by (blast intro: lfp_lowerbound monoD[OF mono] order_trans)
  have "lfp i f \<le> f (lfp i f)"
    by (fastforce intro: 1 monoD[OF mono] lfp_lowerbound)
  with 1 show ?thesis by(blast intro: order_antisym)
qed

end

end
