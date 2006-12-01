(*  Title:      HOL/Lattices.thy
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header {* Abstract lattices *}

theory Lattices
imports Orderings
begin

subsection{* Lattices *}

text{* This theory of lattice locales only defines binary sup and inf
operations. The extension to finite sets is done in theory @{text
Finite_Set}. In the longer term it may be better to define arbitrary
sups and infs via @{text THE}. *}

locale lower_semilattice = partial_order +
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes inf_le1[simp]: "x \<sqinter> y \<sqsubseteq> x" and inf_le2[simp]: "x \<sqinter> y \<sqsubseteq> y"
  and inf_least: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"

locale upper_semilattice = partial_order +
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
  assumes sup_ge1[simp]: "x \<sqsubseteq> x \<squnion> y" and sup_ge2[simp]: "y \<sqsubseteq> x \<squnion> y"
  and sup_greatest: "y \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> y \<squnion> z \<sqsubseteq> x"

locale lattice = lower_semilattice + upper_semilattice

lemma (in lower_semilattice) inf_commute: "(x \<sqinter> y) = (y \<sqinter> x)"
by(blast intro: antisym inf_le1 inf_le2 inf_least)

lemma (in upper_semilattice) sup_commute: "(x \<squnion> y) = (y \<squnion> x)"
by(blast intro: antisym sup_ge1 sup_ge2 sup_greatest)

lemma (in lower_semilattice) inf_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
by(blast intro: antisym inf_le1 inf_le2 inf_least trans del:refl)

lemma (in upper_semilattice) sup_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
by(blast intro!: antisym sup_ge1 sup_ge2 intro: sup_greatest trans del:refl)

lemma (in lower_semilattice) inf_idem[simp]: "x \<sqinter> x = x"
by(blast intro: antisym inf_le1 inf_le2 inf_least refl)

lemma (in upper_semilattice) sup_idem[simp]: "x \<squnion> x = x"
by(blast intro: antisym sup_ge1 sup_ge2 sup_greatest refl)

lemma (in lower_semilattice) inf_left_idem[simp]: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
by (simp add: inf_assoc[symmetric])

lemma (in upper_semilattice) sup_left_idem[simp]: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
by (simp add: sup_assoc[symmetric])

lemma (in lattice) inf_sup_absorb: "x \<sqinter> (x \<squnion> y) = x"
by(blast intro: antisym inf_le1 inf_least sup_ge1)

lemma (in lattice) sup_inf_absorb: "x \<squnion> (x \<sqinter> y) = x"
by(blast intro: antisym sup_ge1 sup_greatest inf_le1)

lemma (in lower_semilattice) inf_absorb: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
by(blast intro: antisym inf_le1 inf_least refl)

lemma (in upper_semilattice) sup_absorb: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
by(blast intro: antisym sup_ge2 sup_greatest refl)


lemma (in lower_semilattice) less_eq_inf_conv [simp]:
 "x \<sqsubseteq> y \<sqinter> z = (x \<sqsubseteq> y \<and> x \<sqsubseteq> z)"
by(blast intro: antisym inf_le1 inf_le2 inf_least refl trans)

lemmas (in lower_semilattice) below_inf_conv = less_eq_inf_conv
  -- {* a duplicate for backward compatibility *}

lemma (in upper_semilattice) above_sup_conv[simp]:
 "x \<squnion> y \<sqsubseteq> z = (x \<sqsubseteq> z \<and> y \<sqsubseteq> z)"
by(blast intro: antisym sup_ge1 sup_ge2 sup_greatest refl trans)


text{* Towards distributivity: if you have one of them, you have them all. *}

lemma (in lattice) distrib_imp1:
assumes D: "!!x y z. x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
shows "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof-
  have "x \<squnion> (y \<sqinter> z) = (x \<squnion> (x \<sqinter> z)) \<squnion> (y \<sqinter> z)" by(simp add:sup_inf_absorb)
  also have "\<dots> = x \<squnion> (z \<sqinter> (x \<squnion> y))" by(simp add:D inf_commute sup_assoc)
  also have "\<dots> = ((x \<squnion> y) \<sqinter> x) \<squnion> ((x \<squnion> y) \<sqinter> z)"
    by(simp add:inf_sup_absorb inf_commute)
  also have "\<dots> = (x \<squnion> y) \<sqinter> (x \<squnion> z)" by(simp add:D)
  finally show ?thesis .
qed

lemma (in lattice) distrib_imp2:
assumes D: "!!x y z. x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
shows "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
proof-
  have "x \<sqinter> (y \<squnion> z) = (x \<sqinter> (x \<squnion> z)) \<sqinter> (y \<squnion> z)" by(simp add:inf_sup_absorb)
  also have "\<dots> = x \<sqinter> (z \<squnion> (x \<sqinter> y))" by(simp add:D sup_commute inf_assoc)
  also have "\<dots> = ((x \<sqinter> y) \<squnion> x) \<sqinter> ((x \<sqinter> y) \<squnion> z)"
    by(simp add:sup_inf_absorb sup_commute)
  also have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" by(simp add:D)
  finally show ?thesis .
qed

text{* A package of rewrite rules for deciding equivalence wrt ACI: *}

lemma (in lower_semilattice) inf_left_commute: "x \<sqinter> (y \<sqinter> z) = y \<sqinter> (x \<sqinter> z)"
proof -
  have "x \<sqinter> (y \<sqinter> z) = (y \<sqinter> z) \<sqinter> x" by (simp only: inf_commute)
  also have "... = y \<sqinter> (z \<sqinter> x)" by (simp only: inf_assoc)
  also have "z \<sqinter> x = x \<sqinter> z" by (simp only: inf_commute)
  finally(back_subst) show ?thesis .
qed

lemma (in upper_semilattice) sup_left_commute: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
proof -
  have "x \<squnion> (y \<squnion> z) = (y \<squnion> z) \<squnion> x" by (simp only: sup_commute)
  also have "... = y \<squnion> (z \<squnion> x)" by (simp only: sup_assoc)
  also have "z \<squnion> x = x \<squnion> z" by (simp only: sup_commute)
  finally(back_subst) show ?thesis .
qed

lemma (in lower_semilattice) inf_left_idem: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
proof -
  have "x \<sqinter> (x \<sqinter> y) = (x \<sqinter> x) \<sqinter> y" by(simp only:inf_assoc)
  also have "\<dots> = x \<sqinter> y" by(simp)
  finally show ?thesis .
qed

lemma (in upper_semilattice) sup_left_idem: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
proof -
  have "x \<squnion> (x \<squnion> y) = (x \<squnion> x) \<squnion> y" by(simp only:sup_assoc)
  also have "\<dots> = x \<squnion> y" by(simp)
  finally show ?thesis .
qed


lemmas (in lower_semilattice) inf_ACI =
 inf_commute inf_assoc inf_left_commute inf_left_idem

lemmas (in upper_semilattice) sup_ACI =
 sup_commute sup_assoc sup_left_commute sup_left_idem

lemmas (in lattice) ACI = inf_ACI sup_ACI


subsection{* Distributive lattices *}

locale distrib_lattice = lattice +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

lemma (in distrib_lattice) sup_inf_distrib2:
 "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
by(simp add:ACI sup_inf_distrib1)

lemma (in distrib_lattice) inf_sup_distrib1:
 "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
by(rule distrib_imp2[OF sup_inf_distrib1])

lemma (in distrib_lattice) inf_sup_distrib2:
 "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
by(simp add:ACI inf_sup_distrib1)

lemmas (in distrib_lattice) distrib =
  sup_inf_distrib1 sup_inf_distrib2 inf_sup_distrib1 inf_sup_distrib2


subsection {* min/max on linear orders as special case of inf/sup *}

interpretation min_max:
  distrib_lattice ["op \<le>" "op <" "min \<Colon> 'a\<Colon>linorder \<Rightarrow> 'a \<Rightarrow> 'a" "max"]
apply unfold_locales
apply (simp add: min_def linorder_not_le order_less_imp_le)
apply (simp add: min_def linorder_not_le order_less_imp_le)
apply (simp add: min_def linorder_not_le order_less_imp_le)
apply (simp add: max_def linorder_not_le order_less_imp_le)
apply (simp add: max_def linorder_not_le order_less_imp_le)
unfolding min_def max_def by auto

lemmas le_maxI1 = min_max.sup_ge1
lemmas le_maxI2 = min_max.sup_ge2
 
lemmas max_ac = min_max.sup_assoc min_max.sup_commute
               mk_left_commute[of max,OF min_max.sup_assoc min_max.sup_commute]

lemmas min_ac = min_max.inf_assoc min_max.inf_commute
               mk_left_commute[of min,OF min_max.inf_assoc min_max.inf_commute]

end
