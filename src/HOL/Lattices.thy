(*  Title:      HOL/Lattices.thy
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header {* Lattices via Locales *}

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
  and inf_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"

locale upper_semilattice = partial_order +
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
  assumes sup_ge1[simp]: "x \<sqsubseteq> x \<squnion> y" and sup_ge2[simp]: "y \<sqsubseteq> x \<squnion> y"
  and sup_least: "y \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> y \<squnion> z \<sqsubseteq> x"

locale lattice = lower_semilattice + upper_semilattice

subsubsection{* Intro and elim rules*}

context lower_semilattice
begin

lemmas antisym_intro[intro!] = antisym

lemma le_infI1[intro]: "a \<sqsubseteq> x \<Longrightarrow> a \<sqinter> b \<sqsubseteq> x"
apply(subgoal_tac "a \<sqinter> b \<sqsubseteq> a")
 apply(blast intro:trans)
apply simp
done

lemma le_infI2[intro]: "b \<sqsubseteq> x \<Longrightarrow> a \<sqinter> b \<sqsubseteq> x"
apply(subgoal_tac "a \<sqinter> b \<sqsubseteq> b")
 apply(blast intro:trans)
apply simp
done

lemma le_infI[intro!]: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<sqinter> b"
by(blast intro: inf_greatest)

lemma le_infE[elim!]: "x \<sqsubseteq> a \<sqinter> b \<Longrightarrow> (x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> P) \<Longrightarrow> P"
by(blast intro: trans)

lemma le_inf_iff [simp]:
 "x \<sqsubseteq> y \<sqinter> z = (x \<sqsubseteq> y \<and> x \<sqsubseteq> z)"
by blast

lemma le_iff_inf: "(x \<sqsubseteq> y) = (x \<sqinter> y = x)"
apply rule
 apply(simp add: antisym)
apply(subgoal_tac "x \<sqinter> y \<sqsubseteq> y")
 apply(simp)
apply(simp (no_asm))
done

end


context upper_semilattice
begin

lemmas antisym_intro[intro!] = antisym

lemma le_supI1[intro]: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
apply(subgoal_tac "a \<sqsubseteq> a \<squnion> b")
 apply(blast intro:trans)
apply simp
done

lemma le_supI2[intro]: "x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
apply(subgoal_tac "b \<sqsubseteq> a \<squnion> b")
 apply(blast intro:trans)
apply simp
done

lemma le_supI[intro!]: "a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> a \<squnion> b \<sqsubseteq> x"
by(blast intro: sup_least)

lemma le_supE[elim!]: "a \<squnion> b \<sqsubseteq> x \<Longrightarrow> (a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> P) \<Longrightarrow> P"
by(blast intro: trans)

lemma ge_sup_conv[simp]:
 "x \<squnion> y \<sqsubseteq> z = (x \<sqsubseteq> z \<and> y \<sqsubseteq> z)"
by blast

lemma le_iff_sup: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
apply rule
 apply(simp add: antisym)
apply(subgoal_tac "x \<sqsubseteq> x \<squnion> y")
apply(simp)
 apply(simp (no_asm))
done

end


subsubsection{* Equational laws *}


context lower_semilattice
begin

lemma inf_commute: "(x \<sqinter> y) = (y \<sqinter> x)"
by blast

lemma inf_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
by blast

lemma inf_idem[simp]: "x \<sqinter> x = x"
by blast

lemma inf_left_idem[simp]: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
by blast

lemma inf_absorb1: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
by blast

lemma inf_absorb2: "y \<sqsubseteq> x \<Longrightarrow> x \<sqinter> y = y"
by blast

lemma inf_left_commute: "x \<sqinter> (y \<sqinter> z) = y \<sqinter> (x \<sqinter> z)"
by blast

lemmas inf_ACI = inf_commute inf_assoc inf_left_commute inf_left_idem

end


context upper_semilattice
begin

lemma sup_commute: "(x \<squnion> y) = (y \<squnion> x)"
by blast

lemma sup_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
by blast

lemma sup_idem[simp]: "x \<squnion> x = x"
by blast

lemma sup_left_idem[simp]: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
by blast

lemma sup_absorb1: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
by blast

lemma sup_absorb2: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
by blast

lemma sup_left_commute: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
by blast

lemmas sup_ACI = sup_commute sup_assoc sup_left_commute sup_left_idem

end

context lattice
begin

lemma inf_sup_absorb: "x \<sqinter> (x \<squnion> y) = x"
by(blast intro: antisym inf_le1 inf_greatest sup_ge1)

lemma sup_inf_absorb: "x \<squnion> (x \<sqinter> y) = x"
by(blast intro: antisym sup_ge1 sup_least inf_le1)

lemmas ACI = inf_ACI sup_ACI

text{* Towards distributivity *}

lemma distrib_sup_le: "x \<squnion> (y \<sqinter> z) \<sqsubseteq> (x \<squnion> y) \<sqinter> (x \<squnion> z)"
by blast

lemma distrib_inf_le: "(x \<sqinter> y) \<squnion> (x \<sqinter> z) \<sqsubseteq> x \<sqinter> (y \<squnion> z)"
by blast


text{* If you have one of them, you have them all. *}

lemma distrib_imp1:
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

lemma distrib_imp2:
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

(* seems unused *)
lemma modular_le: "x \<sqsubseteq> z \<Longrightarrow> x \<squnion> (y \<sqinter> z) \<sqsubseteq> (x \<squnion> y) \<sqinter> z"
by blast

end


subsection{* Distributive lattices *}

locale distrib_lattice = lattice +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

context distrib_lattice
begin

lemma sup_inf_distrib2:
 "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
by(simp add:ACI sup_inf_distrib1)

lemma inf_sup_distrib1:
 "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
by(rule distrib_imp2[OF sup_inf_distrib1])

lemma inf_sup_distrib2:
 "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
by(simp add:ACI inf_sup_distrib1)

lemmas distrib =
  sup_inf_distrib1 sup_inf_distrib2 inf_sup_distrib1 inf_sup_distrib2

end


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

text{* Now we have inherited antisymmetry as an intro-rule on all
linear orders. This is a problem because it applies to bool, which is
undesirable. *}

declare
 min_max.antisym_intro[rule del]
 min_max.le_infI[rule del] min_max.le_supI[rule del]
 min_max.le_supE[rule del] min_max.le_infE[rule del]
 min_max.le_supI1[rule del] min_max.le_supI2[rule del]
 min_max.le_infI1[rule del] min_max.le_infI2[rule del]

lemmas le_maxI1 = min_max.sup_ge1
lemmas le_maxI2 = min_max.sup_ge2
 
lemmas max_ac = min_max.sup_assoc min_max.sup_commute
               mk_left_commute[of max,OF min_max.sup_assoc min_max.sup_commute]

lemmas min_ac = min_max.inf_assoc min_max.inf_commute
               mk_left_commute[of min,OF min_max.inf_assoc min_max.inf_commute]

text {* ML legacy bindings *}

ML {*
val Least_def = thm "Least_def";
val Least_equality = thm "Least_equality";
val min_def = thm "min_def";
val min_of_mono = thm "min_of_mono";
val max_def = thm "max_def";
val max_of_mono = thm "max_of_mono";
val min_leastL = thm "min_leastL";
val max_leastL = thm "max_leastL";
val min_leastR = thm "min_leastR";
val max_leastR = thm "max_leastR";
val le_max_iff_disj = thm "le_max_iff_disj";
val le_maxI1 = thm "le_maxI1";
val le_maxI2 = thm "le_maxI2";
val less_max_iff_disj = thm "less_max_iff_disj";
val max_less_iff_conj = thm "max_less_iff_conj";
val min_less_iff_conj = thm "min_less_iff_conj";
val min_le_iff_disj = thm "min_le_iff_disj";
val min_less_iff_disj = thm "min_less_iff_disj";
val split_min = thm "split_min";
val split_max = thm "split_max";
*}

end
