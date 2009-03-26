(*  Title:      HOL/Lattices.thy
    Author:     Tobias Nipkow
*)

header {* Abstract lattices *}

theory Lattices
imports Orderings
begin

subsection {* Lattices *}

notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less  (infix "\<sqsubset>" 50)

class lower_semilattice = order +
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes inf_le1 [simp]: "x \<sqinter> y \<sqsubseteq> x"
  and inf_le2 [simp]: "x \<sqinter> y \<sqsubseteq> y"
  and inf_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"

class upper_semilattice = order +
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
  assumes sup_ge1 [simp]: "x \<sqsubseteq> x \<squnion> y"
  and sup_ge2 [simp]: "y \<sqsubseteq> x \<squnion> y"
  and sup_least: "y \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> y \<squnion> z \<sqsubseteq> x"
begin

text {* Dual lattice *}

lemma dual_lattice:
  "lower_semilattice (op \<ge>) (op >) sup"
by (rule lower_semilattice.intro, rule dual_order)
  (unfold_locales, simp_all add: sup_least)

end

class lattice = lower_semilattice + upper_semilattice


subsubsection {* Intro and elim rules*}

context lower_semilattice
begin

lemma le_infI1[intro]:
  assumes "a \<sqsubseteq> x"
  shows "a \<sqinter> b \<sqsubseteq> x"
proof (rule order_trans)
  from assms show "a \<sqsubseteq> x" .
  show "a \<sqinter> b \<sqsubseteq> a" by simp 
qed
lemmas (in -) [rule del] = le_infI1

lemma le_infI2[intro]:
  assumes "b \<sqsubseteq> x"
  shows "a \<sqinter> b \<sqsubseteq> x"
proof (rule order_trans)
  from assms show "b \<sqsubseteq> x" .
  show "a \<sqinter> b \<sqsubseteq> b" by simp
qed
lemmas (in -) [rule del] = le_infI2

lemma le_infI[intro!]: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<sqinter> b"
by(blast intro: inf_greatest)
lemmas (in -) [rule del] = le_infI

lemma le_infE [elim!]: "x \<sqsubseteq> a \<sqinter> b \<Longrightarrow> (x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans)
lemmas (in -) [rule del] = le_infE

lemma le_inf_iff [simp]:
  "x \<sqsubseteq> y \<sqinter> z = (x \<sqsubseteq> y \<and> x \<sqsubseteq> z)"
by blast

lemma le_iff_inf: "(x \<sqsubseteq> y) = (x \<sqinter> y = x)"
  by (blast intro: antisym dest: eq_iff [THEN iffD1])

lemma mono_inf:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>lower_semilattice"
  shows "mono f \<Longrightarrow> f (A \<sqinter> B) \<le> f A \<sqinter> f B"
  by (auto simp add: mono_def intro: Lattices.inf_greatest)

end

context upper_semilattice
begin

lemma le_supI1[intro]: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto
lemmas (in -) [rule del] = le_supI1

lemma le_supI2[intro]: "x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto 
lemmas (in -) [rule del] = le_supI2

lemma le_supI[intro!]: "a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> a \<squnion> b \<sqsubseteq> x"
  by (blast intro: sup_least)
lemmas (in -) [rule del] = le_supI

lemma le_supE[elim!]: "a \<squnion> b \<sqsubseteq> x \<Longrightarrow> (a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans)
lemmas (in -) [rule del] = le_supE

lemma ge_sup_conv[simp]:
  "x \<squnion> y \<sqsubseteq> z = (x \<sqsubseteq> z \<and> y \<sqsubseteq> z)"
by blast

lemma le_iff_sup: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
  by (blast intro: antisym dest: eq_iff [THEN iffD1])

lemma mono_sup:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>upper_semilattice"
  shows "mono f \<Longrightarrow> f A \<squnion> f B \<le> f (A \<squnion> B)"
  by (auto simp add: mono_def intro: Lattices.sup_least)

end


subsubsection{* Equational laws *}

context lower_semilattice
begin

lemma inf_commute: "(x \<sqinter> y) = (y \<sqinter> x)"
  by (blast intro: antisym)

lemma inf_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  by (blast intro: antisym)

lemma inf_idem[simp]: "x \<sqinter> x = x"
  by (blast intro: antisym)

lemma inf_left_idem[simp]: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
  by (blast intro: antisym)

lemma inf_absorb1: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
  by (blast intro: antisym)

lemma inf_absorb2: "y \<sqsubseteq> x \<Longrightarrow> x \<sqinter> y = y"
  by (blast intro: antisym)

lemma inf_left_commute: "x \<sqinter> (y \<sqinter> z) = y \<sqinter> (x \<sqinter> z)"
  by (blast intro: antisym)

lemmas inf_ACI = inf_commute inf_assoc inf_left_commute inf_left_idem

end


context upper_semilattice
begin

lemma sup_commute: "(x \<squnion> y) = (y \<squnion> x)"
  by (blast intro: antisym)

lemma sup_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  by (blast intro: antisym)

lemma sup_idem[simp]: "x \<squnion> x = x"
  by (blast intro: antisym)

lemma sup_left_idem[simp]: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
  by (blast intro: antisym)

lemma sup_absorb1: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
  by (blast intro: antisym)

lemma sup_absorb2: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
  by (blast intro: antisym)

lemma sup_left_commute: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
  by (blast intro: antisym)

lemmas sup_ACI = sup_commute sup_assoc sup_left_commute sup_left_idem

end

context lattice
begin

lemma inf_sup_absorb: "x \<sqinter> (x \<squnion> y) = x"
  by (blast intro: antisym inf_le1 inf_greatest sup_ge1)

lemma sup_inf_absorb: "x \<squnion> (x \<sqinter> y) = x"
  by (blast intro: antisym sup_ge1 sup_least inf_le1)

lemmas ACI = inf_ACI sup_ACI

lemmas inf_sup_ord = inf_le1 inf_le2 sup_ge1 sup_ge2

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


subsection {* Distributive lattices *}

class distrib_lattice = lattice +
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


subsection {* Uniqueness of inf and sup *}

lemma (in lower_semilattice) inf_unique:
  fixes f (infixl "\<triangle>" 70)
  assumes le1: "\<And>x y. x \<triangle> y \<le> x" and le2: "\<And>x y. x \<triangle> y \<le> y"
  and greatest: "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<triangle> z"
  shows "x \<sqinter> y = x \<triangle> y"
proof (rule antisym)
  show "x \<triangle> y \<le> x \<sqinter> y" by (rule le_infI) (rule le1, rule le2)
next
  have leI: "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<triangle> z" by (blast intro: greatest)
  show "x \<sqinter> y \<le> x \<triangle> y" by (rule leI) simp_all
qed

lemma (in upper_semilattice) sup_unique:
  fixes f (infixl "\<nabla>" 70)
  assumes ge1 [simp]: "\<And>x y. x \<le> x \<nabla> y" and ge2: "\<And>x y. y \<le> x \<nabla> y"
  and least: "\<And>x y z. y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<nabla> z \<le> x"
  shows "x \<squnion> y = x \<nabla> y"
proof (rule antisym)
  show "x \<squnion> y \<le> x \<nabla> y" by (rule le_supI) (rule ge1, rule ge2)
next
  have leI: "\<And>x y z. x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x \<nabla> y \<le> z" by (blast intro: least)
  show "x \<nabla> y \<le> x \<squnion> y" by (rule leI) simp_all
qed
  

subsection {* @{const min}/@{const max} on linear orders as
  special case of @{const inf}/@{const sup} *}

lemma (in linorder) distrib_lattice_min_max:
  "distrib_lattice (op \<le>) (op <) min max"
proof
  have aux: "\<And>x y \<Colon> 'a. x < y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp add: less_le antisym)
  fix x y z
  show "max x (min y z) = min (max x y) (max x z)"
  unfolding min_def max_def
  by auto
qed (auto simp add: min_def max_def not_le less_imp_le)

interpretation min_max: distrib_lattice "op \<le> :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" min max
  by (rule distrib_lattice_min_max)

lemma inf_min: "inf = (min \<Colon> 'a\<Colon>{lower_semilattice, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (rule ext)+ (auto intro: antisym)

lemma sup_max: "sup = (max \<Colon> 'a\<Colon>{upper_semilattice, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (rule ext)+ (auto intro: antisym)

lemmas le_maxI1 = min_max.sup_ge1
lemmas le_maxI2 = min_max.sup_ge2
 
lemmas max_ac = min_max.sup_assoc min_max.sup_commute
  mk_left_commute [of max, OF min_max.sup_assoc min_max.sup_commute]

lemmas min_ac = min_max.inf_assoc min_max.inf_commute
  mk_left_commute [of min, OF min_max.inf_assoc min_max.inf_commute]

text {*
  Now we have inherited antisymmetry as an intro-rule on all
  linear orders. This is a problem because it applies to bool, which is
  undesirable.
*}

lemmas [rule del] = min_max.le_infI min_max.le_supI
  min_max.le_supE min_max.le_infE min_max.le_supI1 min_max.le_supI2
  min_max.le_infI1 min_max.le_infI2


subsection {* Bool as lattice *}

instantiation bool :: distrib_lattice
begin

definition
  inf_bool_eq: "P \<sqinter> Q \<longleftrightarrow> P \<and> Q"

definition
  sup_bool_eq: "P \<squnion> Q \<longleftrightarrow> P \<or> Q"

instance
  by intro_classes (auto simp add: inf_bool_eq sup_bool_eq le_bool_def)

end


subsection {* Fun as lattice *}

instantiation "fun" :: (type, lattice) lattice
begin

definition
  inf_fun_eq [code del]: "f \<sqinter> g = (\<lambda>x. f x \<sqinter> g x)"

definition
  sup_fun_eq [code del]: "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"

instance
apply intro_classes
unfolding inf_fun_eq sup_fun_eq
apply (auto intro: le_funI)
apply (rule le_funI)
apply (auto dest: le_funD)
apply (rule le_funI)
apply (auto dest: le_funD)
done

end

instance "fun" :: (type, distrib_lattice) distrib_lattice
  by default (auto simp add: inf_fun_eq sup_fun_eq sup_inf_distrib1)


text {* redundant bindings *}

lemmas inf_aci = inf_ACI
lemmas sup_aci = sup_ACI

no_notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

end
