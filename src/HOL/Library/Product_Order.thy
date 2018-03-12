(*  Title:      HOL/Library/Product_Order.thy
    Author:     Brian Huffman
*)

section \<open>Pointwise order on product types\<close>

theory Product_Order
imports Product_Plus
begin

subsection \<open>Pointwise ordering\<close>

instantiation prod :: (ord, ord) ord
begin

definition
  "x \<le> y \<longleftrightarrow> fst x \<le> fst y \<and> snd x \<le> snd y"

definition
  "(x::'a \<times> 'b) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..

end

lemma fst_mono: "x \<le> y \<Longrightarrow> fst x \<le> fst y"
  unfolding less_eq_prod_def by simp

lemma snd_mono: "x \<le> y \<Longrightarrow> snd x \<le> snd y"
  unfolding less_eq_prod_def by simp

lemma Pair_mono: "x \<le> x' \<Longrightarrow> y \<le> y' \<Longrightarrow> (x, y) \<le> (x', y')"
  unfolding less_eq_prod_def by simp

lemma Pair_le [simp]: "(a, b) \<le> (c, d) \<longleftrightarrow> a \<le> c \<and> b \<le> d"
  unfolding less_eq_prod_def by simp

instance prod :: (preorder, preorder) preorder
proof
  fix x y z :: "'a \<times> 'b"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_prod_def)
  show "x \<le> x"
    unfolding less_eq_prod_def
    by fast
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    unfolding less_eq_prod_def
    by (fast elim: order_trans)
qed

instance prod :: (order, order) order
  by standard auto


subsection \<open>Binary infimum and supremum\<close>

instantiation prod :: (inf, inf) inf
begin

definition "inf x y = (inf (fst x) (fst y), inf (snd x) (snd y))"

lemma inf_Pair_Pair [simp]: "inf (a, b) (c, d) = (inf a c, inf b d)"
  unfolding inf_prod_def by simp

lemma fst_inf [simp]: "fst (inf x y) = inf (fst x) (fst y)"
  unfolding inf_prod_def by simp

lemma snd_inf [simp]: "snd (inf x y) = inf (snd x) (snd y)"
  unfolding inf_prod_def by simp

instance ..

end

instance prod :: (semilattice_inf, semilattice_inf) semilattice_inf
  by standard auto


instantiation prod :: (sup, sup) sup
begin

definition
  "sup x y = (sup (fst x) (fst y), sup (snd x) (snd y))"

lemma sup_Pair_Pair [simp]: "sup (a, b) (c, d) = (sup a c, sup b d)"
  unfolding sup_prod_def by simp

lemma fst_sup [simp]: "fst (sup x y) = sup (fst x) (fst y)"
  unfolding sup_prod_def by simp

lemma snd_sup [simp]: "snd (sup x y) = sup (snd x) (snd y)"
  unfolding sup_prod_def by simp

instance ..

end

instance prod :: (semilattice_sup, semilattice_sup) semilattice_sup
  by standard auto

instance prod :: (lattice, lattice) lattice ..

instance prod :: (distrib_lattice, distrib_lattice) distrib_lattice
  by standard (auto simp add: sup_inf_distrib1)


subsection \<open>Top and bottom elements\<close>

instantiation prod :: (top, top) top
begin

definition
  "top = (top, top)"

instance ..

end

lemma fst_top [simp]: "fst top = top"
  unfolding top_prod_def by simp

lemma snd_top [simp]: "snd top = top"
  unfolding top_prod_def by simp

lemma Pair_top_top: "(top, top) = top"
  unfolding top_prod_def by simp

instance prod :: (order_top, order_top) order_top
  by standard (auto simp add: top_prod_def)

instantiation prod :: (bot, bot) bot
begin

definition
  "bot = (bot, bot)"

instance ..

end

lemma fst_bot [simp]: "fst bot = bot"
  unfolding bot_prod_def by simp

lemma snd_bot [simp]: "snd bot = bot"
  unfolding bot_prod_def by simp

lemma Pair_bot_bot: "(bot, bot) = bot"
  unfolding bot_prod_def by simp

instance prod :: (order_bot, order_bot) order_bot
  by standard (auto simp add: bot_prod_def)

instance prod :: (bounded_lattice, bounded_lattice) bounded_lattice ..

instance prod :: (boolean_algebra, boolean_algebra) boolean_algebra
  by standard (auto simp add: prod_eqI diff_eq)


subsection \<open>Complete lattice operations\<close>

instantiation prod :: (Inf, Inf) Inf
begin

definition "Inf A = (INF x:A. fst x, INF x:A. snd x)"

instance ..

end

instantiation prod :: (Sup, Sup) Sup
begin

definition "Sup A = (SUP x:A. fst x, SUP x:A. snd x)"

instance ..

end

instance prod :: (conditionally_complete_lattice, conditionally_complete_lattice)
    conditionally_complete_lattice
  by standard (force simp: less_eq_prod_def Inf_prod_def Sup_prod_def bdd_below_def bdd_above_def
    intro!: cInf_lower cSup_upper cInf_greatest cSup_least)+

instance prod :: (complete_lattice, complete_lattice) complete_lattice
  by standard (simp_all add: less_eq_prod_def Inf_prod_def Sup_prod_def
    INF_lower SUP_upper le_INF_iff SUP_le_iff bot_prod_def top_prod_def)

lemma fst_Sup: "fst (Sup A) = (SUP x:A. fst x)"
  unfolding Sup_prod_def by simp

lemma snd_Sup: "snd (Sup A) = (SUP x:A. snd x)"
  unfolding Sup_prod_def by simp

lemma fst_Inf: "fst (Inf A) = (INF x:A. fst x)"
  unfolding Inf_prod_def by simp

lemma snd_Inf: "snd (Inf A) = (INF x:A. snd x)"
  unfolding Inf_prod_def by simp

lemma fst_SUP: "fst (SUP x:A. f x) = (SUP x:A. fst (f x))"
  using fst_Sup [of "f ` A", symmetric] by (simp add: comp_def)

lemma snd_SUP: "snd (SUP x:A. f x) = (SUP x:A. snd (f x))"
  using snd_Sup [of "f ` A", symmetric] by (simp add: comp_def)

lemma fst_INF: "fst (INF x:A. f x) = (INF x:A. fst (f x))"
  using fst_Inf [of "f ` A", symmetric] by (simp add: comp_def)

lemma snd_INF: "snd (INF x:A. f x) = (INF x:A. snd (f x))"
  using snd_Inf [of "f ` A", symmetric] by (simp add: comp_def)

lemma SUP_Pair: "(SUP x:A. (f x, g x)) = (SUP x:A. f x, SUP x:A. g x)"
  unfolding Sup_prod_def by (simp add: comp_def)

lemma INF_Pair: "(INF x:A. (f x, g x)) = (INF x:A. f x, INF x:A. g x)"
  unfolding Inf_prod_def by (simp add: comp_def)


text \<open>Alternative formulations for set infima and suprema over the product
of two complete lattices:\<close>

lemma INF_prod_alt_def:
  "INFIMUM A f = (INFIMUM A (fst \<circ> f), INFIMUM A (snd \<circ> f))"
  unfolding Inf_prod_def by simp

lemma SUP_prod_alt_def:
  "SUPREMUM A f = (SUPREMUM A (fst \<circ> f), SUPREMUM A (snd \<circ> f))"
  unfolding Sup_prod_def by simp


subsection \<open>Complete distributive lattices\<close>

(* Contribution: Alessandro Coglio *)

instance prod :: (complete_distrib_lattice, complete_distrib_lattice) complete_distrib_lattice
proof
  fix A::"('a\<times>'b) set set"
  show "INFIMUM A Sup \<le> SUPREMUM {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y} Inf"
    by (simp add: Sup_prod_def Inf_prod_def INF_SUP_set)
qed

subsection \<open>Bekic's Theorem\<close>
text \<open>
  Simultaneous fixed points over pairs can be written in terms of separate fixed points.
  Transliterated from HOLCF.Fix by Peter Gammie
\<close>

lemma lfp_prod:
  fixes F :: "'a::complete_lattice \<times> 'b::complete_lattice \<Rightarrow> 'a \<times> 'b"
  assumes "mono F"
  shows "lfp F = (lfp (\<lambda>x. fst (F (x, lfp (\<lambda>y. snd (F (x, y)))))),
                 (lfp (\<lambda>y. snd (F (lfp (\<lambda>x. fst (F (x, lfp (\<lambda>y. snd (F (x, y)))))), y)))))"
  (is "lfp F = (?x, ?y)")
proof(rule lfp_eqI[OF assms])
  have 1: "fst (F (?x, ?y)) = ?x"
    by (rule trans [symmetric, OF lfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono lfp_mono)+
  have 2: "snd (F (?x, ?y)) = ?y"
    by (rule trans [symmetric, OF lfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono lfp_mono)+
  from 1 2 show "F (?x, ?y) = (?x, ?y)" by (simp add: prod_eq_iff)
next
  fix z assume F_z: "F z = z"
  obtain x y where z: "z = (x, y)" by (rule prod.exhaust)
  from F_z z have F_x: "fst (F (x, y)) = x" by simp
  from F_z z have F_y: "snd (F (x, y)) = y" by simp
  let ?y1 = "lfp (\<lambda>y. snd (F (x, y)))"
  have "?y1 \<le> y" by (rule lfp_lowerbound, simp add: F_y)
  hence "fst (F (x, ?y1)) \<le> fst (F (x, y))"
    by (simp add: assms fst_mono monoD)
  hence "fst (F (x, ?y1)) \<le> x" using F_x by simp
  hence 1: "?x \<le> x" by (simp add: lfp_lowerbound)
  hence "snd (F (?x, y)) \<le> snd (F (x, y))"
    by (simp add: assms snd_mono monoD)
  hence "snd (F (?x, y)) \<le> y" using F_y by simp
  hence 2: "?y \<le> y" by (simp add: lfp_lowerbound)
  show "(?x, ?y) \<le> z" using z 1 2 by simp
qed

lemma gfp_prod:
  fixes F :: "'a::complete_lattice \<times> 'b::complete_lattice \<Rightarrow> 'a \<times> 'b"
  assumes "mono F"
  shows "gfp F = (gfp (\<lambda>x. fst (F (x, gfp (\<lambda>y. snd (F (x, y)))))),
                 (gfp (\<lambda>y. snd (F (gfp (\<lambda>x. fst (F (x, gfp (\<lambda>y. snd (F (x, y)))))), y)))))"
  (is "gfp F = (?x, ?y)")
proof(rule gfp_eqI[OF assms])
  have 1: "fst (F (?x, ?y)) = ?x"
    by (rule trans [symmetric, OF gfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono gfp_mono)+
  have 2: "snd (F (?x, ?y)) = ?y"
    by (rule trans [symmetric, OF gfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono gfp_mono)+
  from 1 2 show "F (?x, ?y) = (?x, ?y)" by (simp add: prod_eq_iff)
next
  fix z assume F_z: "F z = z"
  obtain x y where z: "z = (x, y)" by (rule prod.exhaust)
  from F_z z have F_x: "fst (F (x, y)) = x" by simp
  from F_z z have F_y: "snd (F (x, y)) = y" by simp
  let ?y1 = "gfp (\<lambda>y. snd (F (x, y)))"
  have "y \<le> ?y1" by (rule gfp_upperbound, simp add: F_y)
  hence "fst (F (x, y)) \<le> fst (F (x, ?y1))"
    by (simp add: assms fst_mono monoD)
  hence "x \<le> fst (F (x, ?y1))" using F_x by simp
  hence 1: "x \<le> ?x" by (simp add: gfp_upperbound)
  hence "snd (F (x, y)) \<le> snd (F (?x, y))"
    by (simp add: assms snd_mono monoD)
  hence "y \<le> snd (F (?x, y))" using F_y by simp
  hence 2: "y \<le> ?y" by (simp add: gfp_upperbound)
  show "z \<le> (?x, ?y)" using z 1 2 by simp
qed

end
