(*  Title:      HOL/Library/Product_Order.thy
    Author:     Brian Huffman
*)

section {* Pointwise order on product types *}

theory Product_Order
imports Product_plus Conditionally_Complete_Lattices
begin

subsection {* Pointwise ordering *}

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
  by default auto


subsection {* Binary infimum and supremum *}

instantiation prod :: (inf, inf) inf
begin

definition
  "inf x y = (inf (fst x) (fst y), inf (snd x) (snd y))"

lemma inf_Pair_Pair [simp]: "inf (a, b) (c, d) = (inf a c, inf b d)"
  unfolding inf_prod_def by simp

lemma fst_inf [simp]: "fst (inf x y) = inf (fst x) (fst y)"
  unfolding inf_prod_def by simp

lemma snd_inf [simp]: "snd (inf x y) = inf (snd x) (snd y)"
  unfolding inf_prod_def by simp

instance proof qed
end

instance prod :: (semilattice_inf, semilattice_inf) semilattice_inf
  by default auto


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

instance proof qed
end

instance prod :: (semilattice_sup, semilattice_sup) semilattice_sup
  by default auto

instance prod :: (lattice, lattice) lattice ..

instance prod :: (distrib_lattice, distrib_lattice) distrib_lattice
  by default (auto simp add: sup_inf_distrib1)


subsection {* Top and bottom elements *}

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
  by default (auto simp add: top_prod_def)

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
  by default (auto simp add: bot_prod_def)

instance prod :: (bounded_lattice, bounded_lattice) bounded_lattice ..

instance prod :: (boolean_algebra, boolean_algebra) boolean_algebra
  by default (auto simp add: prod_eqI inf_compl_bot sup_compl_top diff_eq)


subsection {* Complete lattice operations *}

instantiation prod :: (Inf, Inf) Inf
begin

definition
  "Inf A = (INF x:A. fst x, INF x:A. snd x)"

instance proof qed
end

instantiation prod :: (Sup, Sup) Sup
begin

definition
  "Sup A = (SUP x:A. fst x, SUP x:A. snd x)"

instance proof qed
end

instance prod :: (conditionally_complete_lattice, conditionally_complete_lattice)
    conditionally_complete_lattice
  by default (force simp: less_eq_prod_def Inf_prod_def Sup_prod_def bdd_below_def bdd_above_def
    INF_def SUP_def simp del: Inf_image_eq Sup_image_eq intro!: cInf_lower cSup_upper cInf_greatest cSup_least)+

instance prod :: (complete_lattice, complete_lattice) complete_lattice
  by default (simp_all add: less_eq_prod_def Inf_prod_def Sup_prod_def
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
  unfolding SUP_def Sup_prod_def by (simp add: comp_def)

lemma INF_Pair: "(INF x:A. (f x, g x)) = (INF x:A. f x, INF x:A. g x)"
  unfolding INF_def Inf_prod_def by (simp add: comp_def)


text {* Alternative formulations for set infima and suprema over the product
of two complete lattices: *}

lemma INF_prod_alt_def:
  "INFIMUM A f = (INFIMUM A (fst o f), INFIMUM A (snd o f))"
  unfolding INF_def Inf_prod_def by simp

lemma SUP_prod_alt_def:
  "SUPREMUM A f = (SUPREMUM A (fst o f), SUPREMUM A (snd o f))"
  unfolding SUP_def Sup_prod_def by simp


subsection {* Complete distributive lattices *}

(* Contribution: Alessandro Coglio *)

instance prod ::
  (complete_distrib_lattice, complete_distrib_lattice) complete_distrib_lattice
proof
  case goal1 thus ?case
    by (auto simp: sup_prod_def Inf_prod_def INF_prod_alt_def sup_Inf sup_INF comp_def)
next
  case goal2 thus ?case
    by (auto simp: inf_prod_def Sup_prod_def SUP_prod_alt_def inf_Sup inf_SUP comp_def)
qed

end

