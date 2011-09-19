(*  Title:      HOL/Library/Product_Lattice.thy
    Author:     Brian Huffman
*)

header {* Lattice operations on product types *}

theory Product_Lattice
imports "~~/src/HOL/Library/Product_plus"
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

instantiation prod :: (semilattice_inf, semilattice_inf) semilattice_inf
begin

definition
  "inf x y = (inf (fst x) (fst y), inf (snd x) (snd y))"

lemma inf_Pair_Pair [simp]: "inf (a, b) (c, d) = (inf a c, inf b d)"
  unfolding inf_prod_def by simp

lemma fst_inf [simp]: "fst (inf x y) = inf (fst x) (fst y)"
  unfolding inf_prod_def by simp

lemma snd_inf [simp]: "snd (inf x y) = inf (snd x) (snd y)"
  unfolding inf_prod_def by simp

instance
  by default auto

end

instantiation prod :: (semilattice_sup, semilattice_sup) semilattice_sup
begin

definition
  "sup x y = (sup (fst x) (fst y), sup (snd x) (snd y))"

lemma sup_Pair_Pair [simp]: "sup (a, b) (c, d) = (sup a c, sup b d)"
  unfolding sup_prod_def by simp

lemma fst_sup [simp]: "fst (sup x y) = sup (fst x) (fst y)"
  unfolding sup_prod_def by simp

lemma snd_sup [simp]: "snd (sup x y) = sup (snd x) (snd y)"
  unfolding sup_prod_def by simp

instance
  by default auto

end

instance prod :: (lattice, lattice) lattice ..

instance prod :: (distrib_lattice, distrib_lattice) distrib_lattice
  by default (auto simp add: sup_inf_distrib1)


subsection {* Top and bottom elements *}

instantiation prod :: (top, top) top
begin

definition
  "top = (top, top)"

lemma fst_top [simp]: "fst top = top"
  unfolding top_prod_def by simp

lemma snd_top [simp]: "snd top = top"
  unfolding top_prod_def by simp

lemma Pair_top_top: "(top, top) = top"
  unfolding top_prod_def by simp

instance
  by default (auto simp add: top_prod_def)

end

instantiation prod :: (bot, bot) bot
begin

definition
  "bot = (bot, bot)"

lemma fst_bot [simp]: "fst bot = bot"
  unfolding bot_prod_def by simp

lemma snd_bot [simp]: "snd bot = bot"
  unfolding bot_prod_def by simp

lemma Pair_bot_bot: "(bot, bot) = bot"
  unfolding bot_prod_def by simp

instance
  by default (auto simp add: bot_prod_def)

end

instance prod :: (bounded_lattice, bounded_lattice) bounded_lattice ..

instance prod :: (boolean_algebra, boolean_algebra) boolean_algebra
  by default (auto simp add: prod_eqI inf_compl_bot sup_compl_top diff_eq)


subsection {* Complete lattice operations *}

instantiation prod :: (complete_lattice, complete_lattice) complete_lattice
begin

definition
  "Sup A = (SUP x:A. fst x, SUP x:A. snd x)"

definition
  "Inf A = (INF x:A. fst x, INF x:A. snd x)"

instance
  by default (simp_all add: less_eq_prod_def Inf_prod_def Sup_prod_def
    INF_lower SUP_upper le_INF_iff SUP_le_iff)

end

lemma fst_Sup: "fst (Sup A) = (SUP x:A. fst x)"
  unfolding Sup_prod_def by simp

lemma snd_Sup: "snd (Sup A) = (SUP x:A. snd x)"
  unfolding Sup_prod_def by simp

lemma fst_Inf: "fst (Inf A) = (INF x:A. fst x)"
  unfolding Inf_prod_def by simp

lemma snd_Inf: "snd (Inf A) = (INF x:A. snd x)"
  unfolding Inf_prod_def by simp

lemma fst_SUP: "fst (SUP x:A. f x) = (SUP x:A. fst (f x))"
  by (simp add: SUP_def fst_Sup image_image)

lemma snd_SUP: "snd (SUP x:A. f x) = (SUP x:A. snd (f x))"
  by (simp add: SUP_def snd_Sup image_image)

lemma fst_INF: "fst (INF x:A. f x) = (INF x:A. fst (f x))"
  by (simp add: INF_def fst_Inf image_image)

lemma snd_INF: "snd (INF x:A. f x) = (INF x:A. snd (f x))"
  by (simp add: INF_def snd_Inf image_image)

lemma SUP_Pair: "(SUP x:A. (f x, g x)) = (SUP x:A. f x, SUP x:A. g x)"
  by (simp add: SUP_def Sup_prod_def image_image)

lemma INF_Pair: "(INF x:A. (f x, g x)) = (INF x:A. f x, INF x:A. g x)"
  by (simp add: INF_def Inf_prod_def image_image)

end
