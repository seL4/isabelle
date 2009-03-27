(*  Title:      HOL/Library/Product_ord.thy
    Author:     Norbert Voelker
*)

header {* Order on product types *}

theory Product_ord
imports Main
begin

instantiation "*" :: (ord, ord) ord
begin

definition
  prod_le_def [code del]: "x \<le> y \<longleftrightarrow> fst x < fst y \<or> fst x = fst y \<and> snd x \<le> snd y"

definition
  prod_less_def [code del]: "x < y \<longleftrightarrow> fst x < fst y \<or> fst x = fst y \<and> snd x < snd y"

instance ..

end

lemma [code]:
  "(x1\<Colon>'a\<Colon>{ord, eq}, y1) \<le> (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 = x2 \<and> y1 \<le> y2"
  "(x1\<Colon>'a\<Colon>{ord, eq}, y1) < (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 = x2 \<and> y1 < y2"
  unfolding prod_le_def prod_less_def by simp_all

instance * :: (order, order) order
  by default (auto simp: prod_le_def prod_less_def intro: order_less_trans)

instance * :: (linorder, linorder) linorder
  by default (auto simp: prod_le_def)

instantiation * :: (linorder, linorder) distrib_lattice
begin

definition
  inf_prod_def: "(inf \<Colon> 'a \<times> 'b \<Rightarrow> _ \<Rightarrow> _) = min"

definition
  sup_prod_def: "(sup \<Colon> 'a \<times> 'b \<Rightarrow> _ \<Rightarrow> _) = max"

instance
  by intro_classes
    (auto simp add: inf_prod_def sup_prod_def min_max.sup_inf_distrib1)

end

end
