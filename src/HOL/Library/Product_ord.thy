(*  Title:      HOL/Library/Product_ord.thy
    ID:         $Id$
    Author:     Norbert Voelker
*)

header {* Order on product types *}

theory Product_ord
imports Main
begin

instance "*" :: (ord, ord) ord
  prod_le_def: "(x \<le> y) \<equiv> (fst x < fst y) \<or> (fst x = fst y \<and> snd x \<le> snd y)"
  prod_less_def: "(x < y) \<equiv> (fst x < fst y) \<or> (fst x = fst y \<and> snd x < snd y)" ..

lemmas prod_ord_defs = prod_less_def prod_le_def

lemma [code func]:
  "(x1\<Colon>'a\<Colon>{ord, eq}, y1) \<le> (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 = x2 \<and> y1 \<le> y2"
  "(x1\<Colon>'a\<Colon>{ord, eq}, y1) < (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 = x2 \<and> y1 < y2"
  unfolding prod_ord_defs by simp_all

lemma [code]:
  "(x1, y1) \<le> (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 = x2 \<and> y1 \<le> y2"
  "(x1, y1) < (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 = x2 \<and> y1 < y2"
  unfolding prod_ord_defs by simp_all

instance * :: (order, order) order
  by default (auto simp: prod_ord_defs intro: order_less_trans)

instance * :: (linorder, linorder) linorder
  by default (auto simp: prod_le_def)

end
