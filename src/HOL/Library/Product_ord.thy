(*  Title:      HOL/Library/Product_ord.thy
    ID:         $Id$
    Author:     Norbert Voelker
*)

header {* Order on product types *}

theory Product_ord
imports Main
begin

instance "*" :: (ord, ord) ord ..

defs (overloaded)
  prod_le_def: "(x \<le> y) \<equiv> (fst x < fst y) | (fst x = fst y & snd x \<le> snd y)"
  prod_less_def: "(x < y) \<equiv> (fst x < fst y) | (fst x = fst y & snd x < snd y)"


lemmas prod_ord_defs = prod_less_def prod_le_def

instance * :: (order, order) order
  by default (auto simp: prod_ord_defs intro: order_less_trans)

instance * :: (linorder, linorder) linorder
  by default (auto simp: prod_le_def)

end
