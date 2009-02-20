(*  Title:      HOL/Library/Product_plus.thy
    Author:     Brian Huffman
*)

header {* Additive group operations on product types *}

theory Product_plus
imports Main
begin

subsection {* Operations *}

instantiation "*" :: (zero, zero) zero
begin

definition zero_prod_def: "0 = (0, 0)"

instance ..
end

instantiation "*" :: (plus, plus) plus
begin

definition plus_prod_def:
  "x + y = (fst x + fst y, snd x + snd y)"

instance ..
end

instantiation "*" :: (minus, minus) minus
begin

definition minus_prod_def:
  "x - y = (fst x - fst y, snd x - snd y)"

instance ..
end

instantiation "*" :: (uminus, uminus) uminus
begin

definition uminus_prod_def:
  "- x = (- fst x, - snd x)"

instance ..
end

lemma fst_zero [simp]: "fst 0 = 0"
  unfolding zero_prod_def by simp

lemma snd_zero [simp]: "snd 0 = 0"
  unfolding zero_prod_def by simp

lemma fst_add [simp]: "fst (x + y) = fst x + fst y"
  unfolding plus_prod_def by simp

lemma snd_add [simp]: "snd (x + y) = snd x + snd y"
  unfolding plus_prod_def by simp

lemma fst_diff [simp]: "fst (x - y) = fst x - fst y"
  unfolding minus_prod_def by simp

lemma snd_diff [simp]: "snd (x - y) = snd x - snd y"
  unfolding minus_prod_def by simp

lemma fst_uminus [simp]: "fst (- x) = - fst x"
  unfolding uminus_prod_def by simp

lemma snd_uminus [simp]: "snd (- x) = - snd x"
  unfolding uminus_prod_def by simp

lemma add_Pair [simp]: "(a, b) + (c, d) = (a + c, b + d)"
  unfolding plus_prod_def by simp

lemma diff_Pair [simp]: "(a, b) - (c, d) = (a - c, b - d)"
  unfolding minus_prod_def by simp

lemma uminus_Pair [simp, code]: "- (a, b) = (- a, - b)"
  unfolding uminus_prod_def by simp

lemmas expand_prod_eq = Pair_fst_snd_eq


subsection {* Class instances *}

instance "*" :: (semigroup_add, semigroup_add) semigroup_add
  by default (simp add: expand_prod_eq add_assoc)

instance "*" :: (ab_semigroup_add, ab_semigroup_add) ab_semigroup_add
  by default (simp add: expand_prod_eq add_commute)

instance "*" :: (monoid_add, monoid_add) monoid_add
  by default (simp_all add: expand_prod_eq)

instance "*" :: (comm_monoid_add, comm_monoid_add) comm_monoid_add
  by default (simp add: expand_prod_eq)

instance "*" ::
  (cancel_semigroup_add, cancel_semigroup_add) cancel_semigroup_add
    by default (simp_all add: expand_prod_eq)

instance "*" ::
  (cancel_ab_semigroup_add, cancel_ab_semigroup_add) cancel_ab_semigroup_add
    by default (simp add: expand_prod_eq)

instance "*" ::
  (cancel_comm_monoid_add, cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance "*" :: (group_add, group_add) group_add
  by default (simp_all add: expand_prod_eq diff_minus)

instance "*" :: (ab_group_add, ab_group_add) ab_group_add
  by default (simp_all add: expand_prod_eq)

end
