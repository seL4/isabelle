(*  Title:      HOL/Library/Product_Plus.thy
    Author:     Brian Huffman
*)

section \<open>Additive group operations on product types\<close>

theory Product_Plus
imports Main
begin

subsection \<open>Operations\<close>

instantiation prod :: (zero, zero) zero
begin

definition zero_prod_def: "0 = (0, 0)"

instance ..
end

instantiation prod :: (plus, plus) plus
begin

definition plus_prod_def:
  "x + y = (fst x + fst y, snd x + snd y)"

instance ..
end

instantiation prod :: (minus, minus) minus
begin

definition minus_prod_def:
  "x - y = (fst x - fst y, snd x - snd y)"

instance ..
end

instantiation prod :: (uminus, uminus) uminus
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

subsection \<open>Class instances\<close>

instance prod :: (semigroup_add, semigroup_add) semigroup_add
  by standard (simp add: prod_eq_iff add.assoc)

instance prod :: (ab_semigroup_add, ab_semigroup_add) ab_semigroup_add
  by standard (simp add: prod_eq_iff add.commute)

instance prod :: (monoid_add, monoid_add) monoid_add
  by standard (simp_all add: prod_eq_iff)

instance prod :: (comm_monoid_add, comm_monoid_add) comm_monoid_add
  by standard (simp add: prod_eq_iff)

instance prod :: (cancel_semigroup_add, cancel_semigroup_add) cancel_semigroup_add
    by standard (simp_all add: prod_eq_iff)

instance prod :: (cancel_ab_semigroup_add, cancel_ab_semigroup_add) cancel_ab_semigroup_add
    by standard (simp_all add: prod_eq_iff diff_diff_eq)

instance prod :: (cancel_comm_monoid_add, cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance prod :: (group_add, group_add) group_add
  by standard (simp_all add: prod_eq_iff)

instance prod :: (ab_group_add, ab_group_add) ab_group_add
  by standard (simp_all add: prod_eq_iff)

lemma fst_sum: "fst (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. fst (f x))"
proof (cases "finite A")
  case True
  then show ?thesis by induct simp_all
next
  case False
  then show ?thesis by simp
qed

lemma snd_sum: "snd (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. snd (f x))"
proof (cases "finite A")
  case True
  then show ?thesis by induct simp_all
next
  case False
  then show ?thesis by simp
qed

lemma sum_prod: "(\<Sum>x\<in>A. (f x, g x)) = (\<Sum>x\<in>A. f x, \<Sum>x\<in>A. g x)"
proof (cases "finite A")
  case True
  then show ?thesis by induct (simp_all add: zero_prod_def)
next
  case False
  then show ?thesis by (simp add: zero_prod_def)
qed

end
