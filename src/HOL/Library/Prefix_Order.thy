(*  Title:      HOL/Library/Prefix_Order.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

section \<open>Prefix order on lists as order class instance\<close>

theory Prefix_Order
imports Sublist
begin

instantiation list :: (type) order
begin

definition "xs \<le> ys \<equiv> prefix xs ys" for xs ys :: "'a list"
definition "xs < ys \<equiv> xs \<le> ys \<and> \<not> (ys \<le> xs)" for xs ys :: "'a list"

instance
  by standard (auto simp: less_eq_list_def less_list_def)

end

lemma less_list_def': "xs < ys \<longleftrightarrow> strict_prefix xs ys" for xs ys :: "'a list"
  by (simp add: less_eq_list_def order.strict_iff_order prefix_order.less_le)

lemmas prefixI [intro?] = prefixI [folded less_eq_list_def]
lemmas prefixE [elim?] = prefixE [folded less_eq_list_def]
lemmas strict_prefixI' [intro?] = strict_prefixI' [folded less_list_def']
lemmas strict_prefixE' [elim?] = strict_prefixE' [folded less_list_def']
lemmas strict_prefixI [intro?] = strict_prefixI [folded less_list_def']
lemmas strict_prefixE [elim?] = strict_prefixE [folded less_list_def']
lemmas Nil_prefix [iff] = Nil_prefix [folded less_eq_list_def]
lemmas prefix_Nil [simp] = prefix_Nil [folded less_eq_list_def]
lemmas prefix_snoc [simp] = prefix_snoc [folded less_eq_list_def]
lemmas Cons_prefix_Cons [simp] = Cons_prefix_Cons [folded less_eq_list_def]
lemmas same_prefix_prefix [simp] = same_prefix_prefix [folded less_eq_list_def]
lemmas same_prefix_nil [iff] = same_prefix_nil [folded less_eq_list_def]
lemmas prefix_prefix [simp] = prefix_prefix [folded less_eq_list_def]
lemmas prefix_Cons = prefix_Cons [folded less_eq_list_def]
lemmas prefix_length_le = prefix_length_le [folded less_eq_list_def]
lemmas strict_prefix_simps [simp, code] = strict_prefix_simps [folded less_list_def']
lemmas not_prefix_induct [consumes 1, case_names Nil Neq Eq] =
  not_prefix_induct [folded less_eq_list_def]

end
