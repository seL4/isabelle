(*  Title:      HOL/Library/Sublist.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

header {* Prefix order on lists as order class instance *}

theory Prefix_Order
imports Sublist
begin

instantiation list :: (type) order
begin

definition "(xs::'a list) \<le> ys \<equiv> prefixeq xs ys"
definition "(xs::'a list) < ys \<equiv> xs \<le> ys \<and> \<not> (ys \<le> xs)"

instance by (default, unfold less_eq_list_def less_list_def) auto

end

lemmas prefixI [intro?] = prefixeqI [folded less_eq_list_def]
lemmas prefixE [elim?] = prefixeqE [folded less_eq_list_def]
lemmas strict_prefixI' [intro?] = prefixI' [folded less_list_def]
lemmas strict_prefixE' [elim?] = prefixE' [folded less_list_def]
lemmas strict_prefixI [intro?] = prefixI [folded less_list_def]
lemmas strict_prefixE [elim?] = prefixE [folded less_list_def]
theorems Nil_prefix [iff] = Nil_prefixeq [folded less_eq_list_def]
theorems prefix_Nil [simp] = prefixeq_Nil [folded less_eq_list_def]
lemmas prefix_snoc [simp] = prefixeq_snoc [folded less_eq_list_def]
lemmas Cons_prefix_Cons [simp] = Cons_prefixeq_Cons [folded less_eq_list_def]
lemmas same_prefix_prefix [simp] = same_prefixeq_prefixeq [folded less_eq_list_def]
lemmas same_prefix_nil [iff] = same_prefixeq_nil [folded less_eq_list_def]
lemmas prefix_prefix [simp] = prefixeq_prefixeq [folded less_eq_list_def]
theorems prefix_Cons = prefixeq_Cons [folded less_eq_list_def]
theorems prefix_length_le = prefixeq_length_le [folded less_eq_list_def]
lemmas strict_prefix_simps [simp, code] = prefix_simps [folded less_list_def]
lemmas not_prefix_induct [consumes 1, case_names Nil Neq Eq] =
  not_prefixeq_induct [folded less_eq_list_def]

end
