(*  Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen
*)

section {* Quicksort with function package *}

theory Quicksort
imports "~~/src/HOL/Library/Multiset"
begin

context linorder
begin

fun quicksort :: "'a list \<Rightarrow> 'a list" where
  "quicksort []     = []"
| "quicksort (x#xs) = quicksort [y\<leftarrow>xs. \<not> x\<le>y] @ [x] @ quicksort [y\<leftarrow>xs. x\<le>y]"

lemma [code]:
  "quicksort []     = []"
  "quicksort (x#xs) = quicksort [y\<leftarrow>xs. y<x] @ [x] @ quicksort [y\<leftarrow>xs. x\<le>y]"
  by (simp_all add: not_le)

lemma quicksort_permutes [simp]:
  "multiset_of (quicksort xs) = multiset_of xs"
  by (induct xs rule: quicksort.induct) (simp_all add: ac_simps)

lemma set_quicksort [simp]: "set (quicksort xs) = set xs"
  by (simp add: set_count_greater_0)

lemma sorted_quicksort: "sorted (quicksort xs)"
  by (induct xs rule: quicksort.induct) (auto simp add: sorted_Cons sorted_append not_le less_imp_le)

theorem sort_quicksort:
  "sort = quicksort"
  by (rule ext, rule properties_for_sort) (fact quicksort_permutes sorted_quicksort)+

end

end
