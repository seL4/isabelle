(*  Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen
*)

section \<open>Quicksort with function package\<close>

theory Quicksort
imports "HOL-Library.Multiset"
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
  "mset (quicksort xs) = mset xs"
  by (induct xs rule: quicksort.induct) (simp_all add: ac_simps)

lemma set_quicksort [simp]: "set (quicksort xs) = set xs"
proof -
  have "set_mset (mset (quicksort xs)) = set_mset (mset xs)"
    by simp
  then show ?thesis by (simp only: set_mset_mset)
qed

lemma sorted_quicksort: "sorted (quicksort xs)"
  by (induct xs rule: quicksort.induct) (auto simp add: sorted_append not_le less_imp_le)

theorem sort_quicksort:
  "sort = quicksort"
  by (rule ext, rule properties_for_sort) (fact quicksort_permutes sorted_quicksort)+

end

end
