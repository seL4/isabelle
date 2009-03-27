(*  Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen
*)

header{*Quicksort*}

theory Quicksort
imports Main Multiset
begin

context linorder
begin

fun quicksort :: "'a list \<Rightarrow> 'a list" where
"quicksort []     = []" |
"quicksort (x#xs) = quicksort([y\<leftarrow>xs. ~ x\<le>y]) @ [x] @ quicksort([y\<leftarrow>xs. x\<le>y])"

lemma quicksort_permutes [simp]:
  "multiset_of (quicksort xs) = multiset_of xs"
by (induct xs rule: quicksort.induct) (auto simp: union_ac)

lemma set_quicksort [simp]: "set (quicksort xs) = set xs"
by(simp add: set_count_greater_0)

lemma sorted_quicksort: "sorted(quicksort xs)"
apply (induct xs rule: quicksort.induct)
 apply simp
apply (simp add:sorted_Cons sorted_append not_le less_imp_le)
apply (metis leD le_cases le_less_trans)
done

end

end
