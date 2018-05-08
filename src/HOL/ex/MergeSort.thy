(*  Title:      HOL/ex/MergeSort.thy
    Author:     Tobias Nipkow
    Copyright   2002 TU Muenchen
*)

section\<open>Merge Sort\<close>

theory MergeSort
imports "HOL-Library.Multiset"
begin

context linorder
begin

fun merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge (x#xs) (y#ys) =
         (if x \<le> y then x # merge xs (y#ys) else y # merge (x#xs) ys)"
| "merge xs [] = xs"
| "merge [] ys = ys"

lemma mset_merge [simp]:
  "mset (merge xs ys) = mset xs + mset ys"
  by (induct xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge [simp]:
  "set (merge xs ys) = set xs \<union> set ys"
  by (induct xs ys rule: merge.induct) auto

lemma sorted_merge [simp]:
  "sorted (merge xs ys) \<longleftrightarrow> sorted xs \<and> sorted ys"
  by (induct xs ys rule: merge.induct) (auto simp add: ball_Un not_le less_le)

fun msort :: "'a list \<Rightarrow> 'a list"
where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = merge (msort (take (size xs div 2) xs))
                    (msort (drop (size xs div 2) xs))"

lemma sorted_msort:
  "sorted (msort xs)"
  by (induct xs rule: msort.induct) simp_all

lemma mset_msort:
  "mset (msort xs) = mset xs"
  by (induct xs rule: msort.induct)
    (simp_all, metis append_take_drop_id mset.simps(2) mset_append)

theorem msort_sort:
  "sort = msort"
  by (rule ext, rule properties_for_sort) (fact mset_msort sorted_msort)+

end

end
