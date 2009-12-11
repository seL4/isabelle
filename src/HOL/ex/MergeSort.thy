(*  Title:      HOL/ex/MergeSort.thy
    Author:     Tobias Nipkow
    Copyright   2002 TU Muenchen
*)

header{*Merge Sort*}

theory MergeSort
imports Sorting
begin

context linorder
begin

fun merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge (x#xs) (y#ys) =
         (if x \<le> y then x # merge xs (y#ys) else y # merge (x#xs) ys)"
| "merge xs [] = xs"
| "merge [] ys = ys"

lemma multiset_of_merge[simp]:
     "multiset_of (merge xs ys) = multiset_of xs + multiset_of ys"
apply(induct xs ys rule: merge.induct)
apply (auto simp: union_ac)
done

lemma set_merge[simp]: "set (merge xs ys) = set xs \<union> set ys"
apply(induct xs ys rule: merge.induct)
apply auto
done

lemma sorted_merge[simp]:
     "sorted (op \<le>) (merge xs ys) = (sorted (op \<le>) xs & sorted (op \<le>) ys)"
apply(induct xs ys rule: merge.induct)
apply(simp_all add: ball_Un not_le less_le)
apply(blast intro: order_trans)
done

fun msort :: "'a list \<Rightarrow> 'a list"
where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = merge (msort (take (size xs div 2) xs))
                    (msort (drop (size xs div 2) xs))"

theorem sorted_msort: "sorted (op \<le>) (msort xs)"
by (induct xs rule: msort.induct) simp_all

theorem multiset_of_msort: "multiset_of (msort xs) = multiset_of xs"
apply (induct xs rule: msort.induct)
  apply simp_all
apply (metis append_take_drop_id drop_Suc_Cons multiset_of.simps(2) multiset_of_append take_Suc_Cons)
done

end


end
