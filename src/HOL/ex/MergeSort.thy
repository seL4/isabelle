(*  Title:      HOL/ex/Merge.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TU Muenchen

Merge sort
*)

theory MergeSort = Sorting:

consts merge :: "('a::linorder)list * 'a list \<Rightarrow> 'a list"

recdef merge "measure(%(xs,ys). size xs + size ys)"
"merge(x#xs,y#ys) =
 (if x <= y then x # merge(xs,y#ys) else y # merge(x#xs,ys))"
"merge(xs,[]) = xs"
"merge([],ys) = ys"

lemma [simp]: "multiset(merge(xs,ys)) x = multiset xs x + multiset ys x"
apply(induct xs ys rule: merge.induct)
apply auto
done

lemma [simp]: "set(merge(xs,ys)) = set xs \<union> set ys"
apply(induct xs ys rule: merge.induct)
apply auto
done

lemma [simp]:
 "sorted (op <=) (merge(xs,ys)) = (sorted (op <=) xs & sorted (op <=) ys)"
apply(induct xs ys rule: merge.induct)
apply(simp_all add:ball_Un linorder_not_le order_less_le)
apply(blast intro: order_trans)
done

consts msort :: "('a::linorder) list \<Rightarrow> 'a list"
recdef msort "measure size"
"msort [] = []"
"msort [x] = [x]"
"msort xs = merge(msort(take (size xs div 2) xs),
                  msort(drop (size xs div 2) xs))"

lemma "sorted op <= (msort xs)"
by (induct xs rule: msort.induct) simp_all

lemma "multiset(msort xs) x = multiset xs x"
apply (induct xs rule: msort.induct)
  apply simp
 apply simp
apply (simp del:multiset_append add:multiset_append[symmetric])
done

end
