(*  Title:      HOL/ex/Qsort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Quicksort
*)

theory Qsort = Sorting:

(*Version one: higher-order*)
consts qsort :: "('a \<Rightarrow> 'a => bool) * 'a list \<Rightarrow> 'a list"

recdef qsort "measure (size o snd)"
"qsort(le, [])   = []"
"qsort(le, x#xs) = qsort(le, [y:xs . ~ le x y]) @ [x] @
                   qsort(le, [y:xs . le x y])"
(hints recdef_simp: length_filter[THEN le_less_trans])

lemma qsort_permutes[simp]:
 "multiset (qsort(le,xs)) x = multiset xs x"
by (induct le xs rule: qsort.induct, auto)


(*Also provable by induction*)
lemma set_qsort[simp]: "set (qsort(le,xs)) = set xs";
by(simp add: set_via_multiset)

lemma sorted_qsort:
 "total(le) ==> transf(le) ==> sorted le (qsort(le,xs))"
apply (induct le xs rule: qsort.induct)
 apply simp
apply simp
apply(unfold Sorting.total_def Sorting.transf_def)
apply blast
done


(*Version two: type classes*)

consts quickSort :: "('a::linorder) list => 'a list"

recdef quickSort "measure size"
"quickSort []   = []"
"quickSort (x#l) = quickSort [y:l. ~ x<=y] @ [x] @ quickSort [y:l. x<=y]"
(hints recdef_simp: length_filter[THEN le_less_trans])

lemma quickSort_permutes[simp]:
 "multiset (quickSort xs) z = multiset xs z"
by (induct xs rule: quickSort.induct) auto

(*Also provable by induction*)
lemma set_quickSort[simp]: "set (quickSort xs) = set xs"
by(simp add: set_via_multiset)

lemma sorted_quickSort: "sorted (op <=) (quickSort xs)"
apply (induct xs rule: quickSort.induct)
 apply simp
apply simp
apply(blast intro: linorder_linear[THEN disjE] order_trans)
done

end
