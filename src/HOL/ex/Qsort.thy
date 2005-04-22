(*  Title:      HOL/ex/Qsort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen
*)

header{*Quicksort*}

theory Qsort
imports Sorting
begin

subsection{*Version 1: higher-order*}

consts qsort :: "('a \<Rightarrow> 'a => bool) * 'a list \<Rightarrow> 'a list"

recdef qsort "measure (size o snd)"
    "qsort(le, [])   = []"
    "qsort(le, x#xs) = qsort(le, [y:xs . ~ le x y]) @ [x] @
		       qsort(le, [y:xs . le x y])"
(hints recdef_simp: length_filter_le[THEN le_less_trans])

lemma qsort_permutes [simp]:
     "multiset_of (qsort(le,xs)) = multiset_of xs"
by (induct le xs rule: qsort.induct) (auto simp: union_ac)

lemma set_qsort [simp]: "set (qsort(le,xs)) = set xs";
by(simp add: set_count_greater_0)

lemma sorted_qsort:
     "total(le) ==> transf(le) ==> sorted le (qsort(le,xs))"
apply (induct le xs rule: qsort.induct)
 apply simp
apply simp
apply(unfold Sorting.total_def Sorting.transf_def)
apply blast
done


subsection{*Version 2:type classes*}

consts quickSort :: "('a::linorder) list => 'a list"

recdef quickSort "measure size"
    "quickSort []   = []"
    "quickSort (x#l) = quickSort [y:l. ~ x\<le>y] @ [x] @ quickSort [y:l. x\<le>y]"
(hints recdef_simp: length_filter_le[THEN le_less_trans])

lemma quickSort_permutes[simp]:
 "multiset_of (quickSort xs) = multiset_of xs"
by (induct xs rule: quickSort.induct) (auto simp: union_ac)

lemma set_quickSort[simp]: "set (quickSort xs) = set xs"
by(simp add: set_count_greater_0)

theorem sorted_quickSort: "sorted (op \<le>) (quickSort xs)"
by (induct xs rule: quickSort.induct, auto)

end
