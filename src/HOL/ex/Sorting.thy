(*  Title:      HOL/ex/sorting.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Specification of sorting
*)

theory Sorting = Main + Multiset:

consts
  sorted1:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  sorted :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"

primrec
  "sorted1 le [] = True"
  "sorted1 le (x#xs) = ((case xs of [] => True | y#ys => le x y) &
                        sorted1 le xs)"

primrec
  "sorted le [] = True"
  "sorted le (x#xs) = ((!y:set xs. le x y) & sorted le xs)"


constdefs
  total  :: "('a \<Rightarrow> 'a \<Rightarrow> bool) => bool"
   "total r == (ALL x y. r x y | r y x)"
  
  transf :: "('a \<Rightarrow> 'a \<Rightarrow> bool) => bool"
   "transf f == (ALL x y z. f x y & f y z --> f x z)"



(* Equivalence of two definitions of `sorted' *)

lemma sorted1_is_sorted:
 "transf(le) ==> sorted1 le xs = sorted le xs";
apply(induct xs)
 apply simp
apply(simp split: list.split)
apply(unfold transf_def);
apply(blast)
done

lemma sorted_append[simp]:
 "sorted le (xs@ys) = (sorted le xs \<and> sorted le ys \<and>
                       (\<forall>x \<in> set xs. \<forall>y \<in> set ys. le x y))"
by (induct xs, auto)

end
