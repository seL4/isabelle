(*  Title:      HOL/ex/sorting.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Specification of sorting
*)

theory Sorting = Main:

consts
  sorted1:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  sorted :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  multiset   :: "'a list => ('a => nat)"

primrec
  "sorted1 le [] = True"
  "sorted1 le (x#xs) = ((case xs of [] => True | y#ys => le x y) &
                        sorted1 le xs)"

primrec
  "sorted le [] = True"
  "sorted le (x#xs) = ((!y:set xs. le x y) & sorted le xs)"

primrec
  "multiset [] y = 0"
  "multiset (x#xs) y = (if x=y then Suc(multiset xs y) else multiset xs y)"

constdefs
  total  :: "('a \<Rightarrow> 'a \<Rightarrow> bool) => bool"
   "total r == (ALL x y. r x y | r y x)"
  
  transf :: "('a \<Rightarrow> 'a \<Rightarrow> bool) => bool"
   "transf f == (ALL x y z. f x y & f y z --> f x z)"

(* Some general lemmas *)

lemma multiset_append[simp]:
 "multiset (xs@ys) x = multiset xs x + multiset ys x"
by (induct xs, auto)

lemma multiset_compl_add[simp]:
 "multiset [x:xs. ~p(x)] z + multiset [x:xs. p(x)] z = multiset xs z";
by (induct xs, auto)

lemma set_via_multiset: "set xs = {x. multiset xs x ~= 0}";
by (induct xs, auto)

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
