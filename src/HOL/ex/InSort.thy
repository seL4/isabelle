(*  Title:      HOL/ex/insort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Insertion sort
*)

theory InSort  =  Sorting:

consts
  ins :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  insort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"

primrec
  "ins le x [] = [x]"
  "ins le x (y#ys) = (if le x y then (x#y#ys) else y#(ins le x ys))"

primrec
  "insort le [] = []"
  "insort le (x#xs) = ins le x (insort le xs)"


lemma multiset_ins[simp]:
 "\<And>y. multiset(ins le x xs) y = multiset (x#xs) y"
by (induct "xs") auto

lemma insort_permutes[simp]:
 "\<And>x. multiset(insort le xs) x = multiset xs x";
by (induct "xs") auto

lemma set_ins[simp]: "set(ins le x xs) = insert x (set xs)"
by (simp add: set_via_multiset) fast

lemma sorted_ins[simp]:
 "\<lbrakk> total le; transf le \<rbrakk> \<Longrightarrow> sorted le (ins le x xs) = sorted le xs";
apply (induct xs)
apply simp_all
apply (unfold Sorting.total_def Sorting.transf_def)
apply blast
done

lemma sorted_insort:
 "[| total(le); transf(le) |] ==>  sorted le (insort le xs)"
by (induct xs) auto

end

