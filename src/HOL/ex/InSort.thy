(*  Title:      HOL/ex/insort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen
*)

header{*Insertion Sort*}

theory InSort
imports Sorting
begin

consts
  ins    :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  insort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"

primrec
  "ins le x [] = [x]"
  "ins le x (y#ys) = (if le x y then (x#y#ys) else y#(ins le x ys))"

primrec
  "insort le [] = []"
  "insort le (x#xs) = ins le x (insort le xs)"


lemma multiset_ins[simp]:
 "\<And>y. multiset_of (ins le x xs) = multiset_of (x#xs)"
  by (induct xs) (auto simp: union_ac)

theorem insort_permutes[simp]:
 "\<And>x. multiset_of (insort le xs) = multiset_of xs"
  by (induct "xs") auto

lemma set_ins [simp]: "set(ins le x xs) = insert x (set xs)"
  by (simp add: set_count_greater_0) fast

lemma sorted_ins[simp]:
 "\<lbrakk> total le; transf le \<rbrakk> \<Longrightarrow> sorted le (ins le x xs) = sorted le xs";
apply (induct xs)
apply simp_all
apply (unfold Sorting.total_def Sorting.transf_def)
apply blast
done

theorem sorted_insort:
 "[| total(le); transf(le) |] ==>  sorted le (insort le xs)"
by (induct xs) auto

end

