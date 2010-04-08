(*  Title:      HOL/Imperative_HOL/ex/Sorted_List.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

header {* Sorted lists as representation of finite sets *}

theory Sorted_List
imports Main
begin

text {* Merge function for two distinct sorted lists to get compound distinct sorted list *}
   
fun merge :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge (x#xs) (y#ys) =
  (if x < y then x # merge xs (y#ys) else (if x > y then y # merge (x#xs) ys else x # merge xs ys))"
| "merge xs [] = xs"
| "merge [] ys = ys"

text {* The function package does not derive automatically the more general rewrite rule as follows: *}
lemma merge_Nil[simp]: "merge [] ys = ys"
by (cases ys) auto

lemma set_merge[simp]: "set (merge xs ys) = set xs \<union> set ys"
by (induct xs ys rule: merge.induct, auto)

lemma sorted_merge[simp]:
     "List.sorted (merge xs ys) = (List.sorted xs \<and> List.sorted ys)"
by (induct xs ys rule: merge.induct, auto simp add: sorted_Cons)

lemma distinct_merge[simp]: "\<lbrakk> distinct xs; distinct ys; List.sorted xs; List.sorted ys \<rbrakk> \<Longrightarrow> distinct (merge xs ys)"
by (induct xs ys rule: merge.induct, auto simp add: sorted_Cons)

text {* The remove function removes an element from a sorted list *}

fun remove :: "('a :: linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove a [] = []"
  |  "remove a (x#xs) = (if a > x then (x # remove a xs) else (if a = x then xs else x#xs))" 

lemma remove': "sorted xs \<and> distinct xs \<Longrightarrow> sorted (remove a xs) \<and> distinct (remove a xs) \<and> set (remove a xs) = set xs - {a}"
apply (induct xs)
apply (auto simp add: sorted_Cons)
done

lemma set_remove[simp]: "\<lbrakk> sorted xs; distinct xs \<rbrakk> \<Longrightarrow> set (remove a xs) = set xs - {a}"
using remove' by auto

lemma sorted_remove[simp]: "\<lbrakk> sorted xs; distinct xs \<rbrakk> \<Longrightarrow> sorted (remove a xs)" 
using remove' by auto

lemma distinct_remove[simp]: "\<lbrakk> sorted xs; distinct xs \<rbrakk> \<Longrightarrow> distinct (remove a xs)" 
using remove' by auto

lemma remove_insort_cancel: "remove a (insort a xs) = xs"
apply (induct xs)
apply simp
apply auto
done

lemma remove_insort_commute: "\<lbrakk> a \<noteq> b; sorted xs \<rbrakk> \<Longrightarrow> remove b (insort a xs) = insort a (remove b xs)"
apply (induct xs)
apply auto
apply (auto simp add: sorted_Cons)
apply (case_tac xs)
apply auto
done

lemma notinset_remove: "x \<notin> set xs \<Longrightarrow> remove x xs = xs"
apply (induct xs)
apply auto
done

lemma remove1_eq_remove:
  "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow> remove1 x xs = remove x xs"
apply (induct xs)
apply (auto simp add: sorted_Cons)
apply (subgoal_tac "x \<notin> set xs")
apply (simp add: notinset_remove)
apply fastsimp
done

lemma sorted_remove1:
  "sorted xs \<Longrightarrow> sorted (remove1 x xs)"
apply (induct xs)
apply (auto simp add: sorted_Cons)
done

subsection {* Efficient member function for sorted lists: smem *}

fun smember :: "('a::linorder) \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "smem" 55)
where
  "x smem [] = False"
|  "x smem (y#ys) = (if x = y then True else (if (x > y) then x smem ys else False))" 

lemma "sorted xs \<Longrightarrow> x smem xs = (x \<in> set xs)" 
apply (induct xs)
apply (auto simp add: sorted_Cons)
done

end