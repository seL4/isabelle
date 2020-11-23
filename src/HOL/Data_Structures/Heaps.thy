(* Author: Tobias Nipkow *)

section \<open>Heaps\<close>

theory Heaps
imports
  "HOL-Library.Tree_Multiset"
  Priority_Queue_Specs
begin

text \<open>Heap = priority queue on trees:\<close>
    
locale Heap =
fixes insert :: "('a::linorder) \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
and  del_min :: "'a tree \<Rightarrow> 'a tree"
assumes mset_insert: "heap q \<Longrightarrow> mset_tree (insert x q) = {#x#} + mset_tree q"
and    mset_del_min: "\<lbrakk> heap q;  q \<noteq> Leaf \<rbrakk> \<Longrightarrow> mset_tree (del_min q) = mset_tree q - {#value q#}"
and     heap_insert: "heap q \<Longrightarrow> heap(insert x q)"
and    heap_del_min: "heap q \<Longrightarrow> heap(del_min q)"
begin

definition empty :: "'a tree" where
"empty = Leaf"

fun is_empty :: "'a tree \<Rightarrow> bool" where
"is_empty t = (t = Leaf)"

sublocale Priority_Queue where empty = empty and is_empty = is_empty and insert = insert
and get_min = "value" and del_min = del_min and invar = heap and mset = mset_tree
proof (standard, goal_cases)
  case 1 thus ?case by (simp add: empty_def)
next
  case 2 thus ?case by(auto)
next
  case 3 thus ?case by(simp add: mset_insert)
next
  case 4 thus ?case by(simp add: mset_del_min)
next
  case 5 thus ?case by(auto simp: neq_Leaf_iff Min_insert2 simp del: Un_iff)
next
  case 6 thus ?case by(simp add: empty_def)
next
  case 7 thus ?case by(simp add: heap_insert)
next
  case 8 thus ?case by(simp add: heap_del_min)
qed

end


text \<open>Once you have \<open>merge\<close>, \<open>insert\<close> and \<open>del_min\<close> are easy:\<close>

locale Heap_Merge =
fixes merge :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
assumes mset_merge: "\<lbrakk> heap q1; heap q2 \<rbrakk> \<Longrightarrow> mset_tree (merge q1 q2) = mset_tree q1 + mset_tree q2"
and invar_merge: "\<lbrakk> heap q1; heap q2 \<rbrakk> \<Longrightarrow> heap (merge q1 q2)"
begin

fun insert :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x t = merge (Node Leaf x Leaf) t"

fun del_min :: "'a tree \<Rightarrow> 'a tree" where
"del_min Leaf = Leaf" |
"del_min (Node l x r) = merge l r"

interpretation Heap insert del_min
proof(standard, goal_cases)
  case 1 thus ?case by(simp add:mset_merge)
next
  case (2 q) thus ?case by(cases q)(auto simp: mset_merge)
next
  case 3 thus ?case by (simp add: invar_merge)
next
  case (4 q) thus ?case by (cases q)(auto simp: invar_merge)
qed

sublocale PQM: Priority_Queue_Merge where empty = empty and is_empty = is_empty and insert = insert
and get_min = "value" and del_min = del_min and invar = heap and mset = mset_tree and merge = merge
proof(standard, goal_cases)
  case 1 thus ?case by (simp add: mset_merge)
next
  case 2 thus ?case by (simp add: invar_merge)
qed

end

end
