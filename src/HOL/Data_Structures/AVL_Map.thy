(* Author: Tobias Nipkow *)

section "AVL Tree Implementation of Maps"

theory AVL_Map
imports
  AVL_Set
  Lookup2
begin

fun update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) avl_tree \<Rightarrow> ('a*'b) avl_tree" where
"update x y Leaf = Node Leaf (x,y) 1 Leaf" |
"update x y (Node l (a,b) h r) = (case cmp x a of
   EQ \<Rightarrow> Node l (x,y) h r |
   LT \<Rightarrow> balL (update x y l) (a,b) r |
   GT \<Rightarrow> balR l (a,b) (update x y r))"

fun delete :: "'a::linorder \<Rightarrow> ('a*'b) avl_tree \<Rightarrow> ('a*'b) avl_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node l (a,b) h r) = (case cmp x a of
   EQ \<Rightarrow> del_root (Node l (a,b) h r) |
   LT \<Rightarrow> balR (delete x l) (a,b) r |
   GT \<Rightarrow> balL l (a,b) (delete x r))"


subsection \<open>Functional Correctness Proofs\<close>

theorem inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by (induct t) (auto simp: upd_list_simps inorder_balL inorder_balR)


theorem inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_balL inorder_balR
     inorder_del_root inorder_split_maxD split: prod.splits)

interpretation Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: lookup_map_of)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed auto

end
