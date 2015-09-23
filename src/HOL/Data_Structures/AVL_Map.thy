(* Author: Tobias Nipkow *)

section "AVL Tree Implementation of Maps"

theory AVL_Map
imports
  AVL_Set
  Lookup2
begin

fun update :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a*'b) avl_tree \<Rightarrow> ('a*'b) avl_tree" where
"update x y Leaf = Node 1 Leaf (x,y) Leaf" |
"update x y (Node h l (a,b) r) = 
   (if x = a then Node h l (x,y) r else
    if x < a then node_bal_l (update x y l) (a,b) r
    else node_bal_r l (a,b) (update x y r))"

fun delete :: "'a::order \<Rightarrow> ('a*'b) avl_tree \<Rightarrow> ('a*'b) avl_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node h l (a,b) r) = (
   if x = a then delete_root (Node h l (a,b) r) else
   if x < a then node_bal_r (delete x l) (a,b) r
   else node_bal_l l (a,b) (delete x r))"


subsection {* Functional Correctness Proofs *}

theorem inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by (induct t) 
   (auto simp: upd_list_simps inorder_node_bal_l inorder_node_bal_r)


theorem inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_node_bal_l inorder_node_bal_r
     inorder_delete_root inorder_delete_maxD split: prod.splits)


interpretation Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update and delete = delete
and inorder = inorder and wf = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: lookup_eq)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed (rule TrueI)+

end
