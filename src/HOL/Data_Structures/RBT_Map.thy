(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Maps\<close>

theory RBT_Map
imports
  RBT_Set
  Map_by_Ordered
begin

fun lookup :: "('a::linorder * 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node _ l (a,b) r) x =
  (if x < a then lookup l x else
   if x > a then lookup r x else Some b)"

fun update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) rbt \<Rightarrow> ('a*'b) rbt" where
"update x y Leaf = R Leaf (x,y) Leaf" |
"update x y (B l (a,b) r) =
  (if x < a then bal (update x y l) (a,b) r else
   if x > a then bal l (a,b) (update x y r)
   else B l (x,y) r)" |
"update x y (R l (a,b) r) =
  (if x < a then R (update x y l) (a,b) r else
   if x > a then R l (a,b) (update x y r)
   else R l (x,y) r)"

fun delete :: "'a::linorder \<Rightarrow> ('a*'b)rbt \<Rightarrow> ('a*'b)rbt"
and deleteL :: "'a::linorder \<Rightarrow> ('a*'b)rbt \<Rightarrow> 'a*'b \<Rightarrow> ('a*'b)rbt \<Rightarrow> ('a*'b)rbt"
and deleteR :: "'a::linorder \<Rightarrow> ('a*'b)rbt \<Rightarrow> 'a*'b \<Rightarrow> ('a*'b)rbt \<Rightarrow> ('a*'b)rbt"
where
"delete x Leaf = Leaf" |
"delete x (Node c t1 (a,b) t2) = 
  (if x < a then deleteL x t1 (a,b) t2 else
   if x > a then deleteR x t1 (a,b) t2 else combine t1 t2)" |
"deleteL x (B t1 a t2) b t3 = balL (delete x (B t1 a t2)) b t3" |
"deleteL x t1 a t2 = R (delete x t1) a t2" |
"deleteR x t1 a (B t2 b t3) = balR t1 a (delete x (B t2 b t3))" | 
"deleteR x t1 a t2 = R t1 a (delete x t2)"


subsection "Functional Correctness Proofs"

lemma lookup_eq:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by(induction t)
  (auto simp: sorted_lems map_of_append map_of_sorteds split: option.split)


lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by(induction x y t rule: update.induct)
  (auto simp: upd_list_simps inorder_bal)


lemma inorder_delete:
 "sorted1(inorder t1) \<Longrightarrow>  inorder(delete x t1) = del_list x (inorder t1)" and
 "sorted1(inorder t1) \<Longrightarrow>  inorder(deleteL x t1 a t2) =
    del_list x (inorder t1) @ a # inorder t2" and
 "sorted1(inorder t2) \<Longrightarrow>  inorder(deleteR x t1 a t2) =
    inorder t1 @ a # del_list x (inorder t2)"
by(induction x t1 and x t1 a t2 and x t1 a t2 rule: delete_deleteL_deleteR.induct)
  (auto simp: del_list_sorted sorted_lems inorder_combine inorder_balL inorder_balR)


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
