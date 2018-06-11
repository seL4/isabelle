(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Maps\<close>

theory RBT_Map
imports
  RBT_Set
  Lookup2
begin

fun upd :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) rbt \<Rightarrow> ('a*'b) rbt" where
"upd x y Leaf = R Leaf (x,y) Leaf" |
"upd x y (B l (a,b) r) = (case cmp x a of
  LT \<Rightarrow> baliL (upd x y l) (a,b) r |
  GT \<Rightarrow> baliR l (a,b) (upd x y r) |
  EQ \<Rightarrow> B l (x,y) r)" |
"upd x y (R l (a,b) r) = (case cmp x a of
  LT \<Rightarrow> R (upd x y l) (a,b) r |
  GT \<Rightarrow> R l (a,b) (upd x y r) |
  EQ \<Rightarrow> R l (x,y) r)"

definition update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) rbt \<Rightarrow> ('a*'b) rbt" where
"update x y t = paint Black (upd x y t)"

fun del :: "'a::linorder \<Rightarrow> ('a*'b)rbt \<Rightarrow> ('a*'b)rbt"
and delL :: "'a::linorder \<Rightarrow> ('a*'b)rbt \<Rightarrow> 'a*'b \<Rightarrow> ('a*'b)rbt \<Rightarrow> ('a*'b)rbt"
and delR :: "'a::linorder \<Rightarrow> ('a*'b)rbt \<Rightarrow> 'a*'b \<Rightarrow> ('a*'b)rbt \<Rightarrow> ('a*'b)rbt"
where
"del x Leaf = Leaf" |
"del x (Node t1 (a,b) c t2) = (case cmp x a of
  LT \<Rightarrow> delL x t1 (a,b) t2 |
  GT \<Rightarrow> delR x t1 (a,b) t2 |
  EQ \<Rightarrow> combine t1 t2)" |
"delL x (B t1 a t2) b t3 = baldL (del x (B t1 a t2)) b t3" |
"delL x t1 a t2 = R (del x t1) a t2" |
"delR x t1 a (B t2 b t3) = baldR t1 a (del x (B t2 b t3))" | 
"delR x t1 a t2 = R t1 a (del x t2)"

definition delete :: "'a::linorder \<Rightarrow> ('a*'b) rbt \<Rightarrow> ('a*'b) rbt" where
"delete x t = paint Black (del x t)"


subsection "Functional Correctness Proofs"

lemma inorder_upd:
  "sorted1(inorder t) \<Longrightarrow> inorder(upd x y t) = upd_list x y (inorder t)"
by(induction x y t rule: upd.induct)
  (auto simp: upd_list_simps inorder_baliL inorder_baliR)

lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by(simp add: update_def inorder_upd inorder_paint)

lemma inorder_del:
 "sorted1(inorder t1) \<Longrightarrow>  inorder(del x t1) = del_list x (inorder t1)" and
 "sorted1(inorder t1) \<Longrightarrow>  inorder(delL x t1 a t2) =
    del_list x (inorder t1) @ a # inorder t2" and
 "sorted1(inorder t2) \<Longrightarrow>  inorder(delR x t1 a t2) =
    inorder t1 @ a # del_list x (inorder t2)"
by(induction x t1 and x t1 a t2 and x t1 a t2 rule: del_delL_delR.induct)
  (auto simp: del_list_simps inorder_combine inorder_baldL inorder_baldR)

lemma inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del inorder_paint)

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
