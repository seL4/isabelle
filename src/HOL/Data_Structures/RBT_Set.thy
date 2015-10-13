(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Sets\<close>

theory RBT_Set
imports
  RBT
  Isin2
begin

fun insert :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"insert x Leaf = R Leaf x Leaf" |
"insert x (B l a r) =
  (if x < a then bal (insert x l) a r else
   if x > a then bal l a (insert x r) else B l a r)" |
"insert x (R l a r) =
  (if x < a then R (insert x l) a r
   else if x > a then R l a (insert x r) else R l a r)"

fun delete :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and deleteL :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and deleteR :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
where
"delete x Leaf = Leaf" |
"delete x (Node _ l a r) = 
  (if x < a then deleteL x l a r 
   else if x > a then deleteR x l a r else combine l r)" |
"deleteL x (B t1 a t2) b t3 = balL (delete x (B t1 a t2)) b t3" |
"deleteL x l a r = R (delete x l) a r" |
"deleteR x t1 a (B t2 b t3) = balR t1 a (delete x (B t2 b t3))" | 
"deleteR x l a r = R l a (delete x r)"


subsection "Functional Correctness Proofs"

lemma inorder_bal:
  "inorder(bal l a r) = inorder l @ a # inorder r"
by(induction l a r rule: bal.induct) (auto)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert a t) = ins_list a (inorder t)"
by(induction a t rule: insert.induct) (auto simp: ins_list_simps inorder_bal)

lemma inorder_red: "inorder(red t) = inorder t"
by(induction t) (auto)

lemma inorder_balL:
  "inorder(balL l a r) = inorder l @ a # inorder r"
by(induction l a r rule: balL.induct)(auto simp: inorder_bal inorder_red)

lemma inorder_balR:
  "inorder(balR l a r) = inorder l @ a # inorder r"
by(induction l a r rule: balR.induct) (auto simp: inorder_bal inorder_red)

lemma inorder_combine:
  "inorder(combine l r) = inorder l @ inorder r"
by(induction l r rule: combine.induct)
  (auto simp: inorder_balL inorder_balR split: tree.split color.split)

lemma inorder_delete:
 "sorted(inorder t) \<Longrightarrow>  inorder(delete x t) = del_list x (inorder t)" and
 "sorted(inorder l) \<Longrightarrow>  inorder(deleteL x l a r) =
    del_list x (inorder l) @ a # inorder r" and
 "sorted(inorder r) \<Longrightarrow>  inorder(deleteR x l a r) =
    inorder l @ a # del_list x (inorder r)"
by(induction x t and x l a r and x l a r rule: delete_deleteL_deleteR.induct)
  (auto simp: del_list_simps inorder_combine inorder_balL inorder_balR)

interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and wf = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed (rule TrueI)+

end
