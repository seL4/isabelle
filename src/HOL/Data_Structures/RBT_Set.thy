(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree Implementation of Sets\<close>

theory RBT_Set
imports
  RBT
  Cmp
  Isin2
begin

fun ins :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"ins x Leaf = R Leaf x Leaf" |
"ins x (B l a r) =
  (case cmp x a of
     LT \<Rightarrow> bal (ins x l) a r |
     GT \<Rightarrow> bal l a (ins x r) |
     EQ \<Rightarrow> B l a r)" |
"ins x (R l a r) =
  (case cmp x a of
    LT \<Rightarrow> R (ins x l) a r |
    GT \<Rightarrow> R l a (ins x r) |
    EQ \<Rightarrow> R l a r)"

definition insert :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"insert x t = paint Black (ins x t)"

fun del :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and delL :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
and delR :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt"
where
"del x Leaf = Leaf" |
"del x (Node _ l a r) =
  (case cmp x a of
     LT \<Rightarrow> delL x l a r |
     GT \<Rightarrow> delR x l a r |
     EQ \<Rightarrow> combine l r)" |
"delL x (B t1 a t2) b t3 = balL (del x (B t1 a t2)) b t3" |
"delL x l a r = R (del x l) a r" |
"delR x t1 a (B t2 b t3) = balR t1 a (del x (B t2 b t3))" | 
"delR x l a r = R l a (del x r)"

definition delete :: "'a::cmp \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"delete x t = paint Black (del x t)"


subsection "Functional Correctness Proofs"

lemma inorder_paint: "inorder(paint c t) = inorder t"
by(induction t) (auto)

lemma inorder_bal:
  "inorder(bal l a r) = inorder l @ a # inorder r"
by(induction l a r rule: bal.induct) (auto)

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(ins x t) = ins_list x (inorder t)"
by(induction x t rule: ins.induct) (auto simp: ins_list_simps inorder_bal)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by (simp add: insert_def inorder_ins inorder_paint)

lemma inorder_balL:
  "inorder(balL l a r) = inorder l @ a # inorder r"
by(induction l a r rule: balL.induct)(auto simp: inorder_bal inorder_paint)

lemma inorder_balR:
  "inorder(balR l a r) = inorder l @ a # inorder r"
by(induction l a r rule: balR.induct) (auto simp: inorder_bal inorder_paint)

lemma inorder_combine:
  "inorder(combine l r) = inorder l @ inorder r"
by(induction l r rule: combine.induct)
  (auto simp: inorder_balL inorder_balR split: tree.split color.split)

lemma inorder_del:
 "sorted(inorder t) \<Longrightarrow>  inorder(del x t) = del_list x (inorder t)"
 "sorted(inorder l) \<Longrightarrow>  inorder(delL x l a r) =
    del_list x (inorder l) @ a # inorder r"
 "sorted(inorder r) \<Longrightarrow>  inorder(delR x l a r) =
    inorder l @ a # del_list x (inorder r)"
by(induction x t and x l a r and x l a r rule: del_delL_delR.induct)
  (auto simp: del_list_simps inorder_combine inorder_balL inorder_balR)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by (auto simp: delete_def inorder_del inorder_paint)


interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed auto

end
