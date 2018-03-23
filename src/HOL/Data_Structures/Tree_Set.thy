(* Author: Tobias Nipkow *)

section \<open>Unbalanced Tree Implementation of Set\<close>

theory Tree_Set
imports
  "HOL-Library.Tree"
  Cmp
  Set_by_Ordered
begin

fun isin :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l a r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin r x)"

hide_const (open) insert

fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x Leaf = Node Leaf x Leaf" |
"insert x (Node l a r) =
  (case cmp x a of
     LT \<Rightarrow> Node (insert x l) a r |
     EQ \<Rightarrow> Node l a r |
     GT \<Rightarrow> Node l a (insert x r))"

fun del_min :: "'a tree \<Rightarrow> 'a * 'a tree" where
"del_min (Node l a r) =
  (if l = Leaf then (a,r) else let (x,l') = del_min l in (x, Node l' a r))"

fun delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete x Leaf = Leaf" |
"delete x (Node l a r) =
  (case cmp x a of
     LT \<Rightarrow>  Node (delete x l) a r |
     GT \<Rightarrow>  Node l a (delete x r) |
     EQ \<Rightarrow> if r = Leaf then l else let (a',r') = del_min r in Node l a' r')"


subsection "Functional Correctness Proofs"

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set (inorder t))"
by (induction t) (auto simp: isin_simps)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps)


lemma del_minD:
  "del_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x # inorder t' = inorder t"
by(induction t arbitrary: t' rule: del_min.induct)
  (auto simp: sorted_lems split: prod.splits if_splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t) (auto simp: del_list_simps del_minD split: prod.splits)

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
qed (rule TrueI)+

end
