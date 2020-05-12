(* Author: Tobias Nipkow *)

section \<open>Unbalanced Tree Implementation of Set\<close>

theory Tree_Set
imports
  "HOL-Library.Tree"
  Cmp
  Set_Specs
begin

definition empty :: "'a tree" where
"empty = Leaf"

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

text \<open>Deletion by replacing:\<close>

fun split_min :: "'a tree \<Rightarrow> 'a * 'a tree" where
"split_min (Node l a r) =
  (if l = Leaf then (a,r) else let (x,l') = split_min l in (x, Node l' a r))"

fun delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete x Leaf = Leaf" |
"delete x (Node l a r) =
  (case cmp x a of
     LT \<Rightarrow>  Node (delete x l) a r |
     GT \<Rightarrow>  Node l a (delete x r) |
     EQ \<Rightarrow> if r = Leaf then l else let (a',r') = split_min r in Node l a' r')"

text \<open>Deletion by joining:\<close>

fun join :: "('a::linorder)tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"join t Leaf = t" |
"join Leaf t = t" |
"join (Node t1 a t2) (Node t3 b t4) =
  (case join t2 t3 of
     Leaf \<Rightarrow> Node t1 a (Node Leaf b t4) |
     Node u2 x u3 \<Rightarrow> Node (Node t1 a u2) x (Node u3 b t4))"

fun delete2 :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete2 x Leaf = Leaf" |
"delete2 x (Node l a r) =
  (case cmp x a of
     LT \<Rightarrow>  Node (delete2 x l) a r |
     GT \<Rightarrow>  Node l a (delete2 x r) |
     EQ \<Rightarrow> join l r)"


subsection "Functional Correctness Proofs"

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set (inorder t))"
by (induction t) (auto simp: isin_simps)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps)


lemma split_minD:
  "split_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x # inorder t' = inorder t"
by(induction t arbitrary: t' rule: split_min.induct)
  (auto simp: sorted_lems split: prod.splits if_splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t) (auto simp: del_list_simps split_minD split: prod.splits)

interpretation S: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed (rule TrueI)+

lemma inorder_join:
  "inorder(join l r) = inorder l @ inorder r"
by(induction l r rule: join.induct) (auto split: tree.split)

lemma inorder_delete2:
  "sorted(inorder t) \<Longrightarrow> inorder(delete2 x t) = del_list x (inorder t)"
by(induction t) (auto simp: inorder_join del_list_simps)

interpretation S2: Set_by_Ordered
where empty = empty and isin = isin and insert = insert and delete = delete2
and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete2)
qed (rule TrueI)+

end
