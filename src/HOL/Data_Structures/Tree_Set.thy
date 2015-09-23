(* Author: Tobias Nipkow *)

section {* Tree Implementation of Sets *}

theory Tree_Set
imports
  "~~/src/HOL/Library/Tree"
  Set_by_Ordered
begin

fun isin :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l a r) x = (x < a \<and> isin l x \<or> x=a \<or> isin r x)"

hide_const (open) insert

fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert a Leaf = Node Leaf a Leaf" |
"insert a (Node l x r) =
   (if a < x then Node (insert a l) x r
    else if a=x then Node l x r
    else Node l x (insert a r))"

fun del_min :: "'a tree \<Rightarrow> 'a * 'a tree" where
"del_min (Node Leaf a r) = (a, r)" |
"del_min (Node l a r) = (let (x,l') = del_min l in (x, Node l' a r))"

fun delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete k Leaf = Leaf" |
"delete k (Node l a r) = (if k<a then Node (delete k l) a r else
  if k > a then Node l a (delete k r) else
  if r = Leaf then l else let (a',r') = del_min r in Node l a' r')"


subsection "Functional Correctness Proofs"

lemma "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> elems (inorder t))"
by (induction t) (auto simp: elems_simps1)

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> elems (inorder t))"
by (induction t) (auto simp: elems_simps2)


lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps)


lemma del_minD:
  "del_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> sorted(inorder t) \<Longrightarrow>
   x # inorder t' = inorder t"
by(induction t arbitrary: t' rule: del_min.induct)
  (auto simp: sorted_lems split: prod.splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t) (auto simp: del_list_simps del_minD split: prod.splits)


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
next
  case 5 thus ?case by(simp)
qed

end
