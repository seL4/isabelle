(* Author: Tobias Nipkow *)

header {* Binary Tree *}

theory Tree
imports Main
begin

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun set_tree :: "'a tree \<Rightarrow> 'a set" where
"set_tree Leaf = {}" |
"set_tree (Node l x r) = insert x (set_tree l \<union> set_tree r)"

fun subtrees :: "'a tree \<Rightarrow> 'a tree set" where
"subtrees Leaf = {Leaf}" |
"subtrees (Node l a r) = insert (Node l a r) (subtrees l \<union> subtrees r)"

fun inorder :: "'a tree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node l x r) = inorder l @ [x] @ inorder r"

text{* Binary Search Tree predicate: *}
fun bst :: "'a::linorder tree \<Rightarrow> bool" where
"bst Leaf = True" |
"bst (Node l a r) =
  (bst l & bst r & (\<forall>x \<in> set_tree l. x < a)  & (\<forall>x \<in> set_tree r. a < x))"

lemma neq_Leaf_iff: "(t \<noteq> Leaf) = (\<exists>l a r. t = Node l a r)"
by (cases t) auto

lemma set_inorder[simp]: "set(inorder t) = set_tree t"
by (induction t) auto

lemma set_treeE: "a : set_tree t \<Longrightarrow> \<exists>l r. Node l a r \<in> subtrees t"
by(induction t)(auto)

lemma Node_notin_subtrees_if[simp]:
  "a \<notin> set_tree t \<Longrightarrow> Node l a r \<notin> subtrees t"
by (induction t) auto

lemma in_set_tree_if:
  "Node l a r \<in> subtrees t \<Longrightarrow> a \<in> set_tree t"
by (metis Node_notin_subtrees_if)

end
