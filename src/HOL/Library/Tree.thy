(* Author: Tobias Nipkow *)

header {* Binary Tree *}

theory Tree
imports Main
begin

datatype_new 'a tree = Leaf | Node (left: "'a tree") (val: 'a) (right: "'a tree")
  where
    "left Leaf = Leaf"
  | "right Leaf = Leaf"

lemma neq_Leaf_iff: "(t \<noteq> Leaf) = (\<exists>l a r. t = Node l a r)"
by (cases t) auto

fun subtrees :: "'a tree \<Rightarrow> 'a tree set" where
"subtrees Leaf = {Leaf}" |
"subtrees (Node l a r) = insert (Node l a r) (subtrees l \<union> subtrees r)"

lemma set_treeE: "a \<in> set_tree t \<Longrightarrow> \<exists>l r. Node l a r \<in> subtrees t"
  by (induction t)(auto)

lemma Node_notin_subtrees_if[simp]:
  "a \<notin> set_tree t \<Longrightarrow> Node l a r \<notin> subtrees t"
  by (induction t) auto

lemma in_set_tree_if:
  "Node l a r \<in> subtrees t \<Longrightarrow> a \<in> set_tree t"
  by (metis Node_notin_subtrees_if)

fun inorder :: "'a tree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node l x r) = inorder l @ [x] @ inorder r"

lemma set_inorder[simp]: "set (inorder t) = set_tree t"
  by (induction t) auto

subsection {* Binary Search Tree predicate *}

inductive bst :: "'a::linorder tree \<Rightarrow> bool" where
Leaf[intro!, simp]: "bst Leaf" |
Node: "bst l \<Longrightarrow> bst r \<Longrightarrow> (\<And>x. x \<in> set_tree l \<Longrightarrow> x < a) \<Longrightarrow> (\<And>x. x \<in> set_tree r \<Longrightarrow> a < x) \<Longrightarrow>
    bst (Node l a r)"

lemma bst_imp_sorted: "bst t \<Longrightarrow> sorted (inorder t)"
  by (induction rule: bst.induct) (auto simp: sorted_append sorted_Cons intro: less_imp_le less_trans)

end
