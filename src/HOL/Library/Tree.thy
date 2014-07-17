(* Author: Tobias Nipkow *)

header {* Binary Tree *}

theory Tree
imports Main
begin

datatype_new 'a tree = Leaf | Node (left: "'a tree") (val: 'a) (right: "'a tree")
  where
    "left Leaf = Leaf"
  | "right Leaf = Leaf"
datatype_compat tree

lemma neq_Leaf_iff: "(t \<noteq> Leaf) = (\<exists>l a r. t = Node l a r)"
  by (cases t) auto

lemma set_tree_Node2: "set_tree(Node l x r) = insert x (set_tree l \<union> set_tree r)"
by auto

fun subtrees :: "'a tree \<Rightarrow> 'a tree set" where
  "subtrees Leaf = {Leaf}" |
  "subtrees (Node l a r) = insert (Node l a r) (subtrees l \<union> subtrees r)"

lemma set_treeE: "a \<in> set_tree t \<Longrightarrow> \<exists>l r. Node l a r \<in> subtrees t"
  by (induction t)(auto)

lemma Node_notin_subtrees_if[simp]: "a \<notin> set_tree t \<Longrightarrow> Node l a r \<notin> subtrees t"
  by (induction t) auto

lemma in_set_tree_if: "Node l a r \<in> subtrees t \<Longrightarrow> a \<in> set_tree t"
  by (metis Node_notin_subtrees_if)

fun inorder :: "'a tree \<Rightarrow> 'a list" where
  "inorder Leaf = []" |
  "inorder (Node l x r) = inorder l @ [x] @ inorder r"

lemma set_inorder[simp]: "set (inorder t) = set_tree t"
  by (induction t) auto

subsection {* Binary Search Tree predicate *}

fun (in linorder) bst :: "'a tree \<Rightarrow> bool" where
  "bst Leaf \<longleftrightarrow> True" |
  "bst (Node l a r) \<longleftrightarrow> bst l \<and> bst r \<and> (\<forall>x\<in>set_tree l. x < a) \<and> (\<forall>x\<in>set_tree r. a < x)"

lemma (in linorder) bst_imp_sorted: "bst t \<Longrightarrow> sorted (inorder t)"
  by (induction t) (auto simp: sorted_append sorted_Cons intro: less_imp_le less_trans)

end
