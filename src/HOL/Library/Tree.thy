(* Author: Tobias Nipkow *)

header {* Binary Tree *}

theory Tree
imports Main
begin

datatype 'a tree = Leaf | Node (left: "'a tree") (val: 'a) (right: "'a tree")
  where
    "left Leaf = Leaf"
  | "right Leaf = Leaf"
datatype_compat tree

lemma neq_Leaf_iff: "(t \<noteq> Leaf) = (\<exists>l a r. t = Node l a r)"
  by (cases t) auto

lemma set_tree_Node2: "set_tree(Node l x r) = insert x (set_tree l \<union> set_tree r)"
by auto

lemma finite_set_tree[simp]: "finite(set_tree t)"
by(induction t) auto


subsection "The set of subtrees"

fun subtrees :: "'a tree \<Rightarrow> 'a tree set" where
  "subtrees Leaf = {Leaf}" |
  "subtrees (Node l a r) = insert (Node l a r) (subtrees l \<union> subtrees r)"

lemma set_treeE: "a \<in> set_tree t \<Longrightarrow> \<exists>l r. Node l a r \<in> subtrees t"
  by (induction t)(auto)

lemma Node_notin_subtrees_if[simp]: "a \<notin> set_tree t \<Longrightarrow> Node l a r \<notin> subtrees t"
  by (induction t) auto

lemma in_set_tree_if: "Node l a r \<in> subtrees t \<Longrightarrow> a \<in> set_tree t"
  by (metis Node_notin_subtrees_if)


subsection "Inorder list of entries"

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


subsection "Deletion of the rightmost entry"

fun del_rightmost :: "'a tree \<Rightarrow> 'a tree * 'a" where
"del_rightmost (Node l a Leaf) = (l,a)" |
"del_rightmost (Node l a r) = (let (r',x) = del_rightmost r in (Node l a r', x))"

lemma del_rightmost_set_tree_if_bst:
  "\<lbrakk> del_rightmost t = (t',x); bst t; t \<noteq> Leaf \<rbrakk>
  \<Longrightarrow> x \<in> set_tree t \<and> set_tree t' = set_tree t - {x}"
apply(induction t arbitrary: t' rule: del_rightmost.induct)
  apply (fastforce simp: ball_Un split: prod.splits)+
done

lemma del_rightmost_set_tree:
  "\<lbrakk> del_rightmost t = (t',x);  t \<noteq> Leaf \<rbrakk> \<Longrightarrow> set_tree t = insert x (set_tree t')"
apply(induction t arbitrary: t' rule: del_rightmost.induct)
by (auto split: prod.splits) auto

lemma del_rightmost_bst:
  "\<lbrakk> del_rightmost t = (t',x);  bst t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow> bst t'"
proof(induction t arbitrary: t' rule: del_rightmost.induct)
  case (2 l a rl b rr)
  let ?r = "Node rl b rr"
  from "2.prems"(1) obtain r' where 1: "del_rightmost ?r = (r',x)" and [simp]: "t' = Node l a r'"
    by(simp split: prod.splits)
  from "2.prems"(2) 1 del_rightmost_set_tree[OF 1] show ?case by(auto)(simp add: "2.IH")
qed auto


lemma del_rightmost_greater: "\<lbrakk> del_rightmost t = (t',x);  bst t;  t \<noteq> Leaf \<rbrakk>
  \<Longrightarrow> \<forall>a\<in>set_tree t'. a < x"
proof(induction t arbitrary: t' rule: del_rightmost.induct)
  case (2 l a rl b rr)
  from "2.prems"(1) obtain r'
  where dm: "del_rightmost (Node rl b rr) = (r',x)" and [simp]: "t' = Node l a r'"
    by(simp split: prod.splits)
  show ?case using "2.prems"(2) "2.IH"[OF dm] del_rightmost_set_tree_if_bst[OF dm]
    by (fastforce simp add: ball_Un)
qed simp_all

(* should be moved but metis not available in much of Main *)
lemma Max_insert1: "\<lbrakk> finite A;  \<forall>a\<in>A. a \<le> x \<rbrakk> \<Longrightarrow> Max(insert x A) = x"
by (metis Max_in Max_insert Max_singleton antisym max_def)

lemma del_rightmost_Max:
  "\<lbrakk> del_rightmost t = (t',x);  bst t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow> x = Max(set_tree t)"
by (metis Max_insert1 del_rightmost_greater del_rightmost_set_tree finite_set_tree less_le_not_le)

end
