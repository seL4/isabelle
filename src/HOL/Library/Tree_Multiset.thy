(* Author: Tobias Nipkow *)

section \<open>Multiset of Elements of Binary Tree\<close>

theory Tree_Multiset
imports Multiset Tree
begin

text \<open>
  Kept separate from theory \<^theory>\<open>HOL-Library.Tree\<close> to avoid importing all of theory \<^theory>\<open>HOL-Library.Multiset\<close> into \<^theory>\<open>HOL-Library.Tree\<close>. Should be merged if \<^theory>\<open>HOL-Library.Multiset\<close> ever becomes part of \<^theory>\<open>Main\<close>.
\<close>

fun mset_tree :: "'a tree \<Rightarrow> 'a multiset" where
"mset_tree Leaf = {#}" |
"mset_tree (Node l a r) = {#a#} + mset_tree l + mset_tree r"

fun subtrees_mset :: "'a tree \<Rightarrow> 'a tree multiset" where
"subtrees_mset Leaf = {#Leaf#}" |
"subtrees_mset (Node l x r) = add_mset (Node l x r) (subtrees_mset l + subtrees_mset r)"


lemma mset_tree_empty_iff[simp]: "mset_tree t = {#} \<longleftrightarrow> t = Leaf"
by (cases t) auto

lemma set_mset_tree[simp]: "set_mset (mset_tree t) = set_tree t"
by(induction t) auto

lemma size_mset_tree[simp]: "size(mset_tree t) = size t"
by(induction t) auto

lemma mset_map_tree: "mset_tree (map_tree f t) = image_mset f (mset_tree t)"
by (induction t) auto

lemma mset_iff_set_tree: "x \<in># mset_tree t \<longleftrightarrow> x \<in> set_tree t"
by(induction t arbitrary: x) auto

lemma mset_preorder[simp]: "mset (preorder t) = mset_tree t"
by (induction t) (auto simp: ac_simps)

lemma mset_inorder[simp]: "mset (inorder t) = mset_tree t"
by (induction t) (auto simp: ac_simps)

lemma map_mirror: "mset_tree (mirror t) = mset_tree t"
by (induction t) (simp_all add: ac_simps)

lemma in_subtrees_mset_iff[simp]: "s \<in># subtrees_mset t \<longleftrightarrow> s \<in> subtrees t"
by(induction t) auto

end
