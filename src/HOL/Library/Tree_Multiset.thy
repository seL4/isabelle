(* Author: Tobias Nipkow *)

section {* Multiset of Elements of Binary Tree *}

theory Tree_Multiset
imports Multiset Tree
begin

text{* Kept separate from theory @{theory Tree} to avoid importing all of
theory @{theory Multiset} into @{theory Tree}. Should be merged if
@{theory Multiset} ever becomes part of @{theory Main}. *}

fun mset_tree :: "'a tree \<Rightarrow> 'a multiset" where
"mset_tree Leaf = {#}" |
"mset_tree (Node l a r) = {#a#} + mset_tree l + mset_tree r"

lemma set_of_mset_tree[simp]: "set_of (mset_tree t) = set_tree t"
by(induction t) auto

lemma size_mset_tree[simp]: "size(mset_tree t) = size t"
by(induction t) auto

lemma mset_map_tree: "mset_tree (map_tree f t) = image_mset f (mset_tree t)"
by (induction t) auto

lemma multiset_of_preorder[simp]: "multiset_of (preorder t) = mset_tree t"
by (induction t) (auto simp: ac_simps)

lemma multiset_of_inorder[simp]: "multiset_of (inorder t) = mset_tree t"
by (induction t) (auto simp: ac_simps)

lemma map_mirror: "mset_tree (mirror t) = mset_tree t"
by (induction t) (simp_all add: ac_simps)

lemma del_rightmost_mset_tree:
  "\<lbrakk> del_rightmost t = (t',x);  t \<noteq> \<langle>\<rangle> \<rbrakk> \<Longrightarrow> mset_tree t = {#x#} + mset_tree t'"
apply(induction t arbitrary: t' rule: del_rightmost.induct)
by (auto split: prod.splits) (auto simp: ac_simps)

end
