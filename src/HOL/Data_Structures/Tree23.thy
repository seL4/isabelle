(* Author: Tobias Nipkow *)

section \<open>2-3 Trees\<close>

theory Tree23
imports Main
begin

class height =
fixes height :: "'a \<Rightarrow> nat"

datatype 'a tree23 =
  Leaf ("\<langle>\<rangle>") |
  Node2 "'a tree23" 'a "'a tree23"  ("\<langle>_, _, _\<rangle>") |
  Node3 "'a tree23" 'a "'a tree23" 'a "'a tree23"  ("\<langle>_, _, _, _, _\<rangle>")

fun inorder :: "'a tree23 \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder(Node2 l a r) = inorder l @ a # inorder r" |
"inorder(Node3 l a m b r) = inorder l @ a # inorder m @ b # inorder r"


instantiation tree23 :: (type)height
begin

fun height_tree23 :: "'a tree23 \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node2 l _ r) = Suc(max (height l) (height r))" |
"height (Node3 l _ m _ r) = Suc(max (height l) (max (height m) (height r)))"

instance ..

end

text \<open>Completeness:\<close>

fun complete :: "'a tree23 \<Rightarrow> bool" where
"complete Leaf = True" |
"complete (Node2 l _ r) = (complete l & complete r & height l = height r)" |
"complete (Node3 l _ m _ r) =
  (complete l & complete m & complete r & height l = height m & height m = height r)"

lemma ht_sz_if_complete: "complete t \<Longrightarrow> 2 ^ height t \<le> size t + 1"
by (induction t) auto

end
