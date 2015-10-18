(* Author: Tobias Nipkow *)

section \<open>2-3 Trees\<close>

theory Tree23
imports Main
begin

class height =
fixes height :: "'a \<Rightarrow> nat"

datatype 'a tree23 =
  Leaf |
  Node2 "'a tree23" 'a "'a tree23" |
  Node3 "'a tree23" 'a "'a tree23" 'a "'a tree23"

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

text \<open>Balanced:\<close>

fun bal :: "'a tree23 \<Rightarrow> bool" where
"bal Leaf = True" |
"bal (Node2 l _ r) = (bal l & bal r & height l = height r)" |
"bal (Node3 l _ m _ r) =
  (bal l & bal m & bal r & height l = height m & height m = height r)"

end
