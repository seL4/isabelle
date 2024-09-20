(* Author: Tobias Nipkow *)

section \<open>2-3-4 Trees\<close>

theory Tree234
imports Main
begin

class height =
fixes height :: "'a \<Rightarrow> nat"

datatype 'a tree234 =
  Leaf (\<open>\<langle>\<rangle>\<close>) |
  Node2 "'a tree234" 'a "'a tree234"  (\<open>\<langle>_, _, _\<rangle>\<close>) |
  Node3 "'a tree234" 'a "'a tree234" 'a "'a tree234"  (\<open>\<langle>_, _, _, _, _\<rangle>\<close>) |
  Node4 "'a tree234" 'a "'a tree234" 'a "'a tree234" 'a "'a tree234"
    (\<open>\<langle>_, _, _, _, _, _, _\<rangle>\<close>)

fun inorder :: "'a tree234 \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder(Node2 l a r) = inorder l @ a # inorder r" |
"inorder(Node3 l a m b r) = inorder l @ a # inorder m @ b # inorder r" |
"inorder(Node4 l a m b n c r) = inorder l @ a # inorder m @ b # inorder n @ c # inorder r"


instantiation tree234 :: (type)height
begin

fun height_tree234 :: "'a tree234 \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node2 l _ r) = Suc(max (height l) (height r))" |
"height (Node3 l _ m _ r) = Suc(max (height l) (max (height m) (height r)))" |
"height (Node4 l _ m _ n _ r) = Suc(max (height l) (max (height m) (max (height n) (height r))))"

instance ..

end

text\<open>Balanced:\<close>
fun bal :: "'a tree234 \<Rightarrow> bool" where
"bal Leaf = True" |
"bal (Node2 l _ r) = (bal l & bal r & height l = height r)" |
"bal (Node3 l _ m _ r) = (bal l & bal m & bal r & height l = height m & height m = height r)" |
"bal (Node4 l _ m _ n _ r) = (bal l & bal m & bal n & bal r & height l = height m & height m = height n & height n = height r)"

end
