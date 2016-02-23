theory Tree2
imports Main
begin

datatype ('a,'b) tree =
  Leaf ("\<langle>\<rangle>") |
  Node 'b "('a,'b)tree" 'a "('a,'b) tree" ("(1\<langle>_,/ _,/ _,/ _\<rangle>)")

fun inorder :: "('a,'b)tree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node _ l a r) = inorder l @ a # inorder r"

fun height :: "('a,'b) tree \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node _ l a r) = max (height l) (height r) + 1"

end
