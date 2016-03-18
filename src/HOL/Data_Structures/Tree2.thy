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

definition size1 :: "('a,'b) tree \<Rightarrow> nat" where
"size1 t = size t + 1"

lemma size1_simps[simp]:
  "size1 \<langle>\<rangle> = 1"
  "size1 \<langle>u, l, x, r\<rangle> = size1 l + size1 r"
by (simp_all add: size1_def)

lemma size1_ge0[simp]: "0 < size1 t"
by (simp add: size1_def)

end
