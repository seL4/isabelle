theory Tree2
imports Main
begin

datatype ('a,'b) tree =
  Leaf ("\<langle>\<rangle>") |
  Node "('a,'b)tree" 'a 'b "('a,'b) tree" ("(1\<langle>_,/ _,/ _,/ _\<rangle>)")

fun inorder :: "('a,'b)tree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node l a _ r) = inorder l @ a # inorder r"

fun height :: "('a,'b) tree \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node l a _ r) = max (height l) (height r) + 1"

fun set_tree :: "('a,'b) tree \<Rightarrow> 'a set" where
"set_tree Leaf = {}" |
"set_tree (Node l a _ r) = Set.insert a (set_tree l \<union> set_tree r)"

fun bst :: "('a::linorder,'b) tree \<Rightarrow> bool" where
"bst Leaf = True" |
"bst (Node l a _ r) = (bst l \<and> bst r \<and> (\<forall>x \<in> set_tree l. x < a) \<and> (\<forall>x \<in> set_tree r. a < x))"

definition size1 :: "('a,'b) tree \<Rightarrow> nat" where
"size1 t = size t + 1"

lemma size1_simps[simp]:
  "size1 \<langle>\<rangle> = 1"
  "size1 \<langle>l, x, u, r\<rangle> = size1 l + size1 r"
by (simp_all add: size1_def)

lemma size1_ge0[simp]: "0 < size1 t"
by (simp add: size1_def)

lemma finite_set_tree[simp]: "finite(set_tree t)"
by(induction t) auto

end
