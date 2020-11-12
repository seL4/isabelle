section \<open>Augmented Tree (Tree2)\<close>

theory Tree2
imports "HOL-Library.Tree"
begin

text \<open>This theory provides the basic infrastructure for the type @{typ \<open>('a * 'b) tree\<close>}
of augmented trees where @{typ 'a} is the key and @{typ 'b} some additional information.\<close>

text \<open>IMPORTANT: Inductions and cases analyses on augmented trees need to use the following
two rules explicitly. They generate nodes of the form @{term "Node l (a,b) r"}
rather than @{term "Node l a r"} for trees of type @{typ "'a tree"}.\<close>

lemmas tree2_induct = tree.induct[where 'a = "'a * 'b", split_format(complete)]

lemmas tree2_cases = tree.exhaust[where 'a = "'a * 'b", split_format(complete)]

fun inorder :: "('a*'b)tree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node l (a,_) r) = inorder l @ a # inorder r"

fun set_tree :: "('a*'b) tree \<Rightarrow> 'a set" where
"set_tree Leaf = {}" |
"set_tree (Node l (a,_) r) = {a} \<union> set_tree l \<union> set_tree r"

fun bst :: "('a::linorder*'b) tree \<Rightarrow> bool" where
"bst Leaf = True" |
"bst (Node l (a, _) r) = ((\<forall>x \<in> set_tree l. x < a) \<and> (\<forall>x \<in> set_tree r. a < x) \<and> bst l \<and> bst r)"

lemma finite_set_tree[simp]: "finite(set_tree t)"
by(induction t) auto

lemma eq_set_tree_empty[simp]: "set_tree t = {} \<longleftrightarrow> t = Leaf"
by (cases t) auto

lemma set_inorder[simp]: "set (inorder t) = set_tree t"
by (induction t) auto

lemma length_inorder[simp]: "length (inorder t) = size t"
by (induction t) auto

end
