(* Author: Tobias Nipkow *)

section \<open>Function \textit{isin} for Tree2\<close>

theory Isin2
imports
  Tree2
  Cmp
  Set_Specs
begin

fun isin :: "('a::linorder,'b) tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l a _ r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin r x)"

lemma isin_set_inorder: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set(inorder t))"
by (induction t) (auto simp: isin_simps)

lemma isin_set_tree: "bst t \<Longrightarrow> isin t x \<longleftrightarrow> x \<in> set_tree t"
by(induction t) auto

end
