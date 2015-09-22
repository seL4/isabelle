(* Author: Tobias Nipkow *)

section \<open>Function \textit{isin} for Tree2\<close>

theory Isin2
imports
  Tree2
  Set_by_Ordered
begin

fun isin :: "('a,'b) tree \<Rightarrow> ('a::order) \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node _ l a r) x = (x < a \<and> isin l x \<or> x=a \<or> isin r x)"

lemma "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> elems(inorder t))"
by (induction t) (auto simp: elems_simps)

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> elems(inorder t))"
by (induction t) (auto simp: elems_simps dest: sortedD)

end