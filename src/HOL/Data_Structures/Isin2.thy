(* Author: Tobias Nipkow *)

section \<open>Function \textit{isin} for Tree2\<close>

theory Isin2
imports
  Tree2
  Cmp
  Set_Interfaces
begin

fun isin :: "('a::linorder,'b) tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node _ l a r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin r x)"

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set(inorder t))"
by (induction t) (auto simp: isin_simps)

end
