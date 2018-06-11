(* Author: Tobias Nipkow *)

section \<open>Function \textit{lookup} for Tree2\<close>

theory Lookup2
imports
  Tree2
  Cmp
  Map_Specs
begin

fun lookup :: "('a::linorder * 'b, 'c) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node l (a,b) _ r) x =
  (case cmp x a of LT \<Rightarrow> lookup l x | GT \<Rightarrow> lookup r x | EQ \<Rightarrow> Some b)"

lemma lookup_map_of:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by(induction t) (auto simp: map_of_simps split: option.split)

end
