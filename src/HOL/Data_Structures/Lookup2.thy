(* Author: Tobias Nipkow *)

section \<open>Function \textit{lookup} for Tree2\<close>

theory Lookup2
imports
  Tree2
  Map_by_Ordered
begin

fun lookup :: "('a::linorder * 'b, 'c) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node _ l (a,b) r) x =
  (if x < a then lookup l x else
   if x > a then lookup r x else Some b)"

lemma lookup_eq:
  "sorted1(inorder t) \<Longrightarrow> lookup t x = map_of (inorder t) x"
by(induction t) (auto simp: map_of_simps split: option.split)

end