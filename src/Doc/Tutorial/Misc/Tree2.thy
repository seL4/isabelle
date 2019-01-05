(*<*)
theory Tree2 imports Tree begin
(*>*)

text\<open>\noindent In Exercise~\ref{ex:Tree} we defined a function
\<^term>\<open>flatten\<close> from trees to lists. The straightforward version of
\<^term>\<open>flatten\<close> is based on \<open>@\<close> and is thus, like \<^term>\<open>rev\<close>,
quadratic. A linear time version of \<^term>\<open>flatten\<close> again reqires an extra
argument, the accumulator. Define\<close>
(*<*)primrec(*>*)flatten2 :: "'a tree \<Rightarrow> 'a list \<Rightarrow> 'a list"(*<*)where
"flatten2 Tip xs = xs" |
"flatten2 (Node l x r) xs = flatten2 l (x#(flatten2 r xs))"
(*>*)

text\<open>\noindent and prove\<close>
(*<*)
lemma [simp]: "\<forall>xs. flatten2 t xs = flatten t @ xs"
apply(induct_tac t)
by(auto)
(*>*)
lemma "flatten2 t [] = flatten t"
(*<*)
by(simp)

end
(*>*)
