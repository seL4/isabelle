(*<*)
theory Plus = Main:
(*>*)

text{*\noindent Define the following addition function *}

consts plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
primrec
"plus m 0 = m"
"plus m (Suc n) = plus (Suc m) n"

text{*\noindent and prove*}
(*<*)
lemma [simp]: "!m. plus m n = m+n"
apply(induct_tac n)
by(auto)
(*>*)
lemma "plus m n = m+n"
(*<*)
by(simp)

end
(*>*)
