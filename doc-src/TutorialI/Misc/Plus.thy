(*<*)
theory Plus imports Main begin
(*>*)

text{*\noindent Define the following addition function *}

primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add m 0 = m" |
"add m (Suc n) = add (Suc m) n"

text{*\noindent and prove*}
(*<*)
lemma [simp]: "!m. add m n = m+n"
apply(induct_tac n)
by(auto)
(*>*)
lemma "add m n = m+n"
(*<*)
by(simp)

end
(*>*)
