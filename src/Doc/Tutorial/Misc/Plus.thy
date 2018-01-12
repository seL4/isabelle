(*<*)
theory Plus imports Main begin
(*>*)

text\<open>\noindent Define the following addition function\<close>

primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add m 0 = m" |
"add m (Suc n) = add (Suc m) n"

text\<open>\noindent and prove\<close>
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
