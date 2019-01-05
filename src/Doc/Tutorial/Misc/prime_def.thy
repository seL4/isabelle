(*<*)
theory prime_def imports Main begin
consts prime :: "nat \<Rightarrow> bool"
(*>*)
text\<open>
\begin{warn}
A common mistake when writing definitions is to introduce extra free
variables on the right-hand side.  Consider the following, flawed definition
(where \<open>dvd\<close> means ``divides''):
@{term[display,quotes]"prime(p) \<equiv> 1 < p \<and> (m dvd p \<longrightarrow> (m=1 \<or> m=p))"}
\par\noindent\hangindent=0pt
Isabelle rejects this ``definition'' because of the extra \<^term>\<open>m\<close> on the
right-hand side, which would introduce an inconsistency (why?). 
The correct version is
@{term[display,quotes]"prime(p) \<equiv> 1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> (m=1 \<or> m=p))"}
\end{warn}
\<close>
(*<*)
end
(*>*)
