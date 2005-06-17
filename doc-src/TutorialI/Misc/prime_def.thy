(*<*)
theory prime_def imports Main begin;
consts prime :: "nat \<Rightarrow> bool"
(*>*)
text{*
\begin{warn}
A common mistake when writing definitions is to introduce extra free
variables on the right-hand side.  Consider the following, flawed definition
(where @{text"dvd"} means ``divides''):
@{term[display,quotes]"prime(p) == 1 < p & (m dvd p --> (m=1 | m=p))"}
\par\noindent\hangindent=0pt
Isabelle rejects this ``definition'' because of the extra @{term"m"} on the
right-hand side, which would introduce an inconsistency (why?). 
The correct version is
@{term[display,quotes]"prime(p) == 1 < p & (!m. m dvd p --> (m=1 | m=p))"}
\end{warn}
*}
(*<*)
end
(*>*)
