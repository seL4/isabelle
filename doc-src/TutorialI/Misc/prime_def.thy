(*<*)
theory prime_def = Main:;
consts prime :: "nat \\<Rightarrow> bool"
(*>*)
text{*
\begin{warn}
A common mistake when writing definitions is to introduce extra free
variables on the right-hand side as in the following fictitious definition:
@{term[display,quotes]"prime(p) == 1 < p & (m dvd p --> (m=1 | m=p))"}
where @{text"dvd"} means ``divides''.
Isabelle rejects this ``definition'' because of the extra @{term"m"} on the
right-hand side, which would introduce an inconsistency (why?). What you
should have written is
@{term[display,quotes]"prime(p) == 1 < p & (!m. m dvd p --> (m=1 | m=p))"}
\end{warn}
*}
(*<*)
end
(*>*)
