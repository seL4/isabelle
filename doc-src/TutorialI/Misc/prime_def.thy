(*<*)
theory prime_def = Main:;
consts prime :: "nat \\<Rightarrow> bool"
(*>*)
(*<*)term(*>*)

    "prime(p) \\<equiv> 1 < p \\<and> (m dvd p \\<longrightarrow> (m=1 \\<or> m=p))";
text{*\noindent\small
where \isa{dvd} means ``divides''.
Isabelle rejects this ``definition'' because of the extra \isa{m} on the
right-hand side, which would introduce an inconsistency (why?). What you
should have written is
*}
(*<*)term(*>*)
 "prime(p) \\<equiv> 1 < p \\<and> (\\<forall>m. m dvd p \\<longrightarrow> (m=1 \\<or> m=p))"
(*<*)
end
(*>*)
