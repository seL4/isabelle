(*<*)
theory appendix = Main:;
(*>*)

text{*
\begin{table}[htbp]
\begin{center}
\begin{tabular}{lll}
Constant & Type & Syntax \\
\hline
@{term 0} & @{text "'a::zero"} \\
@{text"+"} & @{text "('a::plus) \<Rightarrow> 'a \<Rightarrow> 'a"} & (infixl 65) \\
@{text"-"} & @{text "('a::minus) \<Rightarrow> 'a \<Rightarrow> 'a"} &  (infixl 65) \\
@{text"-"} & @{text "('a::minus) \<Rightarrow> 'a"} \\
@{text"*"} & @{text "('a::times) \<Rightarrow> 'a \<Rightarrow> 'a"} & (infixl 70) \\
@{text div} & @{text "('a::div) \<Rightarrow> 'a \<Rightarrow> 'a"} & (infixl 70) \\
@{text mod} & @{text "('a::div) \<Rightarrow> 'a \<Rightarrow> 'a"} & (infixl 70) \\
@{text dvd} & @{text "('a::times) \<Rightarrow> 'a \<Rightarrow> bool"} & (infixl 50) \\
@{text"/"}  & @{text "('a::inverse) \<Rightarrow> 'a \<Rightarrow> 'a"} & (infixl 70) \\
@{text"^"} & @{text "('a::power) \<Rightarrow> nat \<Rightarrow> 'a"} & (infixr 80) \\
@{term abs} &  @{text "('a::minus) \<Rightarrow> 'a"} & ${\mid} x {\mid}$\\
@{text"\<le>"} & @{text "('a::ord) \<Rightarrow> 'a \<Rightarrow> bool"} & (infixl 50) \\
@{text"<"} & @{text "('a::ord) \<Rightarrow> 'a \<Rightarrow> bool"} & (infixl 50) \\
@{term min} &  @{text "('a::ord) \<Rightarrow> 'a \<Rightarrow> 'a"} \\
@{term max} &  @{text "('a::ord) \<Rightarrow> 'a \<Rightarrow> 'a"} \\
@{term Least} & @{text "('a::ord \<Rightarrow> bool) \<Rightarrow> 'a"} &
@{text LEAST}$~x.~P$
\end{tabular}
\caption{Overloaded Constants in HOL}
\label{tab:overloading}
\end{center}
\end{table}
*}

(*<*)
end
(*>*)
