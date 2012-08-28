(*<*)theory appendix
imports Main
begin(*>*)

text{*
\begin{table}[htbp]
\begin{center}
\begin{tabular}{lll}
Constant & Type & Syntax \\
\hline
@{term [source] 0} & @{typeof [show_sorts] "0"} \\
@{term [source] 1} & @{typeof [show_sorts] "1"} \\
@{term [source] plus} & @{typeof [show_sorts] "plus"} & (infixl $+$ 65) \\
@{term [source] minus} & @{typeof [show_sorts] "minus"} & (infixl $-$ 65) \\
@{term [source] uminus} & @{typeof [show_sorts] "uminus"} & $- x$ \\
@{term [source] times} & @{typeof [show_sorts] "times"} & (infixl $*$ 70) \\
@{term [source] divide} & @{typeof [show_sorts] "divide"} & (infixl $/$ 70) \\
@{term [source] Divides.div} & @{typeof [show_sorts] "Divides.div"} & (infixl $div$ 70) \\
@{term [source] Divides.mod} & @{typeof [show_sorts] "Divides.mod"} & (infixl $mod$ 70) \\
@{term [source] abs} & @{typeof [show_sorts] "abs"} & ${\mid} x {\mid}$ \\
@{term [source] sgn} & @{typeof [show_sorts] "sgn"} \\
@{term [source] less_eq} & @{typeof [show_sorts] "less_eq"} & (infixl $\le$ 50) \\
@{term [source] less} & @{typeof [show_sorts] "less"} & (infixl $<$ 50) \\
@{term [source] top} & @{typeof [show_sorts] "top"} \\
@{term [source] bot} & @{typeof [show_sorts] "bot"}
\end{tabular}
\caption{Important Overloaded Constants in Main}
\label{tab:overloading}
\end{center}
\end{table}
*}

(*<*)end(*>*)
