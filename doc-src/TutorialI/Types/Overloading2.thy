(*<*)theory Overloading2 = Overloading1:(*>*)

text{*
Of course this is not the only possible definition of the two relations.
Componentwise comparison of lists of equal length also makes sense. This time
the elements of the list must also be of class @{text ordrel} to permit their
comparison:
*}

instance list :: (ordrel)ordrel
by intro_classes

defs (overloaded)
le_list_def: "xs <<= (ys::'a::ordrel list) \<equiv>
              size xs = size ys \<and> (\<forall>i<size xs. xs!i <<= ys!i)"

text{*\noindent
The infix function @{text"!"} yields the nth element of a list.
*}

subsubsection{*Predefined Overloading*}

text{*
HOL comes with a number of overloaded constants and corresponding classes.
The most important ones are listed in Table~\ref{tab:overloading} in the appendix. They are
defined on all numeric types and sometimes on other types as well, for example
@{text"-"}, @{text"\<le>"} and @{text"<"} on sets.

In addition there is a special input syntax for bounded quantifiers:
\begin{center}
\begin{tabular}{lcl}
@{text"\<forall>x \<le> y. P x"} & @{text"\<rightharpoonup>"} & @{prop"\<forall>x. x \<le> y \<longrightarrow> P x"} \\
@{text"\<exists>x \<le> y. P x"} & @{text"\<rightharpoonup>"} & @{prop"\<exists>x. x \<le> y \<and> P x"}
\end{tabular}
\end{center}
And analogously for @{text"<"} instead of @{text"\<le>"}.
The form on the left is translated into the one on the right upon input.
For technical reasons, it is not translated back upon output.
*}(*<*)end(*>*)
