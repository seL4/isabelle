(*<*)
theory Sugar
imports Main
begin
(*>*)

section "Introduction"

text{* This document is for those Isabelle users that have mastered
the art of mixing \LaTeX\ text and Isabelle theories and never want to
typeset a theorem by hand anymore because they have experienced the
bliss of writing \verb!@!\verb!{thm[display]setsum_cartesian_product[no_vars]}!
and seeing Isabelle typeset it for them:
@{thm[display,eta_contract=false] setsum_cartesian_product[no_vars]}
No typos, no omissions, no sweat!
If you have not experienced that joy, read chapter 4, \emph{Presenting
Theories}, of \cite{LNCS2283} first.

If you have mastered the art of Isabelle's \emph{antiquotations},
i.e.\ things like the above \verb!@!\verb!{thm...}!, beware: in your vanity
you may be tempted to think that all readers of the stunning ps or pdf
documents you can now produce at the drop of a hat will be struck with
awe at the beauty unfolding in front of their eyes. Until one day you
come across that very critical of readers known as the ``common referee''.
He has the nasty habit of refusing to understand unfamiliar notation
like Isabelle's infamous @{text"\<lbrakk> \<rbrakk> \<Longrightarrow>"} no matter how many times you
explain it in your paper. Even worse, he thinks that using @{text"\<lbrakk>
\<rbrakk>"} for anything other than denotational semantics is a cardinal sin
that must be punished by immediate rejection.


This document shows you how to make Isabelle and \LaTeX\ cooperate to
produce ordinary looking mathematics that hides the fact that it was
typeset by a machine. This involves additional syntax-related
declarations for your theory file and corresponding \LaTeX\ macros. We
explain how to use them but show neither. They can be downloaded from
the web.

*}

section "Printing theorems"

subsection "Inference rules"

(*<*)
syntax (Rule output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{>_\<^raw:}>\<^raw:{>_\<^raw:}>")

  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{>_\<^raw:}>\<^raw:{>_\<^raw:}>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("_\<^raw:\\>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("_")
(*>*)

text{* To print theorems as inference rules you need to include the
\texttt{Rule} output syntax declarations in your theory and Didier
Remy's \texttt{mathpartir} package for typesetting inference rules in
your \LaTeX\ file.

Writing \verb!@!\verb!{thm[mode=Rule] conjI[no_vars]}! produces
@{thm[mode=Rule] conjI[no_vars]}, even in the middle of a sentence.
The standard \texttt{display} attribute, i.e.\ writing
\verb![mode=Rule,display]! instead of \verb![mode=Rule]!,
displays the rule on a separate line using a smaller font:
@{thm[mode=Rule,display] conjI[no_vars]}
Centering a display does not work directly. Instead you can enclose the
non-displayed variant in a \texttt{center} environment:

\begin{quote}
\verb!\begin{center}!\\
\verb!@!\verb!{thm[mode=Rule] conjI[no_vars]} {\sc conjI}!\\
\verb!\end{center}!
\end{quote}
also adds a label to the rule and yields
\begin{center}
@{thm[mode=Rule] conjI[no_vars]} {\sc conjI}
\end{center}
Of course you can display multiple rules in this fashion:
\begin{quote}
\verb!\begin{center}\isastyle!\\
\verb!@!\verb!{thm[mode=Rule] conjI[no_vars]} {\sc conjI} \\[1ex]!\\
\verb!@!\verb!{thm[mode=Rule] conjE[no_vars]} {\sc disjI$_1$} \qquad!\\
\verb!@!\verb!{thm[mode=Rule] disjE[no_vars]} {\sc disjI$_2$}!\\
\verb!\end{center}!
\end{quote}
yields
\begin{center}\isastyle
@{thm[mode=Rule] conjI[no_vars]} {\sc conjI} \\[1ex]
@{thm[mode=Rule] disjI1[no_vars]} {\sc disjI$_1$} \qquad
@{thm[mode=Rule] disjI2[no_vars]} {\sc disjI$_2$}
\end{center}
Note that we included \verb!\isastyle! to obtain
the smaller font that otherwise comes only with \texttt{display}.

*}
(*<*)
end
(*>*)