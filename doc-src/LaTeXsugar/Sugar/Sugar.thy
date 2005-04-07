(*<*)
theory Sugar
imports LaTeXsugar OptionalSugar
begin
(*>*)

section "Introduction"

text{* This document is for those Isabelle users who have mastered
the art of mixing \LaTeX\ text and Isabelle theories and never want to
typeset a theorem by hand anymore because they have experienced the
bliss of writing \verb!@!\verb!{thm[display]setsum_cartesian_product[no_vars]}!
and seeing Isabelle typeset it for them:
@{thm[display,eta_contract=false] setsum_cartesian_product[no_vars]}
No typos, no omissions, no sweat.
If you have not experienced that joy, read Chapter 4, \emph{Presenting
Theories}, \cite{LNCS2283} first.

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
that must be punished by instant rejection.


This document shows you how to make Isabelle and \LaTeX\ cooperate to
produce ordinary looking mathematics that hides the fact that it was
typeset by a machine. You merely need to load the right files:
\begin{itemize}
\item Import theory \texttt{LaTeXsugar} in the header of your own
theory.  You may also want bits of \texttt{OptionalSugar}, which you can
copy selectively into your own theory or import as a whole.  Both
theories live in \texttt{HOL/Library} and are found automatically.

\item Should you need additional \LaTeX\ packages (the text will tell
you so), you include them at the beginning of your \LaTeX\ document,
typically in \texttt{root.tex}.
\end{itemize}
*}

section{* HOL syntax*}

subsection{* Logic *}

text{* The predefined constructs @{text"if"}, @{text"let"} and
@{text"case"} are set in sans serif font to distinguish them from
other functions. This improves readability:
\begin{itemize}
\item @{term"if b then e\<^isub>1 else e\<^isub>2"} instead of @{text"if b then e\<^isub>1 else e\<^isub>2"}.
\item @{term"let x = e\<^isub>1 in e\<^isub>2"} instead of @{text"let x = e\<^isub>1 in e\<^isub>2"}.
\item @{term"case x of True \<Rightarrow> e\<^isub>1 | False \<Rightarrow> e\<^isub>2"} instead of\\
      @{text"case x of True \<Rightarrow> e\<^isub>1 | False \<Rightarrow> e\<^isub>2"}.
\end{itemize}
*}

subsection{* Sets *}

text{* Although set syntax in HOL is already close to
standard, we provide a few further improvements:
\begin{itemize}
\item @{term"{x. P}"} instead of @{text"{x. P}"}.
\item @{term"{}"} instead of @{text"{}"}.
\item @{term"insert a (insert b (insert c M))"} instead of @{text"insert a (insert b (insert c M))"}.
\end{itemize}
*}

subsection{* Lists *}

text{* If lists are used heavily, the following notations increase readability:
\begin{itemize}
\item @{term"x # xs"} instead of @{text"x # xs"}.
      Exceptionally, @{term"x # xs"} is also input syntax.
If you prefer more space around the $\cdot$ you have to redefine
\verb!\isasymcdot! in \LaTeX:
\verb!\renewcommand{\isasymcdot}{\isamath{\,\cdot\,}}!

\item @{term"length xs"} instead of @{text"length xs"}.
\item @{term"nth xs n"} instead of @{text"nth xs n"},
      the $n$th element of @{text xs}.

\item The @{text"@"} operation associates implicitly to the right,
which leads to unpleasant line breaks if the term is too long for one
line. To avoid this, \texttt{OptionalSugar} contains syntax to group
@{text"@"}-terms to the left before printing, which leads to better
line breaking behaviour:
@{term[display]"term\<^isub>0 @ term\<^isub>1 @ term\<^isub>2 @ term\<^isub>3 @ term\<^isub>4 @ term\<^isub>5 @ term\<^isub>6 @ term\<^isub>7 @ term\<^isub>8 @ term\<^isub>9 @ term\<^isub>1\<^isub>0"}

\end{itemize}
*}

section "Printing theorems"

subsection "Inference rules"

text{* To print theorems as inference rules you need to include Didier
R\'emy's \texttt{mathpartir} package~\cite{mathpartir}
for typesetting inference rules in your \LaTeX\ file.

Writing \verb!@!\verb!{thm[mode=Rule] conjI[no_vars]}! produces
@{thm[mode=Rule] conjI[no_vars]}, even in the middle of a sentence.
If you prefer your inference rule on a separate line, maybe with a name,
\begin{center}
@{thm[mode=Rule] conjI[no_vars]} {\sc conjI}
\end{center}
is produced by
\begin{quote}
\verb!\begin{center}!\\
\verb!@!\verb!{thm[mode=Rule] conjI[no_vars]} {\sc conjI}!\\
\verb!\end{center}!
\end{quote}
It is not recommended to use the standard \texttt{display} attribute
together with \texttt{Rule} because centering does not work and because
the line breaking mechanisms of \texttt{display} and \texttt{mathpartir} can
clash.

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

The \texttt{mathpartir} package copes well if there are too many
premises for one line:
\begin{center}
@{prop[mode=Rule] "\<lbrakk> A \<longrightarrow> B; B \<longrightarrow> C; C \<longrightarrow> D; D \<longrightarrow> E; E \<longrightarrow> F; F \<longrightarrow> G;
 G \<longrightarrow> H; H \<longrightarrow> I; I \<longrightarrow> J; J \<longrightarrow> K \<rbrakk> \<Longrightarrow> A \<longrightarrow> K"}
\end{center}

Limitations: 1. Premises and conclusion must each not be longer than
the line.  2. Premises that are @{text"\<Longrightarrow>"}-implications are again
displayed with a horizontal line, which looks at least unusual.

*}

subsection{*If-then*}

text{* If you prefer a fake ``natural language'' style you can produce
the body of
\newtheorem{theorem}{Theorem}
\begin{theorem}
@{thm[mode=IfThen] zle_trans[no_vars]}
\end{theorem}
by typing
\begin{quote}
\verb!@!\verb!{thm[mode=IfThen] le_trans[no_vars]}!
\end{quote}

In order to prevent odd line breaks, the premises are put into boxes.
At times this is too drastic:
\begin{theorem}
@{prop[mode=IfThen] "longpremise \<Longrightarrow> longerpremise \<Longrightarrow> P(f(f(f(f(f(f(f(f(f(x)))))))))) \<Longrightarrow> longestpremise \<Longrightarrow> conclusion"}
\end{theorem}
In which case you should use \texttt{mode=IfThenNoBox} instead of
\texttt{mode=IfThen}:
\begin{theorem}
@{prop[mode=IfThenNoBox] "longpremise \<Longrightarrow> longerpremise \<Longrightarrow> P(f(f(f(f(f(f(f(f(f(x)))))))))) \<Longrightarrow> longestpremise \<Longrightarrow> conclusion"}
\end{theorem}
*}

subsection {*Definitions and Equations*}

text {*
  The \verb!thm! antiquotation works nicely for proper theorems, but
  sets of equations as used in definitions are more difficult to
  typeset nicely: for some reason people tend to prefer aligned 
  @{text "="} signs.

  Isabelle2005 has a nice mechanism for this, namely the two
  antiquotations \verb!@!\verb!{lhs thm}! and \verb!@!\verb!{rhs thm}!.

  \begin{center}
  \begin{tabular}{l@ {~~@{text "="}~~}l}
  @{lhs foldl_Nil[no_vars]} & @{rhs foldl_Nil[no_vars]}\\
  @{lhs foldl_Cons[no_vars]} & @{rhs foldl_Cons[no_vars]}
  \end{tabular}
  \end{center}

  \noindent 
  is produced by the following code:

\begin{quote}
  \verb!\begin{center}!\\
  \verb!\begin{tabular}{l@ {~~!\verb!@!\verb!{text "="}~~}l}!\\
  \verb!@!\verb!{lhs foldl_Nil[no_vars]} & @!\verb!{rhs foldl_Nil[no_vars]}!\\
  \verb!@!\verb!{lhs foldl_Cons[no_vars]} & @!\verb!{rhs foldl_Cons[no_vars]}!\\
  \verb!\end{tabular}!\\
  \verb!\end{center}!
\end{quote}

  \noindent
  Note the space between \verb!@! and \verb!{! in the tabular argument.
  It prevents Isabelle from interpreting \verb!@ {~~...~~}! 
  as antiquotation. \verb!@!\verb!{lhs thm}! and \verb!@!\verb!{rhs thm}! 
  try to be smart about the interpretation of the theorem they
  print, they work just as well for meta equality @{text "\<equiv>"} and other
  binary operators like @{text "<"}.
*}

subsection "Patterns"

text {*
  Sometimes functions ignore one or more of their
  arguments and some functional languages have nice 
  syntax for that as in @{thm hd.simps [where xs=DUMMY,no_vars]}.

  You can simulate this in Isabelle by instantiating the @{term xs} in
  definition \mbox{@{thm hd.simps[no_vars]}} with a constant @{text DUMMY} that
  is printed as @{term DUMMY}. The code for the pattern above is 
  \verb!@!\verb!{thm hd.simps [where xs=DUMMY,no_vars]}!.

  You can drive this game even further and extend the syntax of let
  bindings such that certain functions like @{term fst}, @{term hd}, 
  etc.\ are printed as patterns. \texttt{OptionalSugar} provides the
  following:
  
  \begin{center}
  \begin{tabular}{l@ {~~produced by~~}l}
  @{term "let x = fst p in t"} & \verb!@!\verb!{term "let x = fst p in t"}!\\
  @{term "let x = snd p in t"} & \verb!@!\verb!{term "let x = snd p in t"}!\\
  @{term "let x = hd xs in t"} & \verb!@!\verb!{term "let x = hd xs in t"}!\\
  @{term "let x = tl xs in t"} & \verb!@!\verb!{term "let x = tl xs in t"}!\\
  @{term "let x = the y in t"} & \verb!@!\verb!{term "let x = the y in t"}!\\
  \end{tabular}
  \end{center}
*}

subsection "Proofs"

text {*
  Full proofs, even if written in beautiful Isar style, are likely to
  be too long and detailed to be included in conference papers, but
  some key lemmas might be of interest.

  It is usually easiest to put them in figures like the one in Fig.\
  \ref{fig:proof}. This was achieved with the \isakeyword{text\_raw}
  command:
*}
text_raw {*
  \begin{figure}
  \begin{center}\begin{minipage}{0.6\textwidth}  
  \isastyle\isamarkuptrue
*}
lemma True
proof -
  -- "pretty trivial"
  show True by force
qed
text_raw {*    
  \end{minipage}\end{center}
  \caption{Example proof in a figure.}\label{fig:proof}
  \end{figure}
*}
text {*

\begin{quote}
\small
\verb!text_raw {!\verb!*!\\
\verb!  \begin{figure}!\\
\verb!  \begin{center}\begin{minipage}{0.6\textwidth}!\\
\verb!  \isastyle\isamarkuptrue!\\
\verb!*!\verb!}!\\
\verb!lemma True!\\
\verb!proof -!\\
\verb!  -- "pretty trivial"!\\
\verb!  show True by force!\\
\verb!qed!\\
\verb!text_raw {!\verb!*!\\
\verb!  \end{minipage}\end{center}!\\
\verb!  \caption{Example proof in a figure.}\label{fig:proof}!\\
\verb!  \end{figure}!\\
\verb!*!\verb!}!
\end{quote}
  
*}

(*<*)
end
(*>*)