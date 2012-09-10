(*<*)
theory Sugar
imports "~~/src/HOL/Library/LaTeXsugar" "~~/src/HOL/Library/OptionalSugar"
begin
(*>*)
text{*
\section{Introduction}

This document is for those Isabelle users who have mastered
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
typically in \texttt{root.tex}. For a start, you should
\verb!\usepackage{amssymb}! --- otherwise typesetting
@{prop[source]"\<not>(\<exists>x. P x)"} will fail because the AMS symbol
@{text"\<nexists>"} is missing.
\end{itemize}


\section{HOL syntax}

\subsection{Logic}

The formula @{prop[source]"\<not>(\<exists>x. P x)"} is typeset as @{prop"~(EX x. P x)"}.

The predefined constructs @{text"if"}, @{text"let"} and
@{text"case"} are set in sans serif font to distinguish them from
other functions. This improves readability:
\begin{itemize}
\item @{term"if b then e\<^isub>1 else e\<^isub>2"} instead of @{text"if b then e\<^isub>1 else e\<^isub>2"}.
\item @{term"let x = e\<^isub>1 in e\<^isub>2"} instead of @{text"let x = e\<^isub>1 in e\<^isub>2"}.
\item @{term"case x of True \<Rightarrow> e\<^isub>1 | False \<Rightarrow> e\<^isub>2"} instead of\\
      @{text"case x of True \<Rightarrow> e\<^isub>1 | False \<Rightarrow> e\<^isub>2"}.
\end{itemize}

\subsection{Sets}

Although set syntax in HOL is already close to
standard, we provide a few further improvements:
\begin{itemize}
\item @{term"{x. P}"} instead of @{text"{x. P}"}.
\item @{term"{}"} instead of @{text"{}"}, where
 @{term"{}"} is also input syntax.
\item @{term"insert a (insert b (insert c M))"} instead of @{text"insert a (insert b (insert c M))"}.
\end{itemize}


\subsection{Lists}

If lists are used heavily, the following notations increase readability:
\begin{itemize}
\item @{term"x # xs"} instead of @{text"x # xs"},
      where @{term"x # xs"} is also input syntax.
If you prefer more space around the $\cdot$ you have to redefine
\verb!\isasymcdot! in \LaTeX:
\verb!\renewcommand{\isasymcdot}{\isamath{\,\cdot\,}}!

\item @{term"length xs"} instead of @{text"length xs"}.
\item @{term"nth xs n"} instead of @{text"nth xs n"},
      the $n$th element of @{text xs}.

\item Human readers are good at converting automatically from lists to
sets. Hence \texttt{OptionalSugar} contains syntax for suppressing the
conversion function @{const set}: for example, @{prop[source]"x \<in> set xs"}
becomes @{prop"x \<in> set xs"}.

\item The @{text"@"} operation associates implicitly to the right,
which leads to unpleasant line breaks if the term is too long for one
line. To avoid this, \texttt{OptionalSugar} contains syntax to group
@{text"@"}-terms to the left before printing, which leads to better
line breaking behaviour:
@{term[display]"term\<^isub>0 @ term\<^isub>1 @ term\<^isub>2 @ term\<^isub>3 @ term\<^isub>4 @ term\<^isub>5 @ term\<^isub>6 @ term\<^isub>7 @ term\<^isub>8 @ term\<^isub>9 @ term\<^isub>1\<^isub>0"}

\end{itemize}


\subsection{Numbers}

Coercions between numeric types are alien to mathematicians who
consider, for example, @{typ nat} as a subset of @{typ int}.
\texttt{OptionalSugar} contains syntax for suppressing numeric coercions such
as @{const int} @{text"::"} @{typ"nat \<Rightarrow> int"}. For example,
@{term[source]"int 5"} is printed as @{term "int 5"}. Embeddings of types
@{typ nat}, @{typ int}, @{typ real} are covered; non-injective coercions such
as @{const nat} @{text"::"} @{typ"int \<Rightarrow> nat"} are not and should not be
hidden.


\section{Printing theorems}

\subsection{Question marks}

If you print anything, especially theorems, containing
schematic variables they are prefixed with a question mark:
\verb!@!\verb!{thm conjI}! results in @{thm conjI}. Most of the time
you would rather not see the question marks. There is an attribute
\verb!no_vars! that you can attach to the theorem that turns its
schematic into ordinary free variables: \verb!@!\verb!{thm conjI[no_vars]}!
results in @{thm conjI[no_vars]}.

This \verb!no_vars! business can become a bit tedious.
If you would rather never see question marks, simply put
\begin{quote}
\verb!options [show_question_marks = false]!
\end{quote}
into the relevant \texttt{ROOT} file, just before the \texttt{theories} for that session.
The rest of this document is produced with this flag set to \texttt{false}.

Hint: Setting \verb!show_question_marks! to \texttt{false} only
suppresses question marks; variables that end in digits,
e.g. @{text"x1"}, are still printed with a trailing @{text".0"},
e.g. @{text"x1.0"}, their internal index. This can be avoided by
turning the last digit into a subscript: write \verb!x\<^isub>1! and
obtain the much nicer @{text"x\<^isub>1"}. *}

(*<*)declare [[show_question_marks = false]](*>*)

subsection {*Qualified names*}

text{* If there are multiple declarations of the same name, Isabelle prints
the qualified name, for example @{text "T.length"}, where @{text T} is the
theory it is defined in, to distinguish it from the predefined @{const[source]
"List.length"}. In case there is no danger of confusion, you can insist on
short names (no qualifiers) by setting the \verb!names_short!
configuration option in the context.


\subsection {Variable names\label{sec:varnames}}

It sometimes happens that you want to change the name of a
variable in a theorem before printing it. This can easily be achieved
with the help of Isabelle's instantiation attribute \texttt{where}:
@{thm conjI[where P = \<phi> and Q = \<psi>]} is the result of
\begin{quote}
\verb!@!\verb!{thm conjI[where P = \<phi> and Q = \<psi>]}!
\end{quote}
To support the ``\_''-notation for irrelevant variables
the constant \texttt{DUMMY} has been introduced:
@{thm fst_conv[where b = DUMMY]} is produced by
\begin{quote}
\verb!@!\verb!{thm fst_conv[where b = DUMMY]}!
\end{quote}
Variables that are bound by quantifiers or lambdas cannot be renamed
like this. Instead, the attribute \texttt{rename\_abs} does the
job. It expects a list of names or underscores, similar to the
\texttt{of} attribute:
\begin{quote}
\verb!@!\verb!{thm split_paired_All[rename_abs _ l r]}!
\end{quote}
produces @{thm split_paired_All[rename_abs _ l r]}.


\subsection{Inference rules}

To print theorems as inference rules you need to include Didier
R\'emy's \texttt{mathpartir} package~\cite{mathpartir}
for typesetting inference rules in your \LaTeX\ file.

Writing \verb!@!\verb!{thm[mode=Rule] conjI}! produces
@{thm[mode=Rule] conjI}, even in the middle of a sentence.
If you prefer your inference rule on a separate line, maybe with a name,
\begin{center}
@{thm[mode=Rule] conjI} {\sc conjI}
\end{center}
is produced by
\begin{quote}
\verb!\begin{center}!\\
\verb!@!\verb!{thm[mode=Rule] conjI} {\sc conjI}!\\
\verb!\end{center}!
\end{quote}
It is not recommended to use the standard \texttt{display} option
together with \texttt{Rule} because centering does not work and because
the line breaking mechanisms of \texttt{display} and \texttt{mathpartir} can
clash.

Of course you can display multiple rules in this fashion:
\begin{quote}
\verb!\begin{center}!\\
\verb!@!\verb!{thm[mode=Rule] conjI} {\sc conjI} \\[1ex]!\\
\verb!@!\verb!{thm[mode=Rule] conjE} {\sc disjI$_1$} \qquad!\\
\verb!@!\verb!{thm[mode=Rule] disjE} {\sc disjI$_2$}!\\
\verb!\end{center}!
\end{quote}
yields
\begin{center}\small
@{thm[mode=Rule] conjI} {\sc conjI} \\[1ex]
@{thm[mode=Rule] disjI1} {\sc disjI$_1$} \qquad
@{thm[mode=Rule] disjI2} {\sc disjI$_2$}
\end{center}

The \texttt{mathpartir} package copes well if there are too many
premises for one line:
\begin{center}
@{prop[mode=Rule] "\<lbrakk> A \<longrightarrow> B; B \<longrightarrow> C; C \<longrightarrow> D; D \<longrightarrow> E; E \<longrightarrow> F; F \<longrightarrow> G;
 G \<longrightarrow> H; H \<longrightarrow> I; I \<longrightarrow> J; J \<longrightarrow> K \<rbrakk> \<Longrightarrow> A \<longrightarrow> K"}
\end{center}

Limitations: 1. Premises and conclusion must each not be longer than
the line.  2. Premises that are @{text"\<Longrightarrow>"}-implications are again
displayed with a horizontal line, which looks at least unusual.


In case you print theorems without premises no rule will be printed by the
\texttt{Rule} print mode. However, you can use \texttt{Axiom} instead:
\begin{quote}
\verb!\begin{center}!\\
\verb!@!\verb!{thm[mode=Axiom] refl} {\sc refl}! \\
\verb!\end{center}!
\end{quote}
yields
\begin{center}
@{thm[mode=Axiom] refl} {\sc refl} 
\end{center}


\subsection{Displays and font sizes}

When displaying theorems with the \texttt{display} option, for example as in
\verb!@!\verb!{thm[display] refl}! @{thm[display] refl} the theorem is
set in small font. It uses the \LaTeX-macro \verb!\isastyle!,
which is also the style that regular theory text is set in, e.g. *}

lemma "t = t"
(*<*)oops(*>*)

text{* \noindent Otherwise \verb!\isastyleminor! is used,
which does not modify the font size (assuming you stick to the default
\verb!\isabellestyle{it}! in \texttt{root.tex}). If you prefer
normal font size throughout your text, include
\begin{quote}
\verb!\renewcommand{\isastyle}{\isastyleminor}!
\end{quote}
in \texttt{root.tex}. On the other hand, if you like the small font,
just put \verb!\isastyle! in front of the text in question,
e.g.\ at the start of one of the center-environments above.

The advantage of the display option is that you can display a whole
list of theorems in one go. For example,
\verb!@!\verb!{thm[display] append.simps}!
generates @{thm[display] append.simps}


\subsection{If-then}

If you prefer a fake ``natural language'' style you can produce
the body of
\newtheorem{theorem}{Theorem}
\begin{theorem}
@{thm[mode=IfThen] le_trans}
\end{theorem}
by typing
\begin{quote}
\verb!@!\verb!{thm[mode=IfThen] le_trans}!
\end{quote}

In order to prevent odd line breaks, the premises are put into boxes.
At times this is too drastic:
\begin{theorem}
@{prop[mode=IfThen] "longpremise \<Longrightarrow> longerpremise \<Longrightarrow> P(f(f(f(f(f(f(f(f(f(x)))))))))) \<Longrightarrow> longestpremise \<Longrightarrow> conclusion"}
\end{theorem}
In which case you should use \texttt{IfThenNoBox} instead of
\texttt{IfThen}:
\begin{theorem}
@{prop[mode=IfThenNoBox] "longpremise \<Longrightarrow> longerpremise \<Longrightarrow> P(f(f(f(f(f(f(f(f(f(x)))))))))) \<Longrightarrow> longestpremise \<Longrightarrow> conclusion"}
\end{theorem}


\subsection{Doing it yourself\label{sec:yourself}}

If for some reason you want or need to present theorems your
own way, you can extract the premises and the conclusion explicitly
and combine them as you like:
\begin{itemize}
\item \verb!@!\verb!{thm (prem 1)! $thm$\verb!}!
prints premise 1 of $thm$.
\item \verb!@!\verb!{thm (concl)! $thm$\verb!}!
prints the conclusion of $thm$.
\end{itemize}
For example, ``from @{thm (prem 2) conjI} and
@{thm (prem 1) conjI} we conclude @{thm (concl) conjI}''
is produced by
\begin{quote}
\verb!from !\verb!@!\verb!{thm (prem 2) conjI}! \verb!and !\verb!@!\verb!{thm (prem 1) conjI}!\\
\verb!we conclude !\verb!@!\verb!{thm (concl) conjI}!
\end{quote}
Thus you can rearrange or hide premises and typeset the theorem as you like.
Styles like \verb!(prem 1)! are a general mechanism explained
in \S\ref{sec:styles}.


\subsection{Patterns}


In \S\ref{sec:varnames} we shows how to create patterns containing ``@{term DUMMY}''.
You can drive this game even further and extend the syntax of let
bindings such that certain functions like @{term fst}, @{term hd}, 
etc.\ are printed as patterns. \texttt{OptionalSugar} provides the following:

\begin{center}
\begin{tabular}{l@ {~~produced by~~}l}
@{term "let x = fst p in t"} & \verb!@!\verb!{term "let x = fst p in t"}!\\
@{term "let x = snd p in t"} & \verb!@!\verb!{term "let x = snd p in t"}!\\
@{term "let x = hd xs in t"} & \verb!@!\verb!{term "let x = hd xs in t"}!\\
@{term "let x = tl xs in t"} & \verb!@!\verb!{term "let x = tl xs in t"}!\\
@{term "let x = the y in t"} & \verb!@!\verb!{term "let x = the y in t"}!\\
\end{tabular}
\end{center}


\section {Styles\label{sec:styles}}

The \verb!thm! antiquotation works nicely for single theorems, but
sets of equations as used in definitions are more difficult to
typeset nicely: people tend to prefer aligned @{text "="} signs.

To deal with such cases where it is desirable to dive into the structure
of terms and theorems, Isabelle offers antiquotations featuring ``styles'':

\begin{quote}
\verb!@!\verb!{thm (style) thm}!\\
\verb!@!\verb!{prop (style) thm}!\\
\verb!@!\verb!{term (style) term}!\\
\verb!@!\verb!{term_type (style) term}!\\
\verb!@!\verb!{typeof (style) term}!\\
\end{quote}

 A ``style'' is a transformation of a term. There are predefined
 styles, namely \verb!lhs! and \verb!rhs!, \verb!prem! with one argument, and \verb!concl!.
For example, the output
\begin{center}
\begin{tabular}{l@ {~~@{text "="}~~}l}
@{thm (lhs) append_Nil} & @{thm (rhs) append_Nil}\\
@{thm (lhs) append_Cons} & @{thm (rhs) append_Cons}
\end{tabular}
\end{center}
is produced by the following code:
\begin{quote}
  \verb!\begin{center}!\\
  \verb!\begin{tabular}{l@ {~~!\verb!@!\verb!{text "="}~~}l}!\\
  \verb!@!\verb!{thm (lhs) append_Nil} & @!\verb!{thm (rhs) append_Nil}\\!\\
  \verb!@!\verb!{thm (lhs) append_Cons} & @!\verb!{thm (rhs) append_Cons}!\\
  \verb!\end{tabular}!\\
  \verb!\end{center}!
\end{quote}
Note the space between \verb!@! and \verb!{! in the tabular argument.
It prevents Isabelle from interpreting \verb!@ {~~...~~}! 
as an antiquotation. The styles \verb!lhs! and \verb!rhs!
extract the left hand side (or right hand side respectively) from the
conclusion of propositions consisting of a binary operator
(e.~g.~@{text "="}, @{text "\<equiv>"}, @{text "<"}).

Likewise, \verb!concl! may be used as a style to show just the
conclusion of a proposition. For example, take \verb!hd_Cons_tl!:
\begin{center}
  @{thm hd_Cons_tl}
\end{center}
To print just the conclusion,
\begin{center}
  @{thm (concl) hd_Cons_tl}
\end{center}
type
\begin{quote}
  \verb!\begin{center}!\\
  \verb!@!\verb!{thm (concl) hd_Cons_tl}!\\
  \verb!\end{center}!
\end{quote}
Beware that any options must be placed \emph{before} the style, as in this example.

Further use cases can be found in \S\ref{sec:yourself}.
If you are not afraid of ML, you may also define your own styles.
Have a look at module @{ML_struct Term_Style}.


\section {Proofs}

Full proofs, even if written in beautiful Isar style, are
likely to be too long and detailed to be included in conference
papers, but some key lemmas might be of interest.
It is usually easiest to put them in figures like the one in Fig.\
\ref{fig:proof}. This was achieved with the \isakeyword{text\_raw} command:
*}
text_raw {*
  \begin{figure}
  \begin{center}\begin{minipage}{0.6\textwidth}  
  \isastyleminor\isamarkuptrue
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
\verb!  \isastyleminor\isamarkuptrue!\\
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

Other theory text, e.g.\ definitions, can be put in figures, too.

\section{Theory snippets}

This section describes how to include snippets of a theory text in some other \LaTeX\ document.
The typical scenario is that the description of your theory is not part of the theory text but
a separate document that antiquotes bits of the theory. This works well for terms and theorems
but there are no antiquotations, for example, for function definitions or proofs. Even if there are antiquotations,
the output is usually a reformatted (by Isabelle) version of the input and may not look like
you wanted it to look. Here is how to include a snippet of theory text (in \LaTeX\ form) in some
other \LaTeX\ document, in 4 easy steps. Beware that these snippets are not processed by
any antiquotation mechanism: the resulting \LaTeX\ text is more or less exactly what you wrote
in the theory, without any added sugar.

\subsection{Theory markup}

Include some markers at the beginning and the end of the theory snippet you want to cut out.
You have to place the following lines before and after the snippet, where snippets must always be
consecutive lines of theory text:
\begin{quote}
\verb!\text_raw{!\verb!*\snip{!\emph{snippetname}\verb!}{1}{2}{%*!\verb!}!\\
\emph{theory text}\\
\verb!\text_raw{!\verb!*!\verb!}%endsnip*!\verb!}!
\end{quote}
where \emph{snippetname} should be a unique name for the snippet. The numbers \texttt{1}
and \texttt{2} are explained in a moment.

\subsection{Generate the \texttt{.tex} file}

Run your theory \texttt{T} with the \texttt{isabelle} \texttt{build} tool
to generate the \LaTeX-file \texttt{T.tex} which is needed for the next step,
extraction of marked snippets.
You may also want to process \texttt{T.tex} to generate a pdf document.
This requires a definition of \texttt{\char`\\snippet}:
\begin{verbatim}
\newcommand{\repeatisanl}[1]
  {\ifnum#1=0\else\isanewline\repeatisanl{\numexpr#1-1}\fi}
\newcommand{\snip}[4]{\repeatisanl#2#4\repeatisanl#3}
\end{verbatim}
Parameter 2 and 3 of \texttt{\char`\\snippet} are numbers (the \texttt{1}
and \texttt{2} above) and determine how many newlines are inserted before and after the snippet.
Unfortunately \texttt{text\_raw} eats up all preceding and following newlines
and they have to be inserted again in this manner. Otherwise the document generated from \texttt{T.tex}
will look ugly around the snippets. It can take some iterations to get the number of required
newlines exactly right.

\subsection{Extract marked snippets}
\label{subsec:extract}

Extract the marked bits of text with a shell-level script, e.g.
\begin{quote}
\verb!sed -n '/\\snip{/,/endsnip/p' T.tex > !\emph{snippets}\verb!.tex!
\end{quote}
File \emph{snippets}\texttt{.tex} (the name is arbitrary) now contains a sequence of blocks like this
\begin{quote}
\verb!\snip{!\emph{snippetname}\verb!}{1}{2}{%!\\
\emph{theory text}\\
\verb!}%endsnip!
\end{quote}

\subsection{Including snippets}

In the preamble of the document where the snippets are to be used you define \texttt{\char`\\snip}
and input \emph{snippets}\texttt{.tex}:
\begin{verbatim}
\newcommand{\snip}[4]
  {\expandafter\newcommand\csname #1\endcsname{#4}}
\input{snippets}
\end{verbatim}
This definition of \texttt{\char`\\snip} simply has the effect of defining for each snippet
\emph{snippetname} a \LaTeX\ command \texttt{\char`\\}\emph{snippetname}
that produces the corresponding snippet text. In the body of your document you can display that text
like this:
\begin{quote}
\verb!\begin{isabelle}!\\
\texttt{\char`\\}\emph{snippetname}\\
\verb!\end{isabelle}!
\end{quote}
The \texttt{isabelle} environment is the one defined in the standard file
\texttt{isabelle.sty} which most likely you are loading anyway.
*}

(*<*)
end
(*>*)
