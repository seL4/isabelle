(*<*)
theory Basics
imports Main
begin
(*>*)
text\<open>
This chapter introduces HOL as a functional programming language and shows
how to prove properties of functional programs by induction.

\section{Basics}

\subsection{Types, Terms and Formulas}
\label{sec:TypesTermsForms}

HOL is a typed logic whose type system resembles that of functional
programming languages. Thus there are
\begin{description}
\item[base types,] 
in particular \<^typ>\<open>bool\<close>, the type of truth values,
\<^typ>\<open>nat\<close>, the type of natural numbers ($\mathbb{N}$), and \indexed{\<^typ>\<open>int\<close>}{int},
the type of mathematical integers ($\mathbb{Z}$).
\item[type constructors,]
 in particular \<open>list\<close>, the type of
lists, and \<open>set\<close>, the type of sets. Type constructors are written
postfix, i.e., after their arguments. For example,
\<^typ>\<open>nat list\<close> is the type of lists whose elements are natural numbers.
\item[function types,]
denoted by \<open>\<Rightarrow>\<close>.
\item[type variables,]
  denoted by \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close>, etc., like in ML\@.
\end{description}
Note that \<^typ>\<open>'a \<Rightarrow> 'b list\<close> means \noquotes{@{typ[source]"'a \<Rightarrow> ('b list)"}},
not \<^typ>\<open>('a \<Rightarrow> 'b) list\<close>: postfix type constructors have precedence
over \<open>\<Rightarrow>\<close>.

\conceptidx{Terms}{term} are formed as in functional programming by
applying functions to arguments. If \<open>f\<close> is a function of type
\<open>\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2\<close> and \<open>t\<close> is a term of type
\<open>\<tau>\<^sub>1\<close> then \<^term>\<open>f t\<close> is a term of type \<open>\<tau>\<^sub>2\<close>. We write \<open>t :: \<tau>\<close> to mean that term \<open>t\<close> has type \<open>\<tau>\<close>.

\begin{warn}
There are many predefined infix symbols like \<open>+\<close> and \<open>\<le>\<close>.
The name of the corresponding binary function is \<^term>\<open>(+)\<close>,
not just \<open>+\<close>. That is, \<^term>\<open>x + y\<close> is nice surface syntax
(``syntactic sugar'') for \noquotes{@{term[source]"(+) x y"}}.
\end{warn}

HOL also supports some basic constructs from functional programming:
\begin{quote}
\<open>(if b then t\<^sub>1 else t\<^sub>2)\<close>\\
\<open>(let x = t in u)\<close>\\
\<open>(case t of pat\<^sub>1 \<Rightarrow> t\<^sub>1 | \<dots> | pat\<^sub>n \<Rightarrow> t\<^sub>n)\<close>
\end{quote}
\begin{warn}
The above three constructs must always be enclosed in parentheses
if they occur inside other constructs.
\end{warn}
Terms may also contain \<open>\<lambda>\<close>-abstractions. For example,
\<^term>\<open>\<lambda>x. x\<close> is the identity function.

\conceptidx{Formulas}{formula} are terms of type \<open>bool\<close>.
There are the basic constants \<^term>\<open>True\<close> and \<^term>\<open>False\<close> and
the usual logical connectives (in decreasing order of precedence):
\<open>\<not>\<close>, \<open>\<and>\<close>, \<open>\<or>\<close>, \<open>\<longrightarrow>\<close>.

\conceptidx{Equality}{equality} is available in the form of the infix function \<open>=\<close>
of type \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>. It also works for formulas, where
it means ``if and only if''.

\conceptidx{Quantifiers}{quantifier} are written \<^prop>\<open>\<forall>x. P\<close> and \<^prop>\<open>\<exists>x. P\<close>.

Isabelle automatically computes the type of each variable in a term. This is
called \concept{type inference}.  Despite type inference, it is sometimes
necessary to attach an explicit \concept{type constraint} (or \concept{type
annotation}) to a variable or term.  The syntax is \<open>t :: \<tau>\<close> as in
\mbox{\noquotes{@{term[source] "m + (n::nat)"}}}. Type constraints may be
needed to
disambiguate terms involving overloaded functions such as \<open>+\<close>.

Finally there are the universal quantifier \<open>\<And>\<close>\index{$4@\isasymAnd} and the implication
\<open>\<Longrightarrow>\<close>\index{$3@\isasymLongrightarrow}. They are part of the Isabelle framework, not the logic
HOL. Logically, they agree with their HOL counterparts \<open>\<forall>\<close> and
\<open>\<longrightarrow>\<close>, but operationally they behave differently. This will become
clearer as we go along.
\begin{warn}
Right-arrows of all kinds always associate to the right. In particular,
the formula
\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>2 \<Longrightarrow> A\<^sub>3\<close> means \<open>A\<^sub>1 \<Longrightarrow> (A\<^sub>2 \<Longrightarrow> A\<^sub>3)\<close>.
The (Isabelle-specific\footnote{To display implications in this style in
Isabelle/jEdit you need to set Plugins $>$ Plugin Options $>$ Isabelle/General $>$ Print Mode to ``\texttt{brackets}'' and restart.}) notation \mbox{\<open>\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A\<close>}
is short for the iterated implication \mbox{\<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> A\<close>}.
Sometimes we also employ inference rule notation:
\inferrule{\mbox{\<open>A\<^sub>1\<close>}\\ \mbox{\<open>\<dots>\<close>}\\ \mbox{\<open>A\<^sub>n\<close>}}
{\mbox{\<open>A\<close>}}
\end{warn}


\subsection{Theories}
\label{sec:Basic:Theories}

Roughly speaking, a \concept{theory} is a named collection of types,
functions, and theorems, much like a module in a programming language.
All Isabelle text needs to go into a theory.
The general format of a theory \<open>T\<close> is
\begin{quote}
\indexed{\isacom{theory}}{theory} \<open>T\<close>\\
\indexed{\isacom{imports}}{imports} \<open>T\<^sub>1 \<dots> T\<^sub>n\<close>\\
\isacom{begin}\\
\emph{definitions, theorems and proofs}\\
\isacom{end}
\end{quote}
where \<open>T\<^sub>1 \<dots> T\<^sub>n\<close> are the names of existing
theories that \<open>T\<close> is based on. The \<open>T\<^sub>i\<close> are the
direct \conceptidx{parent theories}{parent theory} of \<open>T\<close>.
Everything defined in the parent theories (and their parents, recursively) is
automatically visible. Each theory \<open>T\<close> must
reside in a \concept{theory file} named \<open>T.thy\<close>.

\begin{warn}
HOL contains a theory \<^theory>\<open>Main\<close>\index{Main@\<^theory>\<open>Main\<close>}, the union of all the basic
predefined theories like arithmetic, lists, sets, etc.
Unless you know what you are doing, always include \<open>Main\<close>
as a direct or indirect parent of all your theories.
\end{warn}

In addition to the theories that come with the Isabelle/HOL distribution
(see \<^url>\<open>https://isabelle.in.tum.de/library/HOL\<close>)
there is also the \emph{Archive of Formal Proofs}
at \<^url>\<open>https://isa-afp.org\<close>, a growing collection of Isabelle theories
that everybody can contribute to.

\subsection{Quotation Marks}

The textual definition of a theory follows a fixed syntax with keywords like
\isacom{begin} and \isacom{datatype}.  Embedded in this syntax are
the types and formulas of HOL.  To distinguish the two levels, everything
HOL-specific (terms and types) must be enclosed in quotation marks:
\texttt{"}\dots\texttt{"}. Quotation marks around a
single identifier can be dropped.  When Isabelle prints a syntax error
message, it refers to the HOL syntax as the \concept{inner syntax} and the
enclosing theory language as the \concept{outer syntax}.

\ifsem\else
\subsection{Proof State}

\begin{warn}
By default Isabelle/jEdit does not show the proof state but this tutorial
refers to it frequently. You should tick the ``Proof state'' box
to see the proof state in the output window.
\end{warn}
\fi
\<close>
(*<*)
end
(*>*)
