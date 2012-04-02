(*<*)
theory Basics
imports Main
begin
(*>*)
text{*
This chapter introduces HOL as a functional programming language and shows
how to prove properties of functional programs by induction.

\section{Basics}

\subsection{Types, Terms and Formulae}
\label{sec:TypesTermsForms}

HOL is a typed logic whose type system resembles that of functional
programming languages. Thus there are
\begin{description}
\item[base types,] 
in particular @{typ bool}, the type of truth values,
@{typ nat}, the type of natural numbers ($\mathbb{N}$), and @{typ int},
the type of mathematical integers ($\mathbb{Z}$).
\item[type constructors,]
 in particular @{text list}, the type of
lists, and @{text set}, the type of sets. Type constructors are written
postfix, e.g.\ @{typ "nat list"} is the type of lists whose elements are
natural numbers.
\item[function types,]
denoted by @{text"\<Rightarrow>"}.
\item[type variables,]
  denoted by @{typ 'a}, @{typ 'b} etc., just like in ML\@.
\end{description}

\concept{Terms} are formed as in functional programming by
applying functions to arguments. If @{text f} is a function of type
@{text"\<tau>\<^isub>1 \<Rightarrow> \<tau>\<^isub>2"} and @{text t} is a term of type
@{text"\<tau>\<^isub>1"} then @{term"f t"} is a term of type @{text"\<tau>\<^isub>2"}. We write @{text "t :: \<tau>"} to mean that term @{text t} has type @{text \<tau>}.

\begin{warn}
There are many predefined infix symbols like @{text "+"} and @{text"\<le>"}.
The name of the corresponding binary function is @{term"op +"},
not just @{text"+"}. That is, @{term"x + y"} is syntactic sugar for
\noquotes{@{term[source]"op + x y"}}.
\end{warn}

HOL also supports some basic constructs from functional programming:
\begin{quote}
@{text "(if b then t\<^isub>1 else t\<^isub>2)"}\\
@{text "(let x = t in u)"}\\
@{text "(case t of pat\<^isub>1 \<Rightarrow> t\<^isub>1 | \<dots> | pat\<^isub>n \<Rightarrow> t\<^isub>n)"}
\end{quote}
\begin{warn}
The above three constructs must always be enclosed in parentheses
if they occur inside other constructs.
\end{warn}
Terms may also contain @{text "\<lambda>"}-abstractions. For example,
@{term "\<lambda>x. x"} is the identity function.

\concept{Formulae} are terms of type @{text bool}.
There are the basic constants @{term True} and @{term False} and
the usual logical connectives (in decreasing order of precedence):
@{text"\<not>"}, @{text"\<and>"}, @{text"\<or>"}, @{text"\<longrightarrow>"}.

\concept{Equality} is available in the form of the infix function @{text "="}
of type @{typ "'a \<Rightarrow> 'a \<Rightarrow> bool"}. It also works for formulas, where
it means ``if and only if''.

\concept{Quantifiers} are written @{prop"\<forall>x. P"} and @{prop"\<exists>x. P"}.

Isabelle automatically computes the type of each variable in a term. This is
called \concept{type inference}.  Despite type inference, it is sometimes
necessary to attach explicit \concept{type constraints} (or \concept{type
annotations}) to a variable or term.  The syntax is @{text "t :: \<tau>"} as in
\mbox{\noquotes{@{prop[source] "m < (n::nat)"}}}. Type constraints may be
needed to
disambiguate terms involving overloaded functions such as @{text "+"}, @{text
"*"} and @{text"\<le>"}.

Finally there are the universal quantifier @{text"\<And>"} and the implication
@{text"\<Longrightarrow>"}. They are part of the Isabelle framework, not the logic
HOL. Logically, they agree with their HOL counterparts @{text"\<forall>"} and
@{text"\<longrightarrow>"}, but operationally they behave differently. This will become
clearer as we go along.
\begin{warn}
Right-arrows of all kinds always associate to the right. In particular,
the formula
@{text"A\<^isub>1 \<Longrightarrow> A\<^isub>2 \<Longrightarrow> A\<^isub>3"} means @{text "A\<^isub>1 \<Longrightarrow> (A\<^isub>2 \<Longrightarrow> A\<^isub>3)"}.
The (Isabelle specific) notation \mbox{@{text"\<lbrakk> A\<^isub>1; \<dots>; A\<^isub>n \<rbrakk> \<Longrightarrow> A"}}
is short for the iterated implication \mbox{@{text"A\<^isub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^isub>n \<Longrightarrow> A"}}.
Sometimes we also employ inference rule notation:
\inferrule{\mbox{@{text "A\<^isub>1"}}\\ \mbox{@{text "\<dots>"}}\\ \mbox{@{text "A\<^isub>n"}}}
{\mbox{@{text A}}}
\end{warn}


\subsection{Theories}
\label{sec:Basic:Theories}

Roughly speaking, a \concept{theory} is a named collection of types,
functions, and theorems, much like a module in a programming language.
All the Isabelle text that you ever type needs to go into a theory.
The general format of a theory @{text T} is
\begin{quote}
\isacom{theory} @{text T}\\
\isacom{imports} @{text "T\<^isub>1 \<dots> T\<^isub>n"}\\
\isacom{begin}\\
\emph{definitions, theorems and proofs}\\
\isacom{end}
\end{quote}
where @{text "T\<^isub>1 \<dots> T\<^isub>n"} are the names of existing
theories that @{text T} is based on. The @{text "T\<^isub>i"} are the
direct \concept{parent theories} of @{text T}.
Everything defined in the parent theories (and their parents, recursively) is
automatically visible. Each theory @{text T} must
reside in a \concept{theory file} named @{text "T.thy"}.

\begin{warn}
HOL contains a theory @{text Main}, the union of all the basic
predefined theories like arithmetic, lists, sets, etc.
Unless you know what you are doing, always include @{text Main}
as a direct or indirect parent of all your theories.
\end{warn}

In addition to the theories that come with the Isabelle/HOL distribution
(see \url{http://isabelle.in.tum.de/library/HOL/})
there is also the \emph{Archive of Formal Proofs}
at  \url{http://afp.sourceforge.net}, a growing collection of Isabelle theories
that everybody can contribute to.

\subsection{Quotation Marks}

The textual definition of a theory follows a fixed syntax with keywords like
\isacommand{begin} and \isacommand{datatype}.  Embedded in this syntax are
the types and formulae of HOL.  To distinguish the two levels, everything
HOL-specific (terms and types) must be enclosed in quotation marks:
\texttt{"}\dots\texttt{"}. To lessen this burden, quotation marks around a
single identifier can be dropped.  When Isabelle prints a syntax error
message, it refers to the HOL syntax as the \concept{inner syntax} and the
enclosing theory language as the \concept{outer syntax}.
\begin{warn}
For reasons of readability, we almost never show the quotation marks in this
book. Consult the accompanying theory files to see where they need to go.
\end{warn}
*}
(*<*)
end
(*>*)