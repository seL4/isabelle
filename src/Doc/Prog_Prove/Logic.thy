(*<*)
theory Logic
imports LaTeXsugar
begin
(*>*)
text{*
\vspace{-5ex}
\section{Formulas}

The core syntax of formulas (\textit{form} below)
provides the standard logical constructs, in decreasing order of precedence:
\[
\begin{array}{rcl}

\mathit{form} & ::= &
  @{text"(form)"} ~\mid~
  @{const True} ~\mid~
  @{const False} ~\mid~
  @{prop "term = term"}\\
 &\mid& @{prop"\<not> form"}\index{$HOL4@\isasymnot} ~\mid~
  @{prop "form \<and> form"}\index{$HOL0@\isasymand} ~\mid~
  @{prop "form \<or> form"}\index{$HOL1@\isasymor} ~\mid~
  @{prop "form \<longrightarrow> form"}\index{$HOL2@\isasymlongrightarrow}\\
 &\mid& @{prop"\<forall>x. form"}\index{$HOL6@\isasymforall} ~\mid~  @{prop"\<exists>x. form"}\index{$HOL7@\isasymexists}
\end{array}
\]
Terms are the ones we have seen all along, built from constants, variables,
function application and @{text"\<lambda>"}-abstraction, including all the syntactic
sugar like infix symbols, @{text "if"}, @{text "case"}, etc.
\begin{warn}
Remember that formulas are simply terms of type @{text bool}. Hence
@{text "="} also works for formulas. Beware that @{text"="} has a higher
precedence than the other logical operators. Hence @{prop"s = t \<and> A"} means
@{text"(s = t) \<and> A"}, and @{prop"A\<and>B = B\<and>A"} means @{text"A \<and> (B = B) \<and> A"}.
Logical equivalence can also be written with
@{text "\<longleftrightarrow>"} instead of @{text"="}, where @{text"\<longleftrightarrow>"} has the same low
precedence as @{text"\<longrightarrow>"}. Hence @{text"A \<and> B \<longleftrightarrow> B \<and> A"} really means
@{text"(A \<and> B) \<longleftrightarrow> (B \<and> A)"}.
\end{warn}
\begin{warn}
Quantifiers need to be enclosed in parentheses if they are nested within
other constructs (just like @{text "if"}, @{text case} and @{text let}).
\end{warn}
The most frequent logical symbols and their ASCII representations are shown
in Fig.~\ref{fig:log-symbols}.
\begin{figure}
\begin{center}
\begin{tabular}{l@ {\qquad}l@ {\qquad}l}
@{text "\<forall>"} & \xsymbol{forall} & \texttt{ALL}\\
@{text "\<exists>"} & \xsymbol{exists} & \texttt{EX}\\
@{text "\<lambda>"} & \xsymbol{lambda} & \texttt{\%}\\
@{text "\<longrightarrow>"} & \texttt{-{}->}\\
@{text "\<longleftrightarrow>"} & \texttt{<->}\\
@{text "\<and>"} & \texttt{/\char`\\} & \texttt{\&}\\
@{text "\<or>"} & \texttt{\char`\\/} & \texttt{|}\\
@{text "\<not>"} & \xsymbol{not} & \texttt{\char`~}\\
@{text "\<noteq>"} & \xsymbol{noteq} & \texttt{\char`~=}
\end{tabular}
\end{center}
\caption{Logical symbols and their ASCII forms}
\label{fig:log-symbols}
\end{figure}
The first column shows the symbols, the other columns ASCII representations.
The \texttt{\char`\\}\texttt{<...>} form is always converted into the symbolic form
by the Isabelle interfaces, the treatment of the other ASCII forms
depends on the interface. The ASCII forms \texttt{/\char`\\} and
\texttt{\char`\\/}
are special in that they are merely keyboard shortcuts for the interface and
not logical symbols by themselves.
\begin{warn}
The implication @{text"\<Longrightarrow>"} is part of the Isabelle framework. It structures
theorems and proof states, separating assumptions from conclusions.
The implication @{text"\<longrightarrow>"} is part of the logic HOL and can occur inside the
formulas that make up the assumptions and conclusion.
Theorems should be of the form @{text"\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A"},
not @{text"A\<^sub>1 \<and> \<dots> \<and> A\<^sub>n \<longrightarrow> A"}. Both are logically equivalent
but the first one works better when using the theorem in further proofs.
\end{warn}

\section{Sets}
\label{sec:Sets}

Sets of elements of type @{typ 'a} have type @{typ"'a set"}\index{set@@{text set}}.
They can be finite or infinite. Sets come with the usual notation:
\begin{itemize}
\item \indexed{@{term"{}"}}{$IMP042},\quad @{text"{e\<^sub>1,\<dots>,e\<^sub>n}"}
\item @{prop"e \<in> A"}\index{$HOLSet0@\isasymin},\quad @{prop"A \<subseteq> B"}\index{$HOLSet2@\isasymsubseteq}
\item @{term"A \<union> B"}\index{$HOLSet4@\isasymunion},\quad @{term"A \<inter> B"}\index{$HOLSet5@\isasyminter},\quad @{term"A - B"},\quad @{term"-A"}
\end{itemize}
(where @{term"A-B"} and @{text"-A"} are set difference and complement)
and much more. @{const UNIV} is the set of all elements of some type.
Set comprehension\index{set comprehension} is written
@{term"{x. P}"}\index{$IMP042@@{term"{x. P}"}} rather than @{text"{x | P}"}.
\begin{warn}
In @{term"{x. P}"} the @{text x} must be a variable. Set comprehension
involving a proper term @{text t} must be written
\noquotes{@{term[source] "{t | x y. P}"}}\index{$IMP042@@{text"{t |x. P}"}},
where @{text "x y"} are those free variables in @{text t}
that occur in @{text P}.
This is just a shorthand for @{term"{v. EX x y. v = t \<and> P}"}, where
@{text v} is a new variable. For example, @{term"{x+y|x. x \<in> A}"}
is short for \noquotes{@{term[source]"{v. \<exists>x. v = x+y \<and> x \<in> A}"}}.
\end{warn}

Here are the ASCII representations of the mathematical symbols:
\begin{center}
\begin{tabular}{l@ {\quad}l@ {\quad}l}
@{text "\<in>"} & \texttt{\char`\\\char`\<in>} & \texttt{:}\\
@{text "\<subseteq>"} & \texttt{\char`\\\char`\<subseteq>} & \texttt{<=}\\
@{text "\<union>"} & \texttt{\char`\\\char`\<union>} & \texttt{Un}\\
@{text "\<inter>"} & \texttt{\char`\\\char`\<inter>} & \texttt{Int}
\end{tabular}
\end{center}
Sets also allow bounded quantifications @{prop"ALL x : A. P"} and
@{prop"EX x : A. P"}.

For the more ambitious, there are also @{text"\<Union>"}\index{$HOLSet6@\isasymUnion}
and @{text"\<Inter>"}\index{$HOLSet7@\isasymInter}:
\begin{center}
@{thm Union_eq} \qquad @{thm Inter_eq}
\end{center}
The ASCII forms of @{text"\<Union>"} are \texttt{\char`\\\char`\<Union>} and \texttt{Union},
those of @{text"\<Inter>"} are \texttt{\char`\\\char`\<Inter>} and \texttt{Inter}.
There are also indexed unions and intersections:
\begin{center}
@{thm UNION_eq} \\ @{thm INTER_eq}
\end{center}
The ASCII forms are \ \texttt{UN x:A.~B} \ and \ \texttt{INT x:A. B} \
where \texttt{x} may occur in \texttt{B}.
If \texttt{A} is \texttt{UNIV} you can just write \ \texttt{UN x.~B} \ and \ \texttt{INT x. B}.

Some other frequently useful functions on sets are the following:
\begin{center}
\begin{tabular}{l@ {\quad}l}
@{const_typ set}\index{set@@{const set}} & converts a list to the set of its elements\\
@{const_typ finite}\index{finite@@{const finite}} & is true iff its argument is finite\\
@{const_typ card}\index{card@@{const card}} & is the cardinality of a finite set\\
 & and is @{text 0} for all infinite sets\\
@{thm image_def}\index{$IMP042@@{term"f ` A"}} & is the image of a function over a set
\end{tabular}
\end{center}
See \cite{Nipkow-Main} for the wealth of further predefined functions in theory
@{theory Main}.


\subsection*{Exercises}

\exercise
Start from the data type of binary trees defined earlier:
*}

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text{*
Define a function @{text "set ::"} @{typ "'a tree \<Rightarrow> 'a set"}
that returns the elements in a tree and a function
@{text "ord ::"} @{typ "int tree \<Rightarrow> bool"}
that tests if an @{typ "int tree"} is ordered.

Define a function @{text ins} that inserts an element into an ordered @{typ "int tree"}
while maintaining the order of the tree. If the element is already in the tree, the
same tree should be returned. Prove correctness of @{text ins}:
@{prop "set(ins x t) = {x} \<union> set t"} and @{prop "ord t \<Longrightarrow> ord(ins i t)"}.
\endexercise


\section{Proof Automation}

So far we have only seen @{text simp} and \indexed{@{text auto}}{auto}: Both perform
rewriting, both can also prove linear arithmetic facts (no multiplication),
and @{text auto} is also able to prove simple logical or set-theoretic goals:
*}

lemma "\<forall>x. \<exists>y. x = y"
by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
by auto

text{* where
\begin{quote}
\isacom{by} \textit{proof-method}
\end{quote}
is short for
\begin{quote}
\isacom{apply} \textit{proof-method}\\
\isacom{done}
\end{quote}
The key characteristics of both @{text simp} and @{text auto} are
\begin{itemize}
\item They show you were they got stuck, giving you an idea how to continue.
\item They perform the obvious steps but are highly incomplete.
\end{itemize}
A proof method is \conceptnoidx{complete} if it can prove all true formulas.
There is no complete proof method for HOL, not even in theory.
Hence all our proof methods only differ in how incomplete they are.

A proof method that is still incomplete but tries harder than @{text auto} is
\indexed{@{text fastforce}}{fastforce}.  It either succeeds or fails, it acts on the first
subgoal only, and it can be modified just like @{text auto}, e.g.\
with @{text "simp add"}. Here is a typical example of what @{text fastforce}
can do:
*}

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us \<in> A \<rbrakk>
   \<Longrightarrow> \<exists>n. length us = n+n"
by fastforce

text{* This lemma is out of reach for @{text auto} because of the
quantifiers.  Even @{text fastforce} fails when the quantifier structure
becomes more complicated. In a few cases, its slow version @{text force}
succeeds where @{text fastforce} fails.

The method of choice for complex logical goals is \indexed{@{text blast}}{blast}. In the
following example, @{text T} and @{text A} are two binary predicates. It
is shown that if @{text T} is total, @{text A} is antisymmetric and @{text T} is
a subset of @{text A}, then @{text A} is a subset of @{text T}:
*}

lemma
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast

text{*
We leave it to the reader to figure out why this lemma is true.
Method @{text blast}
\begin{itemize}
\item is (in principle) a complete proof procedure for first-order formulas,
  a fragment of HOL. In practice there is a search bound.
\item does no rewriting and knows very little about equality.
\item covers logic, sets and relations.
\item either succeeds or fails.
\end{itemize}
Because of its strength in logic and sets and its weakness in equality reasoning, it complements the earlier proof methods.


\subsection{\concept{Sledgehammer}}

Command \isacom{sledgehammer} calls a number of external automatic
theorem provers (ATPs) that run for up to 30 seconds searching for a
proof. Some of these ATPs are part of the Isabelle installation, others are
queried over the internet. If successful, a proof command is generated and can
be inserted into your proof.  The biggest win of \isacom{sledgehammer} is
that it will take into account the whole lemma library and you do not need to
feed in any lemma explicitly. For example,*}

lemma "\<lbrakk> xs @ ys = ys @ xs;  length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"

txt{* cannot be solved by any of the standard proof methods, but
\isacom{sledgehammer} finds the following proof: *}

by (metis append_eq_conv_conj)

text{* We do not explain how the proof was found but what this command
means. For a start, Isabelle does not trust external tools (and in particular
not the translations from Isabelle's logic to those tools!)
and insists on a proof that it can check. This is what \indexed{@{text metis}}{metis} does.
It is given a list of lemmas and tries to find a proof just using those lemmas
(and pure logic). In contrast to using @{text simp} and friends who know a lot of
lemmas already, using @{text metis} manually is tedious because one has
to find all the relevant lemmas first. But that is precisely what
\isacom{sledgehammer} does for us.
In this case lemma @{thm[source]append_eq_conv_conj} alone suffices:
@{thm[display] append_eq_conv_conj}
We leave it to the reader to figure out why this lemma suffices to prove
the above lemma, even without any knowledge of what the functions @{const take}
and @{const drop} do. Keep in mind that the variables in the two lemmas
are independent of each other, despite the same names, and that you can
substitute arbitrary values for the free variables in a lemma.

Just as for the other proof methods we have seen, there is no guarantee that
\isacom{sledgehammer} will find a proof if it exists. Nor is
\isacom{sledgehammer} superior to the other proof methods.  They are
incomparable. Therefore it is recommended to apply @{text simp} or @{text
auto} before invoking \isacom{sledgehammer} on what is left.

\subsection{Arithmetic}

By arithmetic formulas we mean formulas involving variables, numbers, @{text
"+"}, @{text"-"}, @{text "="}, @{text "<"}, @{text "\<le>"} and the usual logical
connectives @{text"\<not>"}, @{text"\<and>"}, @{text"\<or>"}, @{text"\<longrightarrow>"},
@{text"\<longleftrightarrow>"}. Strictly speaking, this is known as \concept{linear arithmetic}
because it does not involve multiplication, although multiplication with
numbers, e.g.\ @{text"2*n"}, is allowed. Such formulas can be proved by
\indexed{@{text arith}}{arith}:
*}

lemma "\<lbrakk> (a::nat) \<le> x + b; 2*x < c \<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
by arith

text{* In fact, @{text auto} and @{text simp} can prove many linear
arithmetic formulas already, like the one above, by calling a weak but fast
version of @{text arith}. Hence it is usually not necessary to invoke
@{text arith} explicitly.

The above example involves natural numbers, but integers (type @{typ int})
and real numbers (type @{text real}) are supported as well. As are a number
of further operators like @{const min} and @{const max}. On @{typ nat} and
@{typ int}, @{text arith} can even prove theorems with quantifiers in them,
but we will not enlarge on that here.


\subsection{Trying Them All}

If you want to try all of the above automatic proof methods you simply type
\begin{isabelle}
\isacom{try}
\end{isabelle}
You can also add specific simplification and introduction rules:
\begin{isabelle}
\isacom{try} @{text"simp: \<dots> intro: \<dots>"}
\end{isabelle}
There is also a lightweight variant \isacom{try0} that does not call
sledgehammer.

\section{Single Step Proofs}

Although automation is nice, it often fails, at least initially, and you need
to find out why. When @{text fastforce} or @{text blast} simply fail, you have
no clue why. At this point, the stepwise
application of proof rules may be necessary. For example, if @{text blast}
fails on @{prop"A \<and> B"}, you want to attack the two
conjuncts @{text A} and @{text B} separately. This can
be achieved by applying \emph{conjunction introduction}
\[ @{thm[mode=Rule,show_question_marks]conjI}\ @{text conjI}
\]
to the proof state. We will now examine the details of this process.

\subsection{Instantiating Unknowns}

We had briefly mentioned earlier that after proving some theorem,
Isabelle replaces all free variables @{text x} by so called \conceptidx{unknowns}{unknown}
@{text "?x"}. We can see this clearly in rule @{thm[source] conjI}.
These unknowns can later be instantiated explicitly or implicitly:
\begin{itemize}
\item By hand, using \indexed{@{text of}}{of}.
The expression @{text"conjI[of \"a=b\" \"False\"]"}
instantiates the unknowns in @{thm[source] conjI} from left to right with the
two formulas @{text"a=b"} and @{text False}, yielding the rule
@{thm[display,mode=Rule]conjI[of "a=b" False]}

In general, @{text"th[of string\<^sub>1 \<dots> string\<^sub>n]"} instantiates
the unknowns in the theorem @{text th} from left to right with the terms
@{text string\<^sub>1} to @{text string\<^sub>n}.

\item By unification. \conceptidx{Unification}{unification} is the process of making two
terms syntactically equal by suitable instantiations of unknowns. For example,
unifying @{text"?P \<and> ?Q"} with \mbox{@{prop"a=b \<and> False"}} instantiates
@{text "?P"} with @{prop "a=b"} and @{text "?Q"} with @{prop False}.
\end{itemize}
We need not instantiate all unknowns. If we want to skip a particular one we
can just write @{text"_"} instead, for example @{text "conjI[of _ \"False\"]"}.
Unknowns can also be instantiated by name using \indexed{@{text "where"}}{where}, for example
@{text "conjI[where ?P = \"a=b\""} \isacom{and} @{text"?Q = \"False\"]"}.


\subsection{Rule Application}

\conceptidx{Rule application}{rule application} means applying a rule backwards to a proof state.
For example, applying rule @{thm[source]conjI} to a proof state
\begin{quote}
@{text"1.  \<dots>  \<Longrightarrow> A \<and> B"}
\end{quote}
results in two subgoals, one for each premise of @{thm[source]conjI}:
\begin{quote}
@{text"1.  \<dots>  \<Longrightarrow> A"}\\
@{text"2.  \<dots>  \<Longrightarrow> B"}
\end{quote}
In general, the application of a rule @{text"\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A"}
to a subgoal \mbox{@{text"\<dots> \<Longrightarrow> C"}} proceeds in two steps:
\begin{enumerate}
\item
Unify @{text A} and @{text C}, thus instantiating the unknowns in the rule.
\item
Replace the subgoal @{text C} with @{text n} new subgoals @{text"A\<^sub>1"} to @{text"A\<^sub>n"}.
\end{enumerate}
This is the command to apply rule @{text xyz}:
\begin{quote}
\isacom{apply}@{text"(rule xyz)"}\index{rule@@{text rule}}
\end{quote}
This is also called \concept{backchaining} with rule @{text xyz}.

\subsection{Introduction Rules}

Conjunction introduction (@{thm[source] conjI}) is one example of a whole
class of rules known as \conceptidx{introduction rules}{introduction rule}. They explain under which
premises some logical construct can be introduced. Here are some further
useful introduction rules:
\[
\inferrule*[right=\mbox{@{text impI}}]{\mbox{@{text"?P \<Longrightarrow> ?Q"}}}{\mbox{@{text"?P \<longrightarrow> ?Q"}}}
\qquad
\inferrule*[right=\mbox{@{text allI}}]{\mbox{@{text"\<And>x. ?P x"}}}{\mbox{@{text"\<forall>x. ?P x"}}}
\]
\[
\inferrule*[right=\mbox{@{text iffI}}]{\mbox{@{text"?P \<Longrightarrow> ?Q"}} \\ \mbox{@{text"?Q \<Longrightarrow> ?P"}}}
  {\mbox{@{text"?P = ?Q"}}}
\]
These rules are part of the logical system of \concept{natural deduction}
(e.g.\ \cite{HuthRyan}). Although we intentionally de-emphasize the basic rules
of logic in favour of automatic proof methods that allow you to take bigger
steps, these rules are helpful in locating where and why automation fails.
When applied backwards, these rules decompose the goal:
\begin{itemize}
\item @{thm[source] conjI} and @{thm[source]iffI} split the goal into two subgoals,
\item @{thm[source] impI} moves the left-hand side of a HOL implication into the list of assumptions,
\item and @{thm[source] allI} removes a @{text "\<forall>"} by turning the quantified variable into a fixed local variable of the subgoal.
\end{itemize}
Isabelle knows about these and a number of other introduction rules.
The command
\begin{quote}
\isacom{apply} @{text rule}\index{rule@@{text rule}}
\end{quote}
automatically selects the appropriate rule for the current subgoal.

You can also turn your own theorems into introduction rules by giving them
the \indexed{@{text"intro"}}{intro} attribute, analogous to the @{text simp} attribute.  In
that case @{text blast}, @{text fastforce} and (to a limited extent) @{text
auto} will automatically backchain with those theorems. The @{text intro}
attribute should be used with care because it increases the search space and
can lead to nontermination.  Sometimes it is better to use it only in
specific calls of @{text blast} and friends. For example,
@{thm[source] le_trans}, transitivity of @{text"\<le>"} on type @{typ nat},
is not an introduction rule by default because of the disastrous effect
on the search space, but can be useful in specific situations:
*}

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
by(blast intro: le_trans)

text{*
Of course this is just an example and could be proved by @{text arith}, too.

\subsection{Forward Proof}
\label{sec:forward-proof}

Forward proof means deriving new theorems from old theorems. We have already
seen a very simple form of forward proof: the @{text of} operator for
instantiating unknowns in a theorem. The big brother of @{text of} is
\indexed{@{text OF}}{OF} for applying one theorem to others. Given a theorem @{prop"A \<Longrightarrow> B"} called
@{text r} and a theorem @{text A'} called @{text r'}, the theorem @{text
"r[OF r']"} is the result of applying @{text r} to @{text r'}, where @{text
r} should be viewed as a function taking a theorem @{text A} and returning
@{text B}.  More precisely, @{text A} and @{text A'} are unified, thus
instantiating the unknowns in @{text B}, and the result is the instantiated
@{text B}. Of course, unification may also fail.
\begin{warn}
Application of rules to other rules operates in the forward direction: from
the premises to the conclusion of the rule; application of rules to proof
states operates in the backward direction, from the conclusion to the
premises.
\end{warn}

In general @{text r} can be of the form @{text"\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A"}
and there can be multiple argument theorems @{text r\<^sub>1} to @{text r\<^sub>m}
(with @{text"m \<le> n"}), in which case @{text "r[OF r\<^sub>1 \<dots> r\<^sub>m]"} is obtained
by unifying and thus proving @{text "A\<^sub>i"} with @{text "r\<^sub>i"}, @{text"i = 1\<dots>m"}.
Here is an example, where @{thm[source]refl} is the theorem
@{thm[show_question_marks] refl}:
*}

thm conjI[OF refl[of "a"] refl[of "b"]]

text{* yields the theorem @{thm conjI[OF refl[of "a"] refl[of "b"]]}.
The command \isacom{thm} merely displays the result.

Forward reasoning also makes sense in connection with proof states.
Therefore @{text blast}, @{text fastforce} and @{text auto} support a modifier
@{text dest} which instructs the proof method to use certain rules in a
forward fashion. If @{text r} is of the form \mbox{@{text "A \<Longrightarrow> B"}}, the modifier
\mbox{@{text"dest: r"}}\index{dest@@{text"dest:"}}
allows proof search to reason forward with @{text r}, i.e.\
to replace an assumption @{text A'}, where @{text A'} unifies with @{text A},
with the correspondingly instantiated @{text B}. For example, @{thm[source,show_question_marks] Suc_leD} is the theorem \mbox{@{thm Suc_leD}}, which works well for forward reasoning:
*}

lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
by(blast dest: Suc_leD)

text{* In this particular example we could have backchained with
@{thm[source] Suc_leD}, too, but because the premise is more complicated than the conclusion this can easily lead to nontermination.

%\subsection{Finding Theorems}
%
%Command \isacom{find{\isacharunderscorekeyword}theorems} searches for specific theorems in the current
%theory. Search criteria include pattern matching on terms and on names.
%For details see the Isabelle/Isar Reference Manual~\cite{IsarRef}.
%\bigskip

\begin{warn}
To ease readability we will drop the question marks
in front of unknowns from now on.
\end{warn}


\section{Inductive Definitions}
\label{sec:inductive-defs}\index{inductive definition|(}

Inductive definitions are the third important definition facility, after
datatypes and recursive function.
\ifsem
In fact, they are the key construct in the
definition of operational semantics in the second part of the book.
\fi

\subsection{An Example: Even Numbers}
\label{sec:Logic:even}

Here is a simple example of an inductively defined predicate:
\begin{itemize}
\item 0 is even
\item If $n$ is even, so is $n+2$.
\end{itemize}
The operative word ``inductive'' means that these are the only even numbers.
In Isabelle we give the two rules the names @{text ev0} and @{text evSS}
and write
*}

inductive ev :: "nat \<Rightarrow> bool" where
ev0:    "ev 0" |
evSS:  (*<*)"ev n \<Longrightarrow> ev (Suc(Suc n))"(*>*)
text_raw{* @{prop[source]"ev n \<Longrightarrow> ev (n + 2)"} *}

text{* To get used to inductive definitions, we will first prove a few
properties of @{const ev} informally before we descend to the Isabelle level.

How do we prove that some number is even, e.g.\ @{prop "ev 4"}? Simply by combining the defining rules for @{const ev}:
\begin{quote}
@{text "ev 0 \<Longrightarrow> ev (0 + 2) \<Longrightarrow> ev((0 + 2) + 2) = ev 4"}
\end{quote}

\subsubsection{Rule Induction}\index{rule induction|(}

Showing that all even numbers have some property is more complicated.  For
example, let us prove that the inductive definition of even numbers agrees
with the following recursive one:*}

fun even :: "nat \<Rightarrow> bool" where
"even 0 = True" |
"even (Suc 0) = False" |
"even (Suc(Suc n)) = even n"

text{* We prove @{prop"ev m \<Longrightarrow> even m"}.  That is, we
assume @{prop"ev m"} and by induction on the form of its derivation
prove @{prop"even m"}. There are two cases corresponding to the two rules
for @{const ev}:
\begin{description}
\item[Case @{thm[source]ev0}:]
 @{prop"ev m"} was derived by rule @{prop "ev 0"}: \\
 @{text"\<Longrightarrow>"} @{prop"m=(0::nat)"} @{text"\<Longrightarrow>"} @{text "even m = even 0 = True"}
\item[Case @{thm[source]evSS}:]
 @{prop"ev m"} was derived by rule @{prop "ev n \<Longrightarrow> ev(n+2)"}: \\
@{text"\<Longrightarrow>"} @{prop"m=n+(2::nat)"} and by induction hypothesis @{prop"even n"}\\
@{text"\<Longrightarrow>"} @{text"even m = even(n + 2) = even n = True"}
\end{description}

What we have just seen is a special case of \concept{rule induction}.
Rule induction applies to propositions of this form
\begin{quote}
@{prop "ev n \<Longrightarrow> P n"}
\end{quote}
That is, we want to prove a property @{prop"P n"}
for all even @{text n}. But if we assume @{prop"ev n"}, then there must be
some derivation of this assumption using the two defining rules for
@{const ev}. That is, we must prove
\begin{description}
\item[Case @{thm[source]ev0}:] @{prop"P(0::nat)"}
\item[Case @{thm[source]evSS}:] @{prop"\<lbrakk> ev n; P n \<rbrakk> \<Longrightarrow> P(n + 2::nat)"}
\end{description}
The corresponding rule is called @{thm[source] ev.induct} and looks like this:
\[
\inferrule{
\mbox{@{thm (prem 1) ev.induct[of "n"]}}\\
\mbox{@{thm (prem 2) ev.induct}}\\
\mbox{@{prop"!!n. \<lbrakk> ev n; P n \<rbrakk> \<Longrightarrow> P(n+2)"}}}
{\mbox{@{thm (concl) ev.induct[of "n"]}}}
\]
The first premise @{prop"ev n"} enforces that this rule can only be applied
in situations where we know that @{text n} is even.

Note that in the induction step we may not just assume @{prop"P n"} but also
\mbox{@{prop"ev n"}}, which is simply the premise of rule @{thm[source]
evSS}.  Here is an example where the local assumption @{prop"ev n"} comes in
handy: we prove @{prop"ev m \<Longrightarrow> ev(m - 2)"} by induction on @{prop"ev m"}.
Case @{thm[source]ev0} requires us to prove @{prop"ev(0 - 2)"}, which follows
from @{prop"ev 0"} because @{prop"0 - 2 = (0::nat)"} on type @{typ nat}. In
case @{thm[source]evSS} we have \mbox{@{prop"m = n+(2::nat)"}} and may assume
@{prop"ev n"}, which implies @{prop"ev (m - 2)"} because @{text"m - 2 = (n +
2) - 2 = n"}. We did not need the induction hypothesis at all for this proof (it
is just a case analysis of which rule was used) but having @{prop"ev n"}
at our disposal in case @{thm[source]evSS} was essential.
This case analysis of rules is also called ``rule inversion''
and is discussed in more detail in \autoref{ch:Isar}.

\subsubsection{In Isabelle}

Let us now recast the above informal proofs in Isabelle. For a start,
we use @{const Suc} terms instead of numerals in rule @{thm[source]evSS}:
@{thm[display] evSS}
This avoids the difficulty of unifying @{text"n+2"} with some numeral,
which is not automatic.

The simplest way to prove @{prop"ev(Suc(Suc(Suc(Suc 0))))"} is in a forward
direction: @{text "evSS[OF evSS[OF ev0]]"} yields the theorem @{thm evSS[OF
evSS[OF ev0]]}. Alternatively, you can also prove it as a lemma in backwards
fashion. Although this is more verbose, it allows us to demonstrate how each
rule application changes the proof state: *}

lemma "ev(Suc(Suc(Suc(Suc 0))))"
txt{*
@{subgoals[display,indent=0,goals_limit=1]}
*}
apply(rule evSS)
txt{*
@{subgoals[display,indent=0,goals_limit=1]}
*}
apply(rule evSS)
txt{*
@{subgoals[display,indent=0,goals_limit=1]}
*}
apply(rule ev0)
done

text{* \indent
Rule induction is applied by giving the induction rule explicitly via the
@{text"rule:"} modifier:\index{inductionrule@@{text"induction ... rule:"}}*}

lemma "ev m \<Longrightarrow> even m"
apply(induction rule: ev.induct)
by(simp_all)

text{* Both cases are automatic. Note that if there are multiple assumptions
of the form @{prop"ev t"}, method @{text induction} will induct on the leftmost
one.

As a bonus, we also prove the remaining direction of the equivalence of
@{const ev} and @{const even}:
*}

lemma "even n \<Longrightarrow> ev n"
apply(induction n rule: even.induct)

txt{* This is a proof by computation induction on @{text n} (see
\autoref{sec:recursive-funs}) that sets up three subgoals corresponding to
the three equations for @{const even}:
@{subgoals[display,indent=0]}
The first and third subgoals follow with @{thm[source]ev0} and @{thm[source]evSS}, and the second subgoal is trivially true because @{prop"even(Suc 0)"} is @{const False}:
*}

by (simp_all add: ev0 evSS)

text{* The rules for @{const ev} make perfect simplification and introduction
rules because their premises are always smaller than the conclusion. It
makes sense to turn them into simplification and introduction rules
permanently, to enhance proof automation. They are named @{thm[source] ev.intros}
\index{intros@@{text".intros"}} by Isabelle: *}

declare ev.intros[simp,intro]

text{* The rules of an inductive definition are not simplification rules by
default because, in contrast to recursive functions, there is no termination
requirement for inductive definitions.

\subsubsection{Inductive Versus Recursive}

We have seen two definitions of the notion of evenness, an inductive and a
recursive one. Which one is better? Much of the time, the recursive one is
more convenient: it allows us to do rewriting in the middle of terms, and it
expresses both the positive information (which numbers are even) and the
negative information (which numbers are not even) directly. An inductive
definition only expresses the positive information directly. The negative
information, for example, that @{text 1} is not even, has to be proved from
it (by induction or rule inversion). On the other hand, rule induction is
tailor-made for proving \mbox{@{prop"ev n \<Longrightarrow> P n"}} because it only asks you
to prove the positive cases. In the proof of @{prop"even n \<Longrightarrow> P n"} by
computation induction via @{thm[source]even.induct}, we are also presented
with the trivial negative cases. If you want the convenience of both
rewriting and rule induction, you can make two definitions and show their
equivalence (as above) or make one definition and prove additional properties
from it, for example rule induction from computation induction.

But many concepts do not admit a recursive definition at all because there is
no datatype for the recursion (for example, the transitive closure of a
relation), or the recursion would not terminate (for example,
an interpreter for a programming language). Even if there is a recursive
definition, if we are only interested in the positive information, the
inductive definition may be much simpler.

\subsection{The Reflexive Transitive Closure}
\label{sec:star}

Evenness is really more conveniently expressed recursively than inductively.
As a second and very typical example of an inductive definition we define the
reflexive transitive closure.
\ifsem
It will also be an important building block for
some of the semantics considered in the second part of the book.
\fi

The reflexive transitive closure, called @{text star} below, is a function
that maps a binary predicate to another binary predicate: if @{text r} is of
type @{text"\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool"} then @{term "star r"} is again of type @{text"\<tau> \<Rightarrow>
\<tau> \<Rightarrow> bool"}, and @{prop"star r x y"} means that @{text x} and @{text y} are in
the relation @{term"star r"}. Think @{term"r^*"} when you see @{term"star
r"}, because @{text"star r"} is meant to be the reflexive transitive closure.
That is, @{prop"star r x y"} is meant to be true if from @{text x} we can
reach @{text y} in finitely many @{text r} steps. This concept is naturally
defined inductively: *}

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

text{* The base case @{thm[source] refl} is reflexivity: @{term "x=y"}. The
step case @{thm[source]step} combines an @{text r} step (from @{text x} to
@{text y}) and a @{term"star r"} step (from @{text y} to @{text z}) into a
@{term"star r"} step (from @{text x} to @{text z}).
The ``\isacom{for}~@{text r}'' in the header is merely a hint to Isabelle
that @{text r} is a fixed parameter of @{const star}, in contrast to the
further parameters of @{const star}, which change. As a result, Isabelle
generates a simpler induction rule.

By definition @{term"star r"} is reflexive. It is also transitive, but we
need rule induction to prove that: *}

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
(*<*)
defer
apply(rename_tac u x y)
defer
(*>*)
txt{* The induction is over @{prop"star r x y"} (the first matching assumption)
and we try to prove \mbox{@{prop"star r y z \<Longrightarrow> star r x z"}},
which we abbreviate by @{prop"P x y"}. These are our two subgoals:
@{subgoals[display,indent=0]}
The first one is @{prop"P x x"}, the result of case @{thm[source]refl},
and it is trivial:\index{assumption@@{text assumption}}
*}
apply(assumption)
txt{* Let us examine subgoal @{text 2}, case @{thm[source] step}.
Assumptions @{prop"r u x"} and \mbox{@{prop"star r x y"}}
are the premises of rule @{thm[source]step}.
Assumption @{prop"star r y z \<Longrightarrow> star r x z"} is \mbox{@{prop"P x y"}},
the IH coming from @{prop"star r x y"}. We have to prove @{prop"P u y"},
which we do by assuming @{prop"star r y z"} and proving @{prop"star r u z"}.
The proof itself is straightforward: from \mbox{@{prop"star r y z"}} the IH
leads to @{prop"star r x z"} which, together with @{prop"r u x"},
leads to \mbox{@{prop"star r u z"}} via rule @{thm[source]step}:
*}
apply(metis step)
done

text{*\index{rule induction|)}

\subsection{The General Case}

Inductive definitions have approximately the following general form:
\begin{quote}
\isacom{inductive} @{text"I :: \"\<tau> \<Rightarrow> bool\""} \isacom{where}
\end{quote}
followed by a sequence of (possibly named) rules of the form
\begin{quote}
@{text "\<lbrakk> I a\<^sub>1; \<dots>; I a\<^sub>n \<rbrakk> \<Longrightarrow> I a"}
\end{quote}
separated by @{text"|"}. As usual, @{text n} can be 0.
The corresponding rule induction principle
@{text I.induct} applies to propositions of the form
\begin{quote}
@{prop "I x \<Longrightarrow> P x"}
\end{quote}
where @{text P} may itself be a chain of implications.
\begin{warn}
Rule induction is always on the leftmost premise of the goal.
Hence @{text "I x"} must be the first premise.
\end{warn}
Proving @{prop "I x \<Longrightarrow> P x"} by rule induction means proving
for every rule of @{text I} that @{text P} is invariant:
\begin{quote}
@{text "\<lbrakk> I a\<^sub>1; P a\<^sub>1; \<dots>; I a\<^sub>n; P a\<^sub>n \<rbrakk> \<Longrightarrow> P a"}
\end{quote}

The above format for inductive definitions is simplified in a number of
respects. @{text I} can have any number of arguments and each rule can have
additional premises not involving @{text I}, so-called \conceptidx{side
conditions}{side condition}. In rule inductions, these side conditions appear as additional
assumptions. The \isacom{for} clause seen in the definition of the reflexive
transitive closure simplifies the induction rule.
\index{inductive definition|)}

\subsection*{Exercises}

\begin{exercise}
Formalize the following definition of palindromes
\begin{itemize}
\item The empty list and a singleton list are palindromes.
\item If @{text xs} is a palindrome, so is @{term "a # xs @ [a]"}.
\end{itemize}
as an inductive predicate @{text "palindrome ::"} @{typ "'a list \<Rightarrow> bool"}
and prove that @{prop "rev xs = xs"} if @{text xs} is a palindrome.
\end{exercise}

\exercise
We could also have defined @{const star} as follows:
*}

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

text{*
The single @{text r} step is performed after rather than before the @{text star'}
steps. Prove @{prop "star' r x y \<Longrightarrow> star r x y"} and
@{prop "star r x y \<Longrightarrow> star r' x y"}. You may need lemmas.
Note that rule induction fails
if the assumption about the inductive predicate is not the first assumption.
\endexercise

\begin{exercise}\label{exe:iter}
Analogous to @{const star}, give an inductive definition of the @{text n}-fold iteration
of a relation @{text r}: @{term "iter r n x y"} should hold if there are @{text x\<^sub>0}, \dots, @{text x\<^sub>n}
such that @{prop"x = x\<^sub>0"}, @{prop"x\<^sub>n = y"} and @{text"r x\<^bsub>i\<^esub> x\<^bsub>i+1\<^esub>"} for
all @{prop"i < n"}. Correct and prove the following claim:
@{prop"star r x y \<Longrightarrow> iter r n x y"}.
\end{exercise}

\begin{exercise}
A context-free grammar can be seen as an inductive definition where each
nonterminal $A$ is an inductively defined predicate on lists of terminal
symbols: $A(w)$ means that $w$ is in the language generated by $A$.
For example, the production $S \to a S b$ can be viewed as the implication
@{prop"S w \<Longrightarrow> S (a # w @ [b])"} where @{text a} and @{text b} are terminal symbols,
i.e., elements of some alphabet. The alphabet can be defined like this:
\isacom{datatype} @{text"alpha = a | b | \<dots>"}

Define the two grammars (where $\varepsilon$ is the empty word)
\[
\begin{array}{r@ {\quad}c@ {\quad}l}
S &\to& \varepsilon \quad\mid\quad aSb \quad\mid\quad SS \\
T &\to& \varepsilon \quad\mid\quad TaTb
\end{array}
\]
as two inductive predicates.
If you think of @{text a} and @{text b} as ``@{text "("}'' and  ``@{text ")"}'',
the grammar defines strings of balanced parentheses.
Prove @{prop"T w \<Longrightarrow> S w"} and \mbox{@{prop "S w \<Longrightarrow> T w"}} separately and conclude
@{prop "S w = T w"}.
\end{exercise}

\ifsem
\begin{exercise}
In \autoref{sec:AExp} we defined a recursive evaluation function
@{text "aval :: aexp \<Rightarrow> state \<Rightarrow> val"}.
Define an inductive evaluation predicate
@{text "aval_rel :: aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"}
and prove that it agrees with the recursive function:
@{prop "aval_rel a s v \<Longrightarrow> aval a s = v"}, 
@{prop "aval a s = v \<Longrightarrow> aval_rel a s v"} and thus
\noquotes{@{prop [source] "aval_rel a s v \<longleftrightarrow> aval a s = v"}}.
\end{exercise}

\begin{exercise}
Consider the stack machine from Chapter~3
and recall the concept of \concept{stack underflow}
from Exercise~\ref{exe:stack-underflow}.
Define an inductive predicate
@{text "ok :: nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool"}
such that @{text "ok n is n'"} means that with any initial stack of length
@{text n} the instructions @{text "is"} can be executed
without stack underflow and that the final stack has length @{text n'}.
Prove that @{text ok} correctly computes the final stack size
@{prop[display] "\<lbrakk>ok n is n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"}
and that instruction sequences generated by @{text comp}
cannot cause stack underflow: \ @{text "ok n (comp a) ?"} \ for
some suitable value of @{text "?"}.
\end{exercise}
\fi
*}
(*<*)
end
(*>*)
