(*<*)
theory Logic
imports LaTeXsugar
begin
(*>*)
text\<open>
\vspace{-5ex}
\section{Formulas}

The core syntax of formulas (\textit{form} below)
provides the standard logical constructs, in decreasing order of precedence:
\[
\begin{array}{rcl}

\mathit{form} & ::= &
  \<open>(form)\<close> ~\mid~
  \<^const>\<open>True\<close> ~\mid~
  \<^const>\<open>False\<close> ~\mid~
  \<^prop>\<open>term = term\<close>\\
 &\mid& \<^prop>\<open>\<not> form\<close>\index{$HOL4@\isasymnot} ~\mid~
  \<^prop>\<open>form \<and> form\<close>\index{$HOL0@\isasymand} ~\mid~
  \<^prop>\<open>form \<or> form\<close>\index{$HOL1@\isasymor} ~\mid~
  \<^prop>\<open>form \<longrightarrow> form\<close>\index{$HOL2@\isasymlongrightarrow}\\
 &\mid& \<^prop>\<open>\<forall>x. form\<close>\index{$HOL6@\isasymforall} ~\mid~  \<^prop>\<open>\<exists>x. form\<close>\index{$HOL7@\isasymexists}
\end{array}
\]
Terms are the ones we have seen all along, built from constants, variables,
function application and \<open>\<lambda>\<close>-abstraction, including all the syntactic
sugar like infix symbols, \<open>if\<close>, \<open>case\<close>, etc.
\begin{warn}
Remember that formulas are simply terms of type \<open>bool\<close>. Hence
\<open>=\<close> also works for formulas. Beware that \<open>=\<close> has a higher
precedence than the other logical operators. Hence \<^prop>\<open>s = t \<and> A\<close> means
\<open>(s = t) \<and> A\<close>, and \<^prop>\<open>A\<and>B = B\<and>A\<close> means \<open>A \<and> (B = B) \<and> A\<close>.
Logical equivalence can also be written with
\<open>\<longleftrightarrow>\<close> instead of \<open>=\<close>, where \<open>\<longleftrightarrow>\<close> has the same low
precedence as \<open>\<longrightarrow>\<close>. Hence \<open>A \<and> B \<longleftrightarrow> B \<and> A\<close> really means
\<open>(A \<and> B) \<longleftrightarrow> (B \<and> A)\<close>.
\end{warn}
\begin{warn}
Quantifiers need to be enclosed in parentheses if they are nested within
other constructs (just like \<open>if\<close>, \<open>case\<close> and \<open>let\<close>).
\end{warn}
The most frequent logical symbols and their ASCII representations are shown
in Fig.~\ref{fig:log-symbols}.
\begin{figure}
\begin{center}
\begin{tabular}{l@ {\qquad}l@ {\qquad}l}
\<open>\<forall>\<close> & \xsymbol{forall} & \texttt{ALL}\\
\<open>\<exists>\<close> & \xsymbol{exists} & \texttt{EX}\\
\<open>\<lambda>\<close> & \xsymbol{lambda} & \texttt{\%}\\
\<open>\<longrightarrow>\<close> & \texttt{-{\kern0pt}->}\\
\<open>\<longleftrightarrow>\<close> & \texttt{<->}\\
\<open>\<and>\<close> & \texttt{/\char`\\} & \texttt{\&}\\
\<open>\<or>\<close> & \texttt{\char`\\/} & \texttt{|}\\
\<open>\<not>\<close> & \xsymbol{not} & \texttt{\char`~}\\
\<open>\<noteq>\<close> & \xsymbol{noteq} & \texttt{\char`~=}
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
The implication \<open>\<Longrightarrow>\<close> is part of the Isabelle framework. It structures
theorems and proof states, separating assumptions from conclusions.
The implication \<open>\<longrightarrow>\<close> is part of the logic HOL and can occur inside the
formulas that make up the assumptions and conclusion.
Theorems should be of the form \<open>\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A\<close>,
not \<open>A\<^sub>1 \<and> \<dots> \<and> A\<^sub>n \<longrightarrow> A\<close>. Both are logically equivalent
but the first one works better when using the theorem in further proofs.

The ASCII representation of \<open>\<lbrakk>\<close> and \<open>\<rbrakk>\<close> is \texttt{[|} and \texttt{|]}.
\end{warn}

\section{Sets}
\label{sec:Sets}

Sets of elements of type \<^typ>\<open>'a\<close> have type \<^typ>\<open>'a set\<close>\index{set@\<open>set\<close> (type)}.
They can be finite or infinite. Sets come with the usual notation:
\begin{itemize}
\item \indexed{\<^term>\<open>{}\<close>}{$IMP042},\quad \<open>{e\<^sub>1,\<dots>,e\<^sub>n}\<close>
\item \<^prop>\<open>e \<in> A\<close>\index{$HOLSet0@\isasymin},\quad \<^prop>\<open>A \<subseteq> B\<close>\index{$HOLSet2@\isasymsubseteq}
\item \<^term>\<open>A \<union> B\<close>\index{$HOLSet4@\isasymunion},\quad \<^term>\<open>A \<inter> B\<close>\index{$HOLSet5@\isasyminter},\quad \<^term>\<open>A - B\<close>,\quad \<^term>\<open>-A\<close>
\end{itemize}
(where \<^term>\<open>A-B\<close> and \<open>-A\<close> are set difference and complement)
and much more. \<^const>\<open>UNIV\<close> is the set of all elements of some type.
Set comprehension\index{set comprehension} is written
\<^term>\<open>{x. P}\<close>\index{$IMP042@\<^term>\<open>{x. P}\<close>} rather than \<open>{x | P}\<close>.
\begin{warn}
In \<^term>\<open>{x. P}\<close> the \<open>x\<close> must be a variable. Set comprehension
involving a proper term \<open>t\<close> must be written
\noquotes{@{term[source] "{t | x y. P}"}}\index{$IMP042@\<open>{t |x. P}\<close>},
where \<open>x y\<close> are those free variables in \<open>t\<close>
that occur in \<open>P\<close>.
This is just a shorthand for \<^term>\<open>{v. \<exists>x y. v = t \<and> P}\<close>, where
\<open>v\<close> is a new variable. For example, \<^term>\<open>{x+y|x. x \<in> A}\<close>
is short for \noquotes{@{term[source]"{v. \<exists>x. v = x+y \<and> x \<in> A}"}}.
\end{warn}

Here are the ASCII representations of the mathematical symbols:
\begin{center}
\begin{tabular}{l@ {\quad}l@ {\quad}l}
\<open>\<in>\<close> & \texttt{\char`\\\char`\<in>} & \texttt{:}\\
\<open>\<subseteq>\<close> & \texttt{\char`\\\char`\<subseteq>} & \texttt{<=}\\
\<open>\<union>\<close> & \texttt{\char`\\\char`\<union>} & \texttt{Un}\\
\<open>\<inter>\<close> & \texttt{\char`\\\char`\<inter>} & \texttt{Int}
\end{tabular}
\end{center}
Sets also allow bounded quantifications \<^prop>\<open>\<forall>x \<in> A. P\<close> and
\<^prop>\<open>\<exists>x \<in> A. P\<close>.

For the more ambitious, there are also \<open>\<Union>\<close>\index{$HOLSet6@\isasymUnion}
and \<open>\<Inter>\<close>\index{$HOLSet7@\isasymInter}:
\begin{center}
@{thm Union_eq} \qquad @{thm Inter_eq}
\end{center}
The ASCII forms of \<open>\<Union>\<close> are \texttt{\char`\\\char`\<Union>} and \texttt{Union},
those of \<open>\<Inter>\<close> are \texttt{\char`\\\char`\<Inter>} and \texttt{Inter}.
There are also indexed unions and intersections:
\begin{center}
@{thm[eta_contract=false] UNION_eq} \\ @{thm[eta_contract=false] INTER_eq}
\end{center}
The ASCII forms are \ \texttt{UN x:A.~B} \ and \ \texttt{INT x:A. B} \
where \texttt{x} may occur in \texttt{B}.
If \texttt{A} is \texttt{UNIV} you can write \ \texttt{UN x.~B} \ and \ \texttt{INT x. B}.

Some other frequently useful functions on sets are the following:
\begin{center}
\begin{tabular}{l@ {\quad}l}
@{const_typ set}\index{set@\<^const>\<open>set\<close> (constant)} & converts a list to the set of its elements\\
@{const_typ finite}\index{finite@\<^const>\<open>finite\<close>} & is true iff its argument is finite\\
\noquotes{@{term[source] "card :: 'a set \<Rightarrow> nat"}}\index{card@\<^const>\<open>card\<close>} & is the cardinality of a finite set\\
 & and is \<open>0\<close> for all infinite sets\\
@{thm image_def}\index{$IMP042@\<^term>\<open>f ` A\<close>} & is the image of a function over a set
\end{tabular}
\end{center}
See \<^cite>\<open>"Nipkow-Main"\<close> for the wealth of further predefined functions in theory
\<^theory>\<open>Main\<close>.


\subsection*{Exercises}

\exercise
Start from the data type of binary trees defined earlier:
\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text\<open>
Define a function \<open>set ::\<close> \<^typ>\<open>'a tree \<Rightarrow> 'a set\<close>
that returns the elements in a tree and a function
\<open>ord ::\<close> \<^typ>\<open>int tree \<Rightarrow> bool\<close>
that tests if an \<^typ>\<open>int tree\<close> is ordered.

Define a function \<open>ins\<close> that inserts an element into an ordered \<^typ>\<open>int tree\<close>
while maintaining the order of the tree. If the element is already in the tree, the
same tree should be returned. Prove correctness of \<open>ins\<close>:
\<^prop>\<open>set(ins x t) = {x} \<union> set t\<close> and \<^prop>\<open>ord t \<Longrightarrow> ord(ins i t)\<close>.
\endexercise


\section{Proof Automation}

So far we have only seen \<open>simp\<close> and \indexed{\<open>auto\<close>}{auto}: Both perform
rewriting, both can also prove linear arithmetic facts (no multiplication),
and \<open>auto\<close> is also able to prove simple logical or set-theoretic goals:
\<close>

lemma "\<forall>x. \<exists>y. x = y"
by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
by auto

text\<open>where
\begin{quote}
\isacom{by} \textit{proof-method}
\end{quote}
is short for
\begin{quote}
\isacom{apply} \textit{proof-method}\\
\isacom{done}
\end{quote}
The key characteristics of both \<open>simp\<close> and \<open>auto\<close> are
\begin{itemize}
\item They show you where they got stuck, giving you an idea how to continue.
\item They perform the obvious steps but are highly incomplete.
\end{itemize}
A proof method is \conceptnoidx{complete} if it can prove all true formulas.
There is no complete proof method for HOL, not even in theory.
Hence all our proof methods only differ in how incomplete they are.

A proof method that is still incomplete but tries harder than \<open>auto\<close> is
\indexed{\<open>fastforce\<close>}{fastforce}.  It either succeeds or fails, it acts on the first
subgoal only, and it can be modified like \<open>auto\<close>, e.g.,
with \<open>simp add\<close>. Here is a typical example of what \<open>fastforce\<close>
can do:
\<close>

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us \<in> A \<rbrakk>
   \<Longrightarrow> \<exists>n. length us = n+n"
by fastforce

text\<open>This lemma is out of reach for \<open>auto\<close> because of the
quantifiers.  Even \<open>fastforce\<close> fails when the quantifier structure
becomes more complicated. In a few cases, its slow version \<open>force\<close>
succeeds where \<open>fastforce\<close> fails.

The method of choice for complex logical goals is \indexed{\<open>blast\<close>}{blast}. In the
following example, \<open>T\<close> and \<open>A\<close> are two binary predicates. It
is shown that if \<open>T\<close> is total, \<open>A\<close> is antisymmetric and \<open>T\<close> is
a subset of \<open>A\<close>, then \<open>A\<close> is a subset of \<open>T\<close>:
\<close>

lemma
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast

text\<open>
We leave it to the reader to figure out why this lemma is true.
Method \<open>blast\<close>
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
feed in any lemma explicitly. For example,\<close>

lemma "\<lbrakk> xs @ ys = ys @ xs;  length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"

txt\<open>cannot be solved by any of the standard proof methods, but
\isacom{sledgehammer} finds the following proof:\<close>

by (metis append_eq_conv_conj)

text\<open>We do not explain how the proof was found but what this command
means. For a start, Isabelle does not trust external tools (and in particular
not the translations from Isabelle's logic to those tools!)
and insists on a proof that it can check. This is what \indexed{\<open>metis\<close>}{metis} does.
It is given a list of lemmas and tries to find a proof using just those lemmas
(and pure logic). In contrast to using \<open>simp\<close> and friends who know a lot of
lemmas already, using \<open>metis\<close> manually is tedious because one has
to find all the relevant lemmas first. But that is precisely what
\isacom{sledgehammer} does for us.
In this case lemma @{thm[source]append_eq_conv_conj} alone suffices:
@{thm[display] append_eq_conv_conj}
We leave it to the reader to figure out why this lemma suffices to prove
the above lemma, even without any knowledge of what the functions \<^const>\<open>take\<close>
and \<^const>\<open>drop\<close> do. Keep in mind that the variables in the two lemmas
are independent of each other, despite the same names, and that you can
substitute arbitrary values for the free variables in a lemma.

Just as for the other proof methods we have seen, there is no guarantee that
\isacom{sledgehammer} will find a proof if it exists. Nor is
\isacom{sledgehammer} superior to the other proof methods.  They are
incomparable. Therefore it is recommended to apply \<open>simp\<close> or \<open>auto\<close> before invoking \isacom{sledgehammer} on what is left.

\subsection{Arithmetic}

By arithmetic formulas we mean formulas involving variables, numbers, \<open>+\<close>, \<open>-\<close>, \<open>=\<close>, \<open><\<close>, \<open>\<le>\<close> and the usual logical
connectives \<open>\<not>\<close>, \<open>\<and>\<close>, \<open>\<or>\<close>, \<open>\<longrightarrow>\<close>,
\<open>\<longleftrightarrow>\<close>. Strictly speaking, this is known as \concept{linear arithmetic}
because it does not involve multiplication, although multiplication with
numbers, e.g., \<open>2*n\<close>, is allowed. Such formulas can be proved by
\indexed{\<open>arith\<close>}{arith}:
\<close>

lemma "\<lbrakk> (a::nat) \<le> x + b; 2*x < c \<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
by arith

text\<open>In fact, \<open>auto\<close> and \<open>simp\<close> can prove many linear
arithmetic formulas already, like the one above, by calling a weak but fast
version of \<open>arith\<close>. Hence it is usually not necessary to invoke
\<open>arith\<close> explicitly.

The above example involves natural numbers, but integers (type \<^typ>\<open>int\<close>)
and real numbers (type \<open>real\<close>) are supported as well. As are a number
of further operators like \<^const>\<open>min\<close> and \<^const>\<open>max\<close>. On \<^typ>\<open>nat\<close> and
\<^typ>\<open>int\<close>, \<open>arith\<close> can even prove theorems with quantifiers in them,
but we will not enlarge on that here.


\subsection{Trying Them All}

If you want to try all of the above automatic proof methods you simply type
\begin{isabelle}
\isacom{try}
\end{isabelle}
There is also a lightweight variant \isacom{try0} that does not call
sledgehammer. If desired, specific simplification and introduction rules
can be added:
\begin{isabelle}
\isacom{try0} \<open>simp: \<dots> intro: \<dots>\<close>
\end{isabelle}

\section{Single Step Proofs}

Although automation is nice, it often fails, at least initially, and you need
to find out why. When \<open>fastforce\<close> or \<open>blast\<close> simply fail, you have
no clue why. At this point, the stepwise
application of proof rules may be necessary. For example, if \<open>blast\<close>
fails on \<^prop>\<open>A \<and> B\<close>, you want to attack the two
conjuncts \<open>A\<close> and \<open>B\<close> separately. This can
be achieved by applying \emph{conjunction introduction}
\[ @{thm[mode=Rule,show_question_marks]conjI}\ \<open>conjI\<close>
\]
to the proof state. We will now examine the details of this process.

\subsection{Instantiating Unknowns}

We had briefly mentioned earlier that after proving some theorem,
Isabelle replaces all free variables \<open>x\<close> by so called \conceptidx{unknowns}{unknown}
\<open>?x\<close>. We can see this clearly in rule @{thm[source] conjI}.
These unknowns can later be instantiated explicitly or implicitly:
\begin{itemize}
\item By hand, using \indexed{\<open>of\<close>}{of}.
The expression \<open>conjI[of "a=b" "False"]\<close>
instantiates the unknowns in @{thm[source] conjI} from left to right with the
two formulas \<open>a=b\<close> and \<open>False\<close>, yielding the rule
@{thm[display,mode=Rule,margin=100]conjI[of "a=b" False]}

In general, \<open>th[of string\<^sub>1 \<dots> string\<^sub>n]\<close> instantiates
the unknowns in the theorem \<open>th\<close> from left to right with the terms
\<open>string\<^sub>1\<close> to \<open>string\<^sub>n\<close>.

\item By unification. \conceptidx{Unification}{unification} is the process of making two
terms syntactically equal by suitable instantiations of unknowns. For example,
unifying \<open>?P \<and> ?Q\<close> with \mbox{\<^prop>\<open>a=b \<and> False\<close>} instantiates
\<open>?P\<close> with \<^prop>\<open>a=b\<close> and \<open>?Q\<close> with \<^prop>\<open>False\<close>.
\end{itemize}
We need not instantiate all unknowns. If we want to skip a particular one we
can write \<open>_\<close> instead, for example \<open>conjI[of _ "False"]\<close>.
Unknowns can also be instantiated by name using \indexed{\<open>where\<close>}{where}, for example
\<open>conjI[where ?P = "a=b"\<close> \isacom{and} \<open>?Q = "False"]\<close>.


\subsection{Rule Application}

\conceptidx{Rule application}{rule application} means applying a rule backwards to a proof state.
For example, applying rule @{thm[source]conjI} to a proof state
\begin{quote}
\<open>1.  \<dots>  \<Longrightarrow> A \<and> B\<close>
\end{quote}
results in two subgoals, one for each premise of @{thm[source]conjI}:
\begin{quote}
\<open>1.  \<dots>  \<Longrightarrow> A\<close>\\
\<open>2.  \<dots>  \<Longrightarrow> B\<close>
\end{quote}
In general, the application of a rule \<open>\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A\<close>
to a subgoal \mbox{\<open>\<dots> \<Longrightarrow> C\<close>} proceeds in two steps:
\begin{enumerate}
\item
Unify \<open>A\<close> and \<open>C\<close>, thus instantiating the unknowns in the rule.
\item
Replace the subgoal \<open>C\<close> with \<open>n\<close> new subgoals \<open>A\<^sub>1\<close> to \<open>A\<^sub>n\<close>.
\end{enumerate}
This is the command to apply rule \<open>xyz\<close>:
\begin{quote}
\isacom{apply}\<open>(rule xyz)\<close>\index{rule@\<open>rule\<close>}
\end{quote}
This is also called \concept{backchaining} with rule \<open>xyz\<close>.

\subsection{Introduction Rules}

Conjunction introduction (@{thm[source] conjI}) is one example of a whole
class of rules known as \conceptidx{introduction rules}{introduction rule}. They explain under which
premises some logical construct can be introduced. Here are some further
useful introduction rules:
\[
\inferrule*[right=\mbox{\<open>impI\<close>}]{\mbox{\<open>?P \<Longrightarrow> ?Q\<close>}}{\mbox{\<open>?P \<longrightarrow> ?Q\<close>}}
\qquad
\inferrule*[right=\mbox{\<open>allI\<close>}]{\mbox{\<open>\<And>x. ?P x\<close>}}{\mbox{\<open>\<forall>x. ?P x\<close>}}
\]
\[
\inferrule*[right=\mbox{\<open>iffI\<close>}]{\mbox{\<open>?P \<Longrightarrow> ?Q\<close>} \\ \mbox{\<open>?Q \<Longrightarrow> ?P\<close>}}
  {\mbox{\<open>?P = ?Q\<close>}}
\]
These rules are part of the logical system of \concept{natural deduction}
(e.g., \<^cite>\<open>HuthRyan\<close>). Although we intentionally de-emphasize the basic rules
of logic in favour of automatic proof methods that allow you to take bigger
steps, these rules are helpful in locating where and why automation fails.
When applied backwards, these rules decompose the goal:
\begin{itemize}
\item @{thm[source] conjI} and @{thm[source]iffI} split the goal into two subgoals,
\item @{thm[source] impI} moves the left-hand side of a HOL implication into the list of assumptions,
\item and @{thm[source] allI} removes a \<open>\<forall>\<close> by turning the quantified variable into a fixed local variable of the subgoal.
\end{itemize}
Isabelle knows about these and a number of other introduction rules.
The command
\begin{quote}
\isacom{apply} \<open>rule\<close>\index{rule@\<open>rule\<close>}
\end{quote}
automatically selects the appropriate rule for the current subgoal.

You can also turn your own theorems into introduction rules by giving them
the \indexed{\<open>intro\<close>}{intro} attribute, analogous to the \<open>simp\<close> attribute.  In
that case \<open>blast\<close>, \<open>fastforce\<close> and (to a limited extent) \<open>auto\<close> will automatically backchain with those theorems. The \<open>intro\<close>
attribute should be used with care because it increases the search space and
can lead to nontermination.  Sometimes it is better to use it only in
specific calls of \<open>blast\<close> and friends. For example,
@{thm[source] le_trans}, transitivity of \<open>\<le>\<close> on type \<^typ>\<open>nat\<close>,
is not an introduction rule by default because of the disastrous effect
on the search space, but can be useful in specific situations:
\<close>

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
by(blast intro: le_trans)

text\<open>
Of course this is just an example and could be proved by \<open>arith\<close>, too.

\subsection{Forward Proof}
\label{sec:forward-proof}

Forward proof means deriving new theorems from old theorems. We have already
seen a very simple form of forward proof: the \<open>of\<close> operator for
instantiating unknowns in a theorem. The big brother of \<open>of\<close> is
\indexed{\<open>OF\<close>}{OF} for applying one theorem to others. Given a theorem \<^prop>\<open>A \<Longrightarrow> B\<close> called
\<open>r\<close> and a theorem \<open>A'\<close> called \<open>r'\<close>, the theorem \<open>r[OF r']\<close> is the result of applying \<open>r\<close> to \<open>r'\<close>, where \<open>r\<close> should be viewed as a function taking a theorem \<open>A\<close> and returning
\<open>B\<close>.  More precisely, \<open>A\<close> and \<open>A'\<close> are unified, thus
instantiating the unknowns in \<open>B\<close>, and the result is the instantiated
\<open>B\<close>. Of course, unification may also fail.
\begin{warn}
Application of rules to other rules operates in the forward direction: from
the premises to the conclusion of the rule; application of rules to proof
states operates in the backward direction, from the conclusion to the
premises.
\end{warn}

In general \<open>r\<close> can be of the form \<open>\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A\<close>
and there can be multiple argument theorems \<open>r\<^sub>1\<close> to \<open>r\<^sub>m\<close>
(with \<open>m \<le> n\<close>), in which case \<open>r[OF r\<^sub>1 \<dots> r\<^sub>m]\<close> is obtained
by unifying and thus proving \<open>A\<^sub>i\<close> with \<open>r\<^sub>i\<close>, \<open>i = 1\<dots>m\<close>.
Here is an example, where @{thm[source]refl} is the theorem
@{thm[show_question_marks] refl}:
\<close>

thm conjI[OF refl[of "a"] refl[of "b"]]

text\<open>yields the theorem @{thm conjI[OF refl[of "a"] refl[of "b"]]}.
The command \isacom{thm} merely displays the result.

Forward reasoning also makes sense in connection with proof states.
Therefore \<open>blast\<close>, \<open>fastforce\<close> and \<open>auto\<close> support a modifier
\<open>dest\<close> which instructs the proof method to use certain rules in a
forward fashion. If \<open>r\<close> is of the form \mbox{\<open>A \<Longrightarrow> B\<close>}, the modifier
\mbox{\<open>dest: r\<close>}\index{dest@\<open>dest:\<close>}
allows proof search to reason forward with \<open>r\<close>, i.e.,
to replace an assumption \<open>A'\<close>, where \<open>A'\<close> unifies with \<open>A\<close>,
with the correspondingly instantiated \<open>B\<close>. For example, @{thm[source,show_question_marks] Suc_leD} is the theorem \mbox{@{thm Suc_leD}}, which works well for forward reasoning:
\<close>

lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
by(blast dest: Suc_leD)

text\<open>In this particular example we could have backchained with
@{thm[source] Suc_leD}, too, but because the premise is more complicated than the conclusion this can easily lead to nontermination.

%\subsection{Finding Theorems}
%
%Command \isacom{find{\isacharunderscorekeyword}theorems} searches for specific theorems in the current
%theory. Search criteria include pattern matching on terms and on names.
%For details see the Isabelle/Isar Reference Manual~\<^cite>\<open>IsarRef\<close>.
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
In Isabelle we give the two rules the names \<open>ev0\<close> and \<open>evSS\<close>
and write
\<close>

inductive ev :: "nat \<Rightarrow> bool" where
ev0:    "ev 0" |
evSS:  (*<*)"ev n \<Longrightarrow> ev (Suc(Suc n))"(*>*)
text_raw\<open>@{prop[source]"ev n \<Longrightarrow> ev (n + 2)"}\<close>

text\<open>To get used to inductive definitions, we will first prove a few
properties of \<^const>\<open>ev\<close> informally before we descend to the Isabelle level.

How do we prove that some number is even, e.g., \<^prop>\<open>ev 4\<close>? Simply by combining the defining rules for \<^const>\<open>ev\<close>:
\begin{quote}
\<open>ev 0 \<Longrightarrow> ev (0 + 2) \<Longrightarrow> ev((0 + 2) + 2) = ev 4\<close>
\end{quote}

\subsubsection{Rule Induction}\index{rule induction|(}

Showing that all even numbers have some property is more complicated.  For
example, let us prove that the inductive definition of even numbers agrees
with the following recursive one:\<close>

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text\<open>We prove \<^prop>\<open>ev m \<Longrightarrow> evn m\<close>.  That is, we
assume \<^prop>\<open>ev m\<close> and by induction on the form of its derivation
prove \<^prop>\<open>evn m\<close>. There are two cases corresponding to the two rules
for \<^const>\<open>ev\<close>:
\begin{description}
\item[Case @{thm[source]ev0}:]
 \<^prop>\<open>ev m\<close> was derived by rule \<^prop>\<open>ev 0\<close>: \\
 \<open>\<Longrightarrow>\<close> \<^prop>\<open>m=(0::nat)\<close> \<open>\<Longrightarrow>\<close> \<open>evn m = evn 0 = True\<close>
\item[Case @{thm[source]evSS}:]
 \<^prop>\<open>ev m\<close> was derived by rule \<^prop>\<open>ev n \<Longrightarrow> ev(n+2)\<close>: \\
\<open>\<Longrightarrow>\<close> \<^prop>\<open>m=n+(2::nat)\<close> and by induction hypothesis \<^prop>\<open>evn n\<close>\\
\<open>\<Longrightarrow>\<close> \<open>evn m = evn(n + 2) = evn n = True\<close>
\end{description}

What we have just seen is a special case of \concept{rule induction}.
Rule induction applies to propositions of this form
\begin{quote}
\<^prop>\<open>ev n \<Longrightarrow> P n\<close>
\end{quote}
That is, we want to prove a property \<^prop>\<open>P n\<close>
for all even \<open>n\<close>. But if we assume \<^prop>\<open>ev n\<close>, then there must be
some derivation of this assumption using the two defining rules for
\<^const>\<open>ev\<close>. That is, we must prove
\begin{description}
\item[Case @{thm[source]ev0}:] \<^prop>\<open>P(0::nat)\<close>
\item[Case @{thm[source]evSS}:] \<^prop>\<open>\<lbrakk> ev n; P n \<rbrakk> \<Longrightarrow> P(n + 2::nat)\<close>
\end{description}
The corresponding rule is called @{thm[source] ev.induct} and looks like this:
\[
\inferrule{
\mbox{@{thm (prem 1) ev.induct[of "n"]}}\\
\mbox{@{thm (prem 2) ev.induct}}\\
\mbox{\<^prop>\<open>!!n. \<lbrakk> ev n; P n \<rbrakk> \<Longrightarrow> P(n+2)\<close>}}
{\mbox{@{thm (concl) ev.induct[of "n"]}}}
\]
The first premise \<^prop>\<open>ev n\<close> enforces that this rule can only be applied
in situations where we know that \<open>n\<close> is even.

Note that in the induction step we may not just assume \<^prop>\<open>P n\<close> but also
\mbox{\<^prop>\<open>ev n\<close>}, which is simply the premise of rule @{thm[source]
evSS}.  Here is an example where the local assumption \<^prop>\<open>ev n\<close> comes in
handy: we prove \<^prop>\<open>ev m \<Longrightarrow> ev(m - 2)\<close> by induction on \<^prop>\<open>ev m\<close>.
Case @{thm[source]ev0} requires us to prove \<^prop>\<open>ev(0 - 2)\<close>, which follows
from \<^prop>\<open>ev 0\<close> because \<^prop>\<open>0 - 2 = (0::nat)\<close> on type \<^typ>\<open>nat\<close>. In
case @{thm[source]evSS} we have \mbox{\<^prop>\<open>m = n+(2::nat)\<close>} and may assume
\<^prop>\<open>ev n\<close>, which implies \<^prop>\<open>ev (m - 2)\<close> because \<open>m - 2 = (n +
2) - 2 = n\<close>. We did not need the induction hypothesis at all for this proof (it
is just a case analysis of which rule was used) but having \<^prop>\<open>ev n\<close>
at our disposal in case @{thm[source]evSS} was essential.
This case analysis of rules is also called ``rule inversion''
and is discussed in more detail in \autoref{ch:Isar}.

\subsubsection{In Isabelle}

Let us now recast the above informal proofs in Isabelle. For a start,
we use \<^const>\<open>Suc\<close> terms instead of numerals in rule @{thm[source]evSS}:
@{thm[display] evSS}
This avoids the difficulty of unifying \<open>n+2\<close> with some numeral,
which is not automatic.

The simplest way to prove \<^prop>\<open>ev(Suc(Suc(Suc(Suc 0))))\<close> is in a forward
direction: \<open>evSS[OF evSS[OF ev0]]\<close> yields the theorem @{thm evSS[OF
evSS[OF ev0]]}. Alternatively, you can also prove it as a lemma in backwards
fashion. Although this is more verbose, it allows us to demonstrate how each
rule application changes the proof state:\<close>

lemma "ev(Suc(Suc(Suc(Suc 0))))"
txt\<open>
@{subgoals[display,indent=0,goals_limit=1]}
\<close>
apply(rule evSS)
txt\<open>
@{subgoals[display,indent=0,goals_limit=1]}
\<close>
apply(rule evSS)
txt\<open>
@{subgoals[display,indent=0,goals_limit=1]}
\<close>
apply(rule ev0)
done

text\<open>\indent
Rule induction is applied by giving the induction rule explicitly via the
\<open>rule:\<close> modifier:\index{inductionrule@\<open>induction ... rule:\<close>}\<close>

lemma "ev m \<Longrightarrow> evn m"
apply(induction rule: ev.induct)
by(simp_all)

text\<open>Both cases are automatic. Note that if there are multiple assumptions
of the form \<^prop>\<open>ev t\<close>, method \<open>induction\<close> will induct on the leftmost
one.

As a bonus, we also prove the remaining direction of the equivalence of
\<^const>\<open>ev\<close> and \<^const>\<open>evn\<close>:
\<close>

lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)

txt\<open>This is a proof by computation induction on \<open>n\<close> (see
\autoref{sec:recursive-funs}) that sets up three subgoals corresponding to
the three equations for \<^const>\<open>evn\<close>:
@{subgoals[display,indent=0]}
The first and third subgoals follow with @{thm[source]ev0} and @{thm[source]evSS}, and the second subgoal is trivially true because \<^prop>\<open>evn(Suc 0)\<close> is \<^const>\<open>False\<close>:
\<close>

by (simp_all add: ev0 evSS)

text\<open>The rules for \<^const>\<open>ev\<close> make perfect simplification and introduction
rules because their premises are always smaller than the conclusion. It
makes sense to turn them into simplification and introduction rules
permanently, to enhance proof automation. They are named @{thm[source] ev.intros}
\index{intros@\<open>.intros\<close>} by Isabelle:\<close>

declare ev.intros[simp,intro]

text\<open>The rules of an inductive definition are not simplification rules by
default because, in contrast to recursive functions, there is no termination
requirement for inductive definitions.

\subsubsection{Inductive Versus Recursive}

We have seen two definitions of the notion of evenness, an inductive and a
recursive one. Which one is better? Much of the time, the recursive one is
more convenient: it allows us to do rewriting in the middle of terms, and it
expresses both the positive information (which numbers are even) and the
negative information (which numbers are not even) directly. An inductive
definition only expresses the positive information directly. The negative
information, for example, that \<open>1\<close> is not even, has to be proved from
it (by induction or rule inversion). On the other hand, rule induction is
tailor-made for proving \mbox{\<^prop>\<open>ev n \<Longrightarrow> P n\<close>} because it only asks you
to prove the positive cases. In the proof of \<^prop>\<open>evn n \<Longrightarrow> P n\<close> by
computation induction via @{thm[source]evn.induct}, we are also presented
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

The reflexive transitive closure, called \<open>star\<close> below, is a function
that maps a binary predicate to another binary predicate: if \<open>r\<close> is of
type \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> bool\<close> then \<^term>\<open>star r\<close> is again of type \<open>\<tau> \<Rightarrow>
\<tau> \<Rightarrow> bool\<close>, and \<^prop>\<open>star r x y\<close> means that \<open>x\<close> and \<open>y\<close> are in
the relation \<^term>\<open>star r\<close>. Think \<^term>\<open>r\<^sup>*\<close> when you see \<^term>\<open>star
r\<close>, because \<open>star r\<close> is meant to be the reflexive transitive closure.
That is, \<^prop>\<open>star r x y\<close> is meant to be true if from \<open>x\<close> we can
reach \<open>y\<close> in finitely many \<open>r\<close> steps. This concept is naturally
defined inductively:\<close>

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

text\<open>The base case @{thm[source] refl} is reflexivity: \<^term>\<open>x=y\<close>. The
step case @{thm[source]step} combines an \<open>r\<close> step (from \<open>x\<close> to
\<open>y\<close>) and a \<^term>\<open>star r\<close> step (from \<open>y\<close> to \<open>z\<close>) into a
\<^term>\<open>star r\<close> step (from \<open>x\<close> to \<open>z\<close>).
The ``\isacom{for}~\<open>r\<close>'' in the header is merely a hint to Isabelle
that \<open>r\<close> is a fixed parameter of \<^const>\<open>star\<close>, in contrast to the
further parameters of \<^const>\<open>star\<close>, which change. As a result, Isabelle
generates a simpler induction rule.

By definition \<^term>\<open>star r\<close> is reflexive. It is also transitive, but we
need rule induction to prove that:\<close>

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
(*<*)
defer
apply(rename_tac u x y)
defer
(*>*)
txt\<open>The induction is over \<^prop>\<open>star r x y\<close> (the first matching assumption)
and we try to prove \mbox{\<^prop>\<open>star r y z \<Longrightarrow> star r x z\<close>},
which we abbreviate by \<^prop>\<open>P x y\<close>. These are our two subgoals:
@{subgoals[display,indent=0]}
The first one is \<^prop>\<open>P x x\<close>, the result of case @{thm[source]refl},
and it is trivial:\index{assumption@\<open>assumption\<close>}
\<close>
apply(assumption)
txt\<open>Let us examine subgoal \<open>2\<close>, case @{thm[source] step}.
Assumptions \<^prop>\<open>r u x\<close> and \mbox{\<^prop>\<open>star r x y\<close>}
are the premises of rule @{thm[source]step}.
Assumption \<^prop>\<open>star r y z \<Longrightarrow> star r x z\<close> is \mbox{\<^prop>\<open>P x y\<close>},
the IH coming from \<^prop>\<open>star r x y\<close>. We have to prove \<^prop>\<open>P u y\<close>,
which we do by assuming \<^prop>\<open>star r y z\<close> and proving \<^prop>\<open>star r u z\<close>.
The proof itself is straightforward: from \mbox{\<^prop>\<open>star r y z\<close>} the IH
leads to \<^prop>\<open>star r x z\<close> which, together with \<^prop>\<open>r u x\<close>,
leads to \mbox{\<^prop>\<open>star r u z\<close>} via rule @{thm[source]step}:
\<close>
apply(metis step)
done

text\<open>\index{rule induction|)}

\subsection{The General Case}

Inductive definitions have approximately the following general form:
\begin{quote}
\isacom{inductive} \<open>I :: "\<tau> \<Rightarrow> bool"\<close> \isacom{where}
\end{quote}
followed by a sequence of (possibly named) rules of the form
\begin{quote}
\<open>\<lbrakk> I a\<^sub>1; \<dots>; I a\<^sub>n \<rbrakk> \<Longrightarrow> I a\<close>
\end{quote}
separated by \<open>|\<close>. As usual, \<open>n\<close> can be 0.
The corresponding rule induction principle
\<open>I.induct\<close> applies to propositions of the form
\begin{quote}
\<^prop>\<open>I x \<Longrightarrow> P x\<close>
\end{quote}
where \<open>P\<close> may itself be a chain of implications.
\begin{warn}
Rule induction is always on the leftmost premise of the goal.
Hence \<open>I x\<close> must be the first premise.
\end{warn}
Proving \<^prop>\<open>I x \<Longrightarrow> P x\<close> by rule induction means proving
for every rule of \<open>I\<close> that \<open>P\<close> is invariant:
\begin{quote}
\<open>\<lbrakk> I a\<^sub>1; P a\<^sub>1; \<dots>; I a\<^sub>n; P a\<^sub>n \<rbrakk> \<Longrightarrow> P a\<close>
\end{quote}

The above format for inductive definitions is simplified in a number of
respects. \<open>I\<close> can have any number of arguments and each rule can have
additional premises not involving \<open>I\<close>, so-called \conceptidx{side
conditions}{side condition}. In rule inductions, these side conditions appear as additional
assumptions. The \isacom{for} clause seen in the definition of the reflexive
transitive closure simplifies the induction rule.
\index{inductive definition|)}

\subsection*{Exercises}

\begin{exercise}
Formalize the following definition of palindromes
\begin{itemize}
\item The empty list and a singleton list are palindromes.
\item If \<open>xs\<close> is a palindrome, so is \<^term>\<open>a # xs @ [a]\<close>.
\end{itemize}
as an inductive predicate \<open>palindrome ::\<close> \<^typ>\<open>'a list \<Rightarrow> bool\<close>
and prove that \<^prop>\<open>rev xs = xs\<close> if \<open>xs\<close> is a palindrome.
\end{exercise}

\exercise
We could also have defined \<^const>\<open>star\<close> as follows:
\<close>

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

text\<open>
The single \<open>r\<close> step is performed after rather than before the \<open>star'\<close>
steps. Prove \<^prop>\<open>star' r x y \<Longrightarrow> star r x y\<close> and
\<^prop>\<open>star r x y \<Longrightarrow> star' r x y\<close>. You may need lemmas.
Note that rule induction fails
if the assumption about the inductive predicate is not the first assumption.
\endexercise

\begin{exercise}\label{exe:iter}
Analogous to \<^const>\<open>star\<close>, give an inductive definition of the \<open>n\<close>-fold iteration
of a relation \<open>r\<close>: \<^term>\<open>iter r n x y\<close> should hold if there are \<open>x\<^sub>0\<close>, \dots, \<open>x\<^sub>n\<close>
such that \<^prop>\<open>x = x\<^sub>0\<close>, \<^prop>\<open>x\<^sub>n = y\<close> and \<open>r x\<^bsub>i\<^esub> x\<^bsub>i+1\<^esub>\<close> for
all \<^prop>\<open>i < n\<close>. Correct and prove the following claim:
\<^prop>\<open>star r x y \<Longrightarrow> iter r n x y\<close>.
\end{exercise}

\begin{exercise}\label{exe:cfg}
A context-free grammar can be seen as an inductive definition where each
nonterminal $A$ is an inductively defined predicate on lists of terminal
symbols: $A(w)$ means that $w$ is in the language generated by $A$.
For example, the production $S \to a S b$ can be viewed as the implication
\<^prop>\<open>S w \<Longrightarrow> S (a # w @ [b])\<close> where \<open>a\<close> and \<open>b\<close> are terminal symbols,
i.e., elements of some alphabet. The alphabet can be defined like this:
\isacom{datatype} \<open>alpha = a | b | \<dots>\<close>

Define the two grammars (where $\varepsilon$ is the empty word)
\[
\begin{array}{r@ {\quad}c@ {\quad}l}
S &\to& \varepsilon \quad\mid\quad aSb \quad\mid\quad SS \\
T &\to& \varepsilon \quad\mid\quad TaTb
\end{array}
\]
as two inductive predicates.
If you think of \<open>a\<close> and \<open>b\<close> as ``\<open>(\<close>'' and  ``\<open>)\<close>'',
the grammars define balanced strings of parentheses.
Prove \<^prop>\<open>T w \<Longrightarrow> S w\<close> and \mbox{\<^prop>\<open>S w \<Longrightarrow> T w\<close>} separately and conclude
\<^prop>\<open>S w = T w\<close>.
\end{exercise}

\ifsem
\begin{exercise}
In \autoref{sec:AExp} we defined a recursive evaluation function
\<open>aval :: aexp \<Rightarrow> state \<Rightarrow> val\<close>.
Define an inductive evaluation predicate
\<open>aval_rel :: aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool\<close>
and prove that it agrees with the recursive function:
\<^prop>\<open>aval_rel a s v \<Longrightarrow> aval a s = v\<close>, 
\<^prop>\<open>aval a s = v \<Longrightarrow> aval_rel a s v\<close> and thus
\noquotes{@{prop [source] "aval_rel a s v \<longleftrightarrow> aval a s = v"}}.
\end{exercise}

\begin{exercise}
Consider the stack machine from Chapter~3
and recall the concept of \concept{stack underflow}
from Exercise~\ref{exe:stack-underflow}.
Define an inductive predicate
\<open>ok :: nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool\<close>
such that \<open>ok n is n'\<close> means that with any initial stack of length
\<open>n\<close> the instructions \<open>is\<close> can be executed
without stack underflow and that the final stack has length \<open>n'\<close>.
Prove that \<open>ok\<close> correctly computes the final stack size
@{prop[display] "\<lbrakk>ok n is n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"}
and that instruction sequences generated by \<open>comp\<close>
cannot cause stack underflow: \ \<open>ok n (comp a) ?\<close> \ for
some suitable value of \<open>?\<close>.
\end{exercise}
\fi
\<close>
(*<*)
end
(*>*)
