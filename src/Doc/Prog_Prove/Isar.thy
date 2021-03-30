(*<*)
theory Isar
imports LaTeXsugar
begin
declare [[quick_and_dirty]]
(*>*)
text\<open>
Apply-scripts are unreadable and hard to maintain. The language of choice
for larger proofs is \concept{Isar}. The two key features of Isar are:
\begin{itemize}
\item It is structured, not linear.
\item It is readable without its being run because
you need to state what you are proving at any given point.
\end{itemize}
Whereas apply-scripts are like assembly language programs, Isar proofs
are like structured programs with comments. A typical Isar proof looks like this:
\<close>text\<open>
\begin{tabular}{@ {}l}
\isacom{proof}\\
\quad\isacom{assume} \<open>"\<close>$\mathit{formula}_0$\<open>"\<close>\\
\quad\isacom{have} \<open>"\<close>$\mathit{formula}_1$\<open>"\<close> \quad\isacom{by} \<open>simp\<close>\\
\quad\vdots\\
\quad\isacom{have} \<open>"\<close>$\mathit{formula}_n$\<open>"\<close> \quad\isacom{by} \<open>blast\<close>\\
\quad\isacom{show} \<open>"\<close>$\mathit{formula}_{n+1}$\<open>"\<close> \quad\isacom{by} \<open>\<dots>\<close>\\
\isacom{qed}
\end{tabular}
\<close>text\<open>
It proves $\mathit{formula}_0 \Longrightarrow \mathit{formula}_{n+1}$
(provided each proof step succeeds).
The intermediate \isacom{have} statements are merely stepping stones
on the way towards the \isacom{show} statement that proves the actual
goal. In more detail, this is the Isar core syntax:
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{proof} &=& \indexed{\isacom{by}}{by} \textit{method}\\
      &$\mid$& \indexed{\isacom{proof}}{proof} [\textit{method}] \ \textit{step}$^*$ \ \indexed{\isacom{qed}}{qed}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{step} &=& \indexed{\isacom{fix}}{fix} \textit{variables} \\
      &$\mid$& \indexed{\isacom{assume}}{assume} \textit{proposition} \\
      &$\mid$& [\indexed{\isacom{from}}{from} \textit{fact}$^+$] (\indexed{\isacom{have}}{have} $\mid$ \indexed{\isacom{show}}{show}) \ \textit{proposition} \ \textit{proof}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{proposition} &=& [\textit{name}:] \<open>"\<close>\textit{formula}\<open>"\<close>
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{fact} &=& \textit{name} \ $\mid$ \ \dots
\end{tabular}
\medskip

\noindent A proof can either be an atomic \isacom{by} with a single proof
method which must finish off the statement being proved, for example \<open>auto\<close>,  or it can be a \isacom{proof}--\isacom{qed} block of multiple
steps. Such a block can optionally begin with a proof method that indicates
how to start off the proof, e.g., \mbox{\<open>(induction xs)\<close>}.

A step either assumes a proposition or states a proposition
together with its proof. The optional \isacom{from} clause
indicates which facts are to be used in the proof.
Intermediate propositions are stated with \isacom{have}, the overall goal
is stated with \isacom{show}. A step can also introduce new local variables with
\isacom{fix}. Logically, \isacom{fix} introduces \<open>\<And>\<close>-quantified
variables, \isacom{assume} introduces the assumption of an implication
(\<open>\<Longrightarrow>\<close>) and \isacom{have}/\isacom{show} introduce the conclusion.

Propositions are optionally named formulas. These names can be referred to in
later \isacom{from} clauses. In the simplest case, a fact is such a name.
But facts can also be composed with \<open>OF\<close> and \<open>of\<close> as shown in
\autoref{sec:forward-proof} --- hence the \dots\ in the above grammar.  Note
that assumptions, intermediate \isacom{have} statements and global lemmas all
have the same status and are thus collectively referred to as
\conceptidx{facts}{fact}.

Fact names can stand for whole lists of facts. For example, if \<open>f\<close> is
defined by command \isacom{fun}, \<open>f.simps\<close> refers to the whole list of
recursion equations defining \<open>f\<close>. Individual facts can be selected by
writing \<open>f.simps(2)\<close>, whole sublists by writing \<open>f.simps(2-4)\<close>.


\section{Isar by Example}

We show a number of proofs of Cantor's theorem that a function from a set to
its powerset cannot be surjective, illustrating various features of Isar. The
constant \<^const>\<open>surj\<close> is predefined.
\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

text\<open>
The \isacom{proof} command lacks an explicit method by which to perform
the proof. In such cases Isabelle tries to use some standard introduction
rule, in the above case for \<open>\<not>\<close>:
\[
\inferrule{
\mbox{@{thm (prem 1) notI}}}
{\mbox{@{thm (concl) notI}}}
\]
In order to prove \<^prop>\<open>~ P\<close>, assume \<open>P\<close> and show \<open>False\<close>.
Thus we may assume \mbox{\noquotes{@{prop [source] "surj f"}}}. The proof shows that names of propositions
may be (single!) digits --- meaningful names are hard to invent and are often
not necessary. Both \isacom{have} steps are obvious. The second one introduces
the diagonal set \<^term>\<open>{x. x \<notin> f x}\<close>, the key idea in the proof.
If you wonder why \<open>2\<close> directly implies \<open>False\<close>: from \<open>2\<close>
it follows that \<^prop>\<open>a \<notin> f a \<longleftrightarrow> a \<in> f a\<close>.

\subsection{\indexed{\<open>this\<close>}{this}, \indexed{\isacom{then}}{then}, \indexed{\isacom{hence}}{hence} and \indexed{\isacom{thus}}{thus}}

Labels should be avoided. They interrupt the flow of the reader who has to
scan the context for the point where the label was introduced. Ideally, the
proof is a linear flow, where the output of one step becomes the input of the
next step, piping the previously proved fact into the next proof, like
in a UNIX pipe. In such cases the predefined name \<open>this\<close> can be used
to refer to the proposition proved in the previous step. This allows us to
eliminate all labels from our proof (we suppress the \isacom{lemma} statement):
\<close>
(*<*)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
(*>*)
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text\<open>We have also taken the opportunity to compress the two \isacom{have}
steps into one.

To compact the text further, Isar has a few convenient abbreviations:
\medskip

\begin{tabular}{r@ {\quad=\quad}l}
\isacom{then} & \isacom{from} \<open>this\<close>\\
\isacom{thus} & \isacom{then} \isacom{show}\\
\isacom{hence} & \isacom{then} \isacom{have}
\end{tabular}
\medskip

\noindent
With the help of these abbreviations the proof becomes
\<close>
(*<*)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
(*>*)
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed
text\<open>

There are two further linguistic variations:
\medskip

\begin{tabular}{r@ {\quad=\quad}l}
(\isacom{have}$\mid$\isacom{show}) \ \textit{prop} \ \indexed{\isacom{using}}{using} \ \textit{facts}
&
\isacom{from} \ \textit{facts} \ (\isacom{have}$\mid$\isacom{show}) \ \textit{prop}\\
\indexed{\isacom{with}}{with} \ \textit{facts} & \isacom{from} \ \textit{facts} \isa{this}
\end{tabular}
\medskip

\noindent The \isacom{using} idiom de-emphasizes the used facts by moving them
behind the proposition.

\subsection{Structured Lemma Statements: \indexed{\isacom{fixes}}{fixes}, \indexed{\isacom{assumes}}{assumes}, \indexed{\isacom{shows}}{shows}}
\index{lemma@\isacom{lemma}}
Lemmas can also be stated in a more structured fashion. To demonstrate this
feature with Cantor's theorem, we rephrase \noquotes{@{prop[source]"\<not> surj f"}}
a little:
\<close>

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"

txt\<open>The optional \isacom{fixes} part allows you to state the types of
variables up front rather than by decorating one of their occurrences in the
formula with a type constraint. The key advantage of the structured format is
the \isacom{assumes} part that allows you to name each assumption; multiple
assumptions can be separated by \isacom{and}. The
\isacom{shows} part gives the goal. The actual theorem that will come out of
the proof is \noquotes{@{prop[source]"surj f \<Longrightarrow> False"}}, but during the proof the assumption
\noquotes{@{prop[source]"surj f"}} is available under the name \<open>s\<close> like any other fact.
\<close>

proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def)
  thus "False" by blast
qed

text\<open>
\begin{warn}
Note the hyphen after the \isacom{proof} command.
It is the null method that does nothing to the goal. Leaving it out would be asking
Isabelle to try some suitable introduction rule on the goal \<^const>\<open>False\<close> --- but
there is no such rule and \isacom{proof} would fail.
\end{warn}
In the \isacom{have} step the assumption \noquotes{@{prop[source]"surj f"}} is now
referenced by its name \<open>s\<close>. The duplication of \noquotes{@{prop[source]"surj f"}} in the
above proofs (once in the statement of the lemma, once in its proof) has been
eliminated.

Stating a lemma with \isacom{assumes}-\isacom{shows} implicitly introduces the
name \indexed{\<open>assms\<close>}{assms} that stands for the list of all assumptions. You can refer
to individual assumptions by \<open>assms(1)\<close>, \<open>assms(2)\<close>, etc.,
thus obviating the need to name them individually.

\section{Proof Patterns}

We show a number of important basic proof patterns. Many of them arise from
the rules of natural deduction that are applied by \isacom{proof} by
default. The patterns are phrased in terms of \isacom{show} but work for
\isacom{have} and \isacom{lemma}, too.

\ifsem\else
\subsection{Logic}
\fi

We start with two forms of \concept{case analysis}:
starting from a formula \<open>P\<close> we have the two cases \<open>P\<close> and
\<^prop>\<open>~P\<close>, and starting from a fact \<^prop>\<open>P \<or> Q\<close>
we have the two cases \<open>P\<close> and \<open>Q\<close>:
\<close>text_raw\<open>
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "R" proof-(*>*)
show "R"
proof cases
  assume "P"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "R" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
next
  assume "\<not> P"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "R" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)oops(*>*)
text_raw \<open>}
\end{minipage}\index{cases@\<open>cases\<close>}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "R" proof-(*>*)
have "P \<or> Q" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
then show "R"
proof
  assume "P"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "R" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
next
  assume "Q"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "R" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)oops(*>*)

text_raw \<open>}
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
How to prove a logical equivalence:
\end{isamarkuptext}%
\isa{%
\<close>
(*<*)lemma "P\<longleftrightarrow>Q" proof-(*>*)
show "P \<longleftrightarrow> Q"
proof
  assume "P"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "Q" (*<*)sorry(*>*) text_raw\<open>\ \isasymproof\\\<close>
next
  assume "Q"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "P" (*<*)sorry(*>*) text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)qed(*>*)
text_raw \<open>}
\medskip
\begin{isamarkuptext}%
Proofs by contradiction (@{thm[source] ccontr} stands for ``classical contradiction''):
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "\<not> P" proof-(*>*)
show "\<not> P"
proof
  assume "P"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "False" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)oops(*>*)

text_raw \<open>}
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "P" proof-(*>*)
show "P"
proof (rule ccontr)
  assume "\<not>P"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "False" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)oops(*>*)

text_raw \<open>}
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
How to prove quantified formulas:
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "\<forall>x. P x" proof-(*>*)
show "\<forall>x. P(x)"
proof
  fix x
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "P(x)" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)oops(*>*)

text_raw \<open>}
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "\<exists>x. P(x)" proof-(*>*)
show "\<exists>x. P(x)"
proof
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "P(witness)" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed
(*<*)oops(*>*)

text_raw \<open>}
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
In the proof of \noquotes{@{prop[source]"\<forall>x. P(x)"}},
the step \indexed{\isacom{fix}}{fix}~\<open>x\<close> introduces a locally fixed variable \<open>x\<close>
into the subproof, the proverbial ``arbitrary but fixed value''.
Instead of \<open>x\<close> we could have chosen any name in the subproof.
In the proof of \noquotes{@{prop[source]"\<exists>x. P(x)"}},
\<open>witness\<close> is some arbitrary
term for which we can prove that it satisfies \<open>P\<close>.

How to reason forward from \noquotes{@{prop[source] "\<exists>x. P(x)"}}:
\end{isamarkuptext}%
\<close>
(*<*)lemma True proof- assume 1: "\<exists>x. P x"(*>*)
have "\<exists>x. P(x)" (*<*)by(rule 1)(*>*)text_raw\<open>\ \isasymproof\\\<close>
then obtain x where p: "P(x)" by blast
(*<*)oops(*>*)
text\<open>
After the \indexed{\isacom{obtain}}{obtain} step, \<open>x\<close> (we could have chosen any name)
is a fixed local
variable, and \<open>p\<close> is the name of the fact
\noquotes{@{prop[source] "P(x)"}}.
This pattern works for one or more \<open>x\<close>.
As an example of the \isacom{obtain} command, here is the proof of
Cantor's theorem in more detail:
\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence  "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where  "{x. x \<notin> f x} = f a"  by blast
  hence  "a \<notin> f a \<longleftrightarrow> a \<in> f a"  by blast
  thus "False" by blast
qed

text_raw\<open>
\begin{isamarkuptext}%

Finally, how to prove set equality and subset relationship:
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "A = (B::'a set)" proof-(*>*)
show "A = B"
proof
  show "A \<subseteq> B" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
next
  show "B \<subseteq> A" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)qed(*>*)

text_raw \<open>}
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "A <= (B::'a set)" proof-(*>*)
show "A \<subseteq> B"
proof
  fix x
  assume "x \<in> A"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "x \<in> B" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)qed(*>*)

text_raw \<open>}
\end{minipage}
\end{tabular}
\begin{isamarkuptext}%

\ifsem\else
\subsection{Chains of (In)Equations}

In textbooks, chains of equations (and inequations) are often displayed like this:
\begin{quote}
\begin{tabular}{@ {}l@ {\qquad}l@ {}}
$t_1 = t_2$ & \isamath{\,\langle\mathit{justification}\rangle}\\
$\phantom{t_1} = t_3$ & \isamath{\,\langle\mathit{justification}\rangle}\\
\quad $\vdots$\\
$\phantom{t_1} = t_n$ & \isamath{\,\langle\mathit{justification}\rangle}
\end{tabular}
\end{quote}
The Isar equivalent is this:

\begin{samepage}
\begin{quote}
\isacom{have} \<open>"t\<^sub>1 = t\<^sub>2"\<close> \isasymproof\\
\isacom{also have} \<open>"... = t\<^sub>3"\<close> \isasymproof\\
\quad $\vdots$\\
\isacom{also have} \<open>"... = t\<^sub>n"\<close> \isasymproof \\
\isacom{finally show} \<open>"t\<^sub>1 = t\<^sub>n"\<close>\ \texttt{.}
\end{quote}
\end{samepage}

\noindent
The ``\<open>...\<close>'' and ``\<open>.\<close>'' deserve some explanation:
\begin{description}
\item[``\<open>...\<close>''] is literally three dots. It is the name of an unknown that Isar
automatically instantiates with the right-hand side of the previous equation.
In general, if \<open>this\<close> is the theorem \<^term>\<open>p t\<^sub>1 t\<^sub>2\<close> then ``\<open>...\<close>''
stands for \<open>t\<^sub>2\<close>.
\item[``\<open>.\<close>''] (a single dot) is a proof method that solves a goal by one of the
assumptions. This works here because the result of \isacom{finally}
is the theorem \mbox{\<open>t\<^sub>1 = t\<^sub>n\<close>},
\isacom{show} \<open>"t\<^sub>1 = t\<^sub>n"\<close> states the theorem explicitly,
and ``\<open>.\<close>'' proves the theorem with the result of \isacom{finally}.
\end{description}
The above proof template also works for arbitrary mixtures of \<open>=\<close>, \<open>\<le>\<close> and \<open><\<close>,
for example:
\begin{quote}
\isacom{have} \<open>"t\<^sub>1 < t\<^sub>2"\<close> \isasymproof\\
\isacom{also have} \<open>"... = t\<^sub>3"\<close> \isasymproof\\
\quad $\vdots$\\
\isacom{also have} \<open>"... \<le> t\<^sub>n"\<close> \isasymproof \\
\isacom{finally show} \<open>"t\<^sub>1 < t\<^sub>n"\<close>\ \texttt{.}
\end{quote}
The relation symbol in the \isacom{finally} step needs to be the most precise one
possible. In the example above, you must not write \<open>t\<^sub>1 \<le> t\<^sub>n\<close> instead of \mbox{\<open>t\<^sub>1 < t\<^sub>n\<close>}.

\begin{warn}
Isabelle only supports \<open>=\<close>, \<open>\<le>\<close> and \<open><\<close> but not \<open>\<ge>\<close> and \<open>>\<close>
in (in)equation chains (by default).
\end{warn}

If you want to go beyond merely using the above proof patterns and want to
understand what \isacom{also} and \isacom{finally} mean, read on.
There is an Isar theorem variable called \<open>calculation\<close>, similar to \<open>this\<close>.
When the first \isacom{also} in a chain is encountered, Isabelle sets
\<open>calculation := this\<close>. In each subsequent \isacom{also} step,
Isabelle composes the theorems \<open>calculation\<close> and \<open>this\<close> (i.e.\ the two previous
(in)equalities) using some predefined set of rules including transitivity
of \<open>=\<close>, \<open>\<le>\<close> and \<open><\<close> but also mixed rules like \<^prop>\<open>\<lbrakk> x \<le> y; y < z \<rbrakk> \<Longrightarrow> x < z\<close>.
The result of this composition is assigned to \<open>calculation\<close>. Consider
\begin{quote}
\isacom{have} \<open>"t\<^sub>1 \<le> t\<^sub>2"\<close> \isasymproof\\
\isacom{also} \isacom{have} \<open>"... < t\<^sub>3"\<close> \isasymproof\\
\isacom{also} \isacom{have} \<open>"... = t\<^sub>4"\<close> \isasymproof\\
\isacom{finally show} \<open>"t\<^sub>1 < t\<^sub>4"\<close>\ \texttt{.}
\end{quote}
After the first \isacom{also}, \<open>calculation\<close> is \<open>"t\<^sub>1 \<le> t\<^sub>2"\<close>,
and after the second \isacom{also}, \<open>calculation\<close> is \<open>"t\<^sub>1 < t\<^sub>3"\<close>.
The command \isacom{finally} is short for \isacom{also from} \<open>calculation\<close>.
Therefore the \isacom{also} hidden in \isacom{finally} sets \<open>calculation\<close>
to \<open>t\<^sub>1 < t\<^sub>4\<close> and the final ``\texttt{.}'' succeeds.

For more information on this style of proof see @{cite "BauerW-TPHOLs01"}.
\fi

\section{Streamlining Proofs}

\subsection{Pattern Matching and Quotations}

In the proof patterns shown above, formulas are often duplicated.
This can make the text harder to read, write and maintain. Pattern matching
is an abbreviation mechanism to avoid such duplication. Writing
\begin{quote}
\isacom{show} \ \textit{formula} \<open>(\<close>\indexed{\isacom{is}}{is} \textit{pattern}\<open>)\<close>
\end{quote}
matches the pattern against the formula, thus instantiating the unknowns in
the pattern for later use. As an example, consider the proof pattern for
\<open>\<longleftrightarrow>\<close>:
\end{isamarkuptext}%
\<close>
(*<*)lemma "formula\<^sub>1 \<longleftrightarrow> formula\<^sub>2" proof-(*>*)
show "formula\<^sub>1 \<longleftrightarrow> formula\<^sub>2" (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "?R" (*<*)sorry(*>*) text_raw\<open>\ \isasymproof\\\<close>
next
  assume "?R"
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show "?L" (*<*)sorry(*>*) text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)qed(*>*)

text\<open>Instead of duplicating \<open>formula\<^sub>i\<close> in the text, we introduce
the two abbreviations \<open>?L\<close> and \<open>?R\<close> by pattern matching.
Pattern matching works wherever a formula is stated, in particular
with \isacom{have} and \isacom{lemma}.

The unknown \indexed{\<open>?thesis\<close>}{thesis} is implicitly matched against any goal stated by
\isacom{lemma} or \isacom{show}. Here is a typical example:\<close>

lemma "formula"
proof -
  text_raw\<open>\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}\<close>
  show ?thesis (*<*)sorry(*>*) text_raw\<open>\ \isasymproof\\\<close>
qed

text\<open>
Unknowns can also be instantiated with \indexed{\isacom{let}}{let} commands
\begin{quote}
\isacom{let} \<open>?t\<close> = \<open>"\<close>\textit{some-big-term}\<open>"\<close>
\end{quote}
Later proof steps can refer to \<open>?t\<close>:
\begin{quote}
\isacom{have} \<open>"\<close>\dots \<open>?t\<close> \dots\<open>"\<close>
\end{quote}
\begin{warn}
Names of facts are introduced with \<open>name:\<close> and refer to proved
theorems. Unknowns \<open>?X\<close> refer to terms or formulas.
\end{warn}

Although abbreviations shorten the text, the reader needs to remember what
they stand for. Similarly for names of facts. Names like \<open>1\<close>, \<open>2\<close>
and \<open>3\<close> are not helpful and should only be used in short proofs. For
longer proofs, descriptive names are better. But look at this example:
\begin{quote}
\isacom{have} \ \<open>x_gr_0: "x > 0"\<close>\\
$\vdots$\\
\isacom{from} \<open>x_gr_0\<close> \dots
\end{quote}
The name is longer than the fact it stands for! Short facts do not need names;
one can refer to them easily by quoting them:
\begin{quote}
\isacom{have} \ \<open>"x > 0"\<close>\\
$\vdots$\\
\isacom{from} \<open>`x>0`\<close> \dots\index{$IMP053@\<open>`...`\<close>}
\end{quote}
Note that the quotes around \<open>x>0\<close> are \conceptnoidx{back quotes}.
They refer to the fact not by name but by value.

\subsection{\indexed{\isacom{moreover}}{moreover}}
\index{ultimately@\isacom{ultimately}}

Sometimes one needs a number of facts to enable some deduction. Of course
one can name these facts individually, as shown on the right,
but one can also combine them with \isacom{moreover}, as shown on the left:
\<close>text_raw\<open>
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "P" proof-(*>*)
have "P\<^sub>1" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
moreover have "P\<^sub>2" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
moreover
text_raw\<open>\\$\vdots$\\\hspace{-1.4ex}\<close>(*<*)have "True" ..(*>*)
moreover have "P\<^sub>n" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
ultimately have "P"  (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
(*<*)oops(*>*)

text_raw \<open>}
\end{minipage}
&
\qquad
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "P" proof-(*>*)
have lab\<^sub>1: "P\<^sub>1" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
have lab\<^sub>2: "P\<^sub>2" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\<close>
text_raw\<open>\\$\vdots$\\\hspace{-1.4ex}\<close>
have lab\<^sub>n: "P\<^sub>n" (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
from lab\<^sub>1 lab\<^sub>2 text_raw\<open>\ $\dots$\\\<close>
have "P"  (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
(*<*)oops(*>*)

text_raw \<open>}
\end{minipage}
\end{tabular}
\begin{isamarkuptext}%
The \isacom{moreover} version is no shorter but expresses the structure
a bit more clearly and avoids new names.

\subsection{Local Lemmas}

Sometimes one would like to prove some lemma locally within a proof,
a lemma that shares the current context of assumptions but that
has its own assumptions and is generalized over its locally fixed
variables at the end. This is simply an extension of the basic
\indexed{\isacom{have}}{have} construct:
\begin{quote}
\indexed{\isacom{have}}{have} \<open>B\<close>\
 \indexed{\isacom{if}}{if} \<open>name:\<close> \<open>A\<^sub>1 \<dots> A\<^sub>m\<close>\
 \indexed{\isacom{for}}{for} \<open>x\<^sub>1 \<dots> x\<^sub>n\<close>\\
\isasymproof
\end{quote}
proves \<open>\<lbrakk> A\<^sub>1; \<dots> ; A\<^sub>m \<rbrakk> \<Longrightarrow> B\<close>
where all \<open>x\<^sub>i\<close> have been replaced by unknowns \<open>?x\<^sub>i\<close>.
As an example we prove a simple fact about divisibility on integers.
The definition of \<open>dvd\<close> is @{thm dvd_def}.
\end{isamarkuptext}%
\<close>

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  have "\<exists>k'. a = b*k'" if asm: "a+b = b*k" for k
  proof
    show "a = b*(k - 1)" using asm by(simp add: algebra_simps)
  qed
  then show ?thesis using assms by(auto simp add: dvd_def)
qed

text\<open>

\subsection*{Exercises}

\exercise
Give a readable, structured proof of the following lemma:
\<close>
lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
(*<*)oops(*>*)
text\<open>
\endexercise

\exercise
Give a readable, structured proof of the following lemma:
\<close>
lemma "\<exists>ys zs. xs = ys @ zs \<and>
            (length ys = length zs \<or> length ys = length zs + 1)"
(*<*)oops(*>*)
text\<open>
Hint: There are predefined functions @{const_typ take} and @{const_typ drop}
such that \<open>take k [x\<^sub>1,\<dots>] = [x\<^sub>1,\<dots>,x\<^sub>k]\<close> and
\<open>drop k [x\<^sub>1,\<dots>] = [x\<^bsub>k+1\<^esub>,\<dots>]\<close>. Let sledgehammer find and apply
the relevant \<^const>\<open>take\<close> and \<^const>\<open>drop\<close> lemmas for you.
\endexercise


\section{Case Analysis and Induction}

\subsection{Datatype Case Analysis}
\index{case analysis|(}

We have seen case analysis on formulas. Now we want to distinguish
which form some term takes: is it \<open>0\<close> or of the form \<^term>\<open>Suc n\<close>,
is it \<^term>\<open>[]\<close> or of the form \<^term>\<open>x#xs\<close>, etc. Here is a typical example
proof by case analysis on the form of \<open>xs\<close>:
\<close>

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

text\<open>\index{cases@\<open>cases\<close>|(}Function \<open>tl\<close> (''tail'') is defined by @{thm list.sel(2)} and
@{thm list.sel(3)}. Note that the result type of \<^const>\<open>length\<close> is \<^typ>\<open>nat\<close>
and \<^prop>\<open>0 - 1 = (0::nat)\<close>.

This proof pattern works for any term \<open>t\<close> whose type is a datatype.
The goal has to be proved for each constructor \<open>C\<close>:
\begin{quote}
\isacom{fix} \ \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> \isacom{assume} \<open>"t = C x\<^sub>1 \<dots> x\<^sub>n"\<close>
\end{quote}\index{case@\isacom{case}|(}
Each case can be written in a more compact form by means of the \isacom{case}
command:
\begin{quote}
\isacom{case} \<open>(C x\<^sub>1 \<dots> x\<^sub>n)\<close>
\end{quote}
This is equivalent to the explicit \isacom{fix}-\isacom{assume} line
but also gives the assumption \<open>"t = C x\<^sub>1 \<dots> x\<^sub>n"\<close> a name: \<open>C\<close>,
like the constructor.
Here is the \isacom{case} version of the proof above:
\<close>
(*<*)lemma "length(tl xs) = length xs - 1"(*>*)
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

text\<open>Remember that \<open>Nil\<close> and \<open>Cons\<close> are the alphanumeric names
for \<open>[]\<close> and \<open>#\<close>. The names of the assumptions
are not used because they are directly piped (via \isacom{thus})
into the proof of the claim.
\index{case analysis|)}

\subsection{Structural Induction}
\index{induction|(}
\index{structural induction|(}

We illustrate structural induction with an example based on natural numbers:
the sum (\<open>\<Sum>\<close>) of the first \<open>n\<close> natural numbers
(\<open>{0..n::nat}\<close>) is equal to \mbox{\<^term>\<open>n*(n+1) div 2::nat\<close>}.
Never mind the details, just focus on the pattern:
\<close>

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n assume "\<Sum>{0..n::nat} = n*(n+1) div 2"
  thus "\<Sum>{0..Suc n} = Suc n*(Suc n+1) div 2" by simp
qed

text\<open>Except for the rewrite steps, everything is explicitly given. This
makes the proof easily readable, but the duplication means it is tedious to
write and maintain. Here is how pattern
matching can completely avoid any duplication:\<close>

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text\<open>The first line introduces an abbreviation \<open>?P n\<close> for the goal.
Pattern matching \<open>?P n\<close> with the goal instantiates \<open>?P\<close> to the
function \<^term>\<open>\<lambda>n. \<Sum>{0..n::nat} = n*(n+1) div 2\<close>.  Now the proposition to
be proved in the base case can be written as \<open>?P 0\<close>, the induction
hypothesis as \<open>?P n\<close>, and the conclusion of the induction step as
\<open>?P(Suc n)\<close>.

Induction also provides the \isacom{case} idiom that abbreviates
the \isacom{fix}-\isacom{assume} step. The above proof becomes
\<close>
(*<*)lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"(*>*)
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed

text\<open>
The unknown \<open>?case\<close>\index{case?@\<open>?case\<close>|(} is set in each case to the required
claim, i.e., \<open>?P 0\<close> and \mbox{\<open>?P(Suc n)\<close>} in the above proof,
without requiring the user to define a \<open>?P\<close>. The general
pattern for induction over \<^typ>\<open>nat\<close> is shown on the left-hand side:
\<close>text_raw\<open>
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
\<close>
(*<*)lemma "P(n::nat)" proof -(*>*)
show "P(n)"
proof (induction n)
  case 0
  text_raw\<open>\\\mbox{}\ \ $\vdots$\\\mbox{}\hspace{-1ex}\<close>
  show ?case (*<*)sorry(*>*) text_raw\<open>\ \isasymproof\\\<close>
next
  case (Suc n)
  text_raw\<open>\\\mbox{}\ \ $\vdots$\\\mbox{}\hspace{-1ex}\<close>
  show ?case (*<*)sorry(*>*) text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)qed(*>*)

text_raw \<open>}
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
~\\
~\\
\isacom{let} \<open>?case = "P(0)"\<close>\\
~\\
~\\
~\\[1ex]
\isacom{fix} \<open>n\<close> \isacom{assume} \<open>Suc: "P(n)"\<close>\\
\isacom{let} \<open>?case = "P(Suc n)"\<close>\\
\end{minipage}
\end{tabular}
\medskip
\<close>
text\<open>
On the right side you can see what the \isacom{case} command
on the left stands for.

In case the goal is an implication, induction does one more thing: the
proposition to be proved in each case is not the whole implication but only
its conclusion; the premises of the implication are immediately made
assumptions of that case. That is, if in the above proof we replace
\isacom{show}~\<open>"P(n)"\<close> by
\mbox{\isacom{show}~\<open>"A(n) \<Longrightarrow> P(n)"\<close>}
then \isacom{case}~\<open>0\<close> stands for
\begin{quote}
\isacom{assume} \ \<open>0: "A(0)"\<close>\\
\isacom{let} \<open>?case = "P(0)"\<close>
\end{quote}
and \isacom{case}~\<open>(Suc n)\<close> stands for
\begin{quote}
\isacom{fix} \<open>n\<close>\\
\isacom{assume} \<open>Suc:\<close>
  \begin{tabular}[t]{l}\<open>"A(n) \<Longrightarrow> P(n)"\<close>\\\<open>"A(Suc n)"\<close>\end{tabular}\\
\isacom{let} \<open>?case = "P(Suc n)"\<close>
\end{quote}
The list of assumptions \<open>Suc\<close> is actually subdivided
into \<open>Suc.IH\<close>, the induction hypotheses (here \<open>A(n) \<Longrightarrow> P(n)\<close>),
and \<open>Suc.prems\<close>, the premises of the goal being proved
(here \<open>A(Suc n)\<close>).

Induction works for any datatype.
Proving a goal \<open>\<lbrakk> A\<^sub>1(x); \<dots>; A\<^sub>k(x) \<rbrakk> \<Longrightarrow> P(x)\<close>
by induction on \<open>x\<close> generates a proof obligation for each constructor
\<open>C\<close> of the datatype. The command \isacom{case}~\<open>(C x\<^sub>1 \<dots> x\<^sub>n)\<close>
performs the following steps:
\begin{enumerate}
\item \isacom{fix} \<open>x\<^sub>1 \<dots> x\<^sub>n\<close>
\item \isacom{assume} the induction hypotheses (calling them \<open>C.IH\<close>\index{IH@\<open>.IH\<close>})
 and the premises \mbox{\<open>A\<^sub>i(C x\<^sub>1 \<dots> x\<^sub>n)\<close>} (calling them \<open>C.prems\<close>\index{prems@\<open>.prems\<close>})
 and calling the whole list \<open>C\<close>
\item \isacom{let} \<open>?case = "P(C x\<^sub>1 \<dots> x\<^sub>n)"\<close>
\end{enumerate}
\index{structural induction|)}


\ifsem\else
\subsection{Computation Induction}
\index{rule induction}

In \autoref{sec:recursive-funs} we introduced computation induction and
its realization in Isabelle: the definition
of a recursive function \<open>f\<close> via \isacom{fun} proves the corresponding computation
induction rule called \<open>f.induct\<close>. Induction with this rule looks like in
\autoref{sec:recursive-funs}, but now with \isacom{proof} instead of \isacom{apply}:
\begin{quote}
\isacom{proof} (\<open>induction x\<^sub>1 \<dots> x\<^sub>k rule: f.induct\<close>)
\end{quote}
Just as for structural induction, this creates several cases, one for each
defining equation for \<open>f\<close>. By default (if the equations have not been named
by the user), the cases are numbered. That is, they are started by
\begin{quote}
\isacom{case} (\<open>i x y ...\<close>)
\end{quote}
where \<open>i = 1,...,n\<close>, \<open>n\<close> is the number of equations defining \<open>f\<close>,
and \<open>x y ...\<close> are the variables in equation \<open>i\<close>. Note the following:
\begin{itemize}
\item
Although \<open>i\<close> is an Isar name, \<open>i.IH\<close> (or similar) is not. You need
double quotes: "\<open>i.IH\<close>". When indexing the name, write "\<open>i.IH\<close>"(1),
not "\<open>i.IH\<close>(1)".
\item
If defining equations for \<open>f\<close> overlap, \isacom{fun} instantiates them to make
them nonoverlapping. This means that one user-provided equation may lead to
several equations and thus to several cases in the induction rule.
These have names of the form "\<open>i_j\<close>", where \<open>i\<close> is the number of the original
equation and the system-generated \<open>j\<close> indicates the subcase.
\end{itemize}
In Isabelle/jEdit, the \<open>induction\<close> proof method displays a proof skeleton
with all \isacom{case}s. This is particularly useful for computation induction
and the following rule induction.
\fi


\subsection{Rule Induction}
\index{rule induction|(}

Recall the inductive and recursive definitions of even numbers in
\autoref{sec:inductive-defs}:
\<close>

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text\<open>We recast the proof of \<^prop>\<open>ev n \<Longrightarrow> evn n\<close> in Isar. The
left column shows the actual proof text, the right column shows
the implicit effect of the two \isacom{case} commands:\<close>text_raw\<open>
\begin{tabular}{@ {}l@ {\qquad}l@ {}}
\begin{minipage}[t]{.5\textwidth}
\isa{%
\<close>

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0
  show ?case by simp
next
  case evSS



  thus ?case by simp
qed

text_raw \<open>}
\end{minipage}
&
\begin{minipage}[t]{.5\textwidth}
~\\
~\\
\isacom{let} \<open>?case = "evn 0"\<close>\\
~\\
~\\
\isacom{fix} \<open>n\<close>\\
\isacom{assume} \<open>evSS:\<close>
  \begin{tabular}[t]{l} \<open>"ev n"\<close>\\\<open>"evn n"\<close>\end{tabular}\\
\isacom{let} \<open>?case = "evn(Suc(Suc n))"\<close>\\
\end{minipage}
\end{tabular}
\medskip
\<close>
text\<open>
The proof resembles structural induction, but the induction rule is given
explicitly and the names of the cases are the names of the rules in the
inductive definition.
Let us examine the two assumptions named @{thm[source]evSS}:
\<^prop>\<open>ev n\<close> is the premise of rule @{thm[source]evSS}, which we may assume
because we are in the case where that rule was used; \<^prop>\<open>evn n\<close>
is the induction hypothesis.
\begin{warn}
Because each \isacom{case} command introduces a list of assumptions
named like the case name, which is the name of a rule of the inductive
definition, those rules now need to be accessed with a qualified name, here
@{thm[source] ev.ev0} and @{thm[source] ev.evSS}.
\end{warn}

In the case @{thm[source]evSS} of the proof above we have pretended that the
system fixes a variable \<open>n\<close>.  But unless the user provides the name
\<open>n\<close>, the system will just invent its own name that cannot be referred
to.  In the above proof, we do not need to refer to it, hence we do not give
it a specific name. In case one needs to refer to it one writes
\begin{quote}
\isacom{case} \<open>(evSS m)\<close>
\end{quote}
like \isacom{case}~\<open>(Suc n)\<close> in earlier structural inductions.
The name \<open>m\<close> is an arbitrary choice. As a result,
case @{thm[source] evSS} is derived from a renamed version of
rule @{thm[source] evSS}: \<open>ev m \<Longrightarrow> ev(Suc(Suc m))\<close>.
Here is an example with a (contrived) intermediate step that refers to \<open>m\<close>:
\<close>

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0 show ?case by simp
next
  case (evSS m)
  have "evn(Suc(Suc m)) = evn m" by simp
  thus ?case using `evn m` by blast
qed

text\<open>
\indent
In general, let \<open>I\<close> be a (for simplicity unary) inductively defined
predicate and let the rules in the definition of \<open>I\<close>
be called \<open>rule\<^sub>1\<close>, \dots, \<open>rule\<^sub>n\<close>. A proof by rule
induction follows this pattern:\index{inductionrule@\<open>induction ... rule:\<close>}
\<close>

(*<*)
inductive I where rule\<^sub>1: "I()" |  rule\<^sub>2: "I()" |  rule\<^sub>n: "I()"
lemma "I x \<Longrightarrow> P x" proof-(*>*)
show "I x \<Longrightarrow> P x"
proof(induction rule: I.induct)
  case rule\<^sub>1
  text_raw\<open>\\[-.4ex]\mbox{}\ \ $\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}\<close>
  show ?case (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
next
  text_raw\<open>\\[-.4ex]$\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}\<close>
(*<*)
  case rule\<^sub>2
  show ?case sorry
(*>*)
next
  case rule\<^sub>n
  text_raw\<open>\\[-.4ex]\mbox{}\ \ $\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}\<close>
  show ?case (*<*)sorry(*>*)text_raw\<open>\ \isasymproof\\\<close>
qed(*<*)qed(*>*)

text\<open>
One can provide explicit variable names by writing
\isacom{case}~\<open>(rule\<^sub>i x\<^sub>1 \<dots> x\<^sub>k)\<close>, thus renaming the first \<open>k\<close>
free variables in rule \<open>i\<close> to \<open>x\<^sub>1 \<dots> x\<^sub>k\<close>,
going through rule \<open>i\<close> from left to right.

\subsection{Assumption Naming}
\label{sec:assm-naming}

In any induction, \isacom{case}~\<open>name\<close> sets up a list of assumptions
also called \<open>name\<close>, which is subdivided into three parts:
\begin{description}
\item[\<open>name.IH\<close>]\index{IH@\<open>.IH\<close>} contains the induction hypotheses.
\item[\<open>name.hyps\<close>]\index{hyps@\<open>.hyps\<close>} contains all the other hypotheses of this case in the
induction rule. For rule inductions these are the hypotheses of rule
\<open>name\<close>, for structural inductions these are empty.
\item[\<open>name.prems\<close>]\index{prems@\<open>.prems\<close>} contains the (suitably instantiated) premises
of the statement being proved, i.e., the \<open>A\<^sub>i\<close> when
proving \<open>\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A\<close>.
\end{description}
\begin{warn}
Proof method \<open>induct\<close> differs from \<open>induction\<close>
only in this naming policy: \<open>induct\<close> does not distinguish
\<open>IH\<close> from \<open>hyps\<close> but subsumes \<open>IH\<close> under \<open>hyps\<close>.
\end{warn}

More complicated inductive proofs than the ones we have seen so far
often need to refer to specific assumptions --- just \<open>name\<close> or even
\<open>name.prems\<close> and \<open>name.IH\<close> can be too unspecific.
This is where the indexing of fact lists comes in handy, e.g.,
\<open>name.IH(2)\<close> or \<open>name.prems(1-2)\<close>.

\subsection{Rule Inversion}
\label{sec:rule-inversion}
\index{rule inversion|(}

Rule inversion is case analysis of which rule could have been used to
derive some fact. The name \conceptnoidx{rule inversion} emphasizes that we are
reasoning backwards: by which rules could some given fact have been proved?
For the inductive definition of \<^const>\<open>ev\<close>, rule inversion can be summarized
like this:
@{prop[display]"ev n \<Longrightarrow> n = 0 \<or> (\<exists>k. n = Suc(Suc k) \<and> ev k)"}
The realisation in Isabelle is a case analysis.
A simple example is the proof that \<^prop>\<open>ev n \<Longrightarrow> ev (n - 2)\<close>. We
already went through the details informally in \autoref{sec:Logic:even}. This
is the Isar proof:
\<close>
(*<*)
notepad
begin fix n
(*>*)
  assume "ev n"
  from this have "ev(n - 2)"
  proof cases
    case ev0 thus "ev(n - 2)" by (simp add: ev.ev0)
  next
    case (evSS k) thus "ev(n - 2)" by (simp add: ev.evSS)
  qed
(*<*)
end
(*>*)

text\<open>The key point here is that a case analysis over some inductively
defined predicate is triggered by piping the given fact
(here: \isacom{from}~\<open>this\<close>) into a proof by \<open>cases\<close>.
Let us examine the assumptions available in each case. In case \<open>ev0\<close>
we have \<open>n = 0\<close> and in case \<open>evSS\<close> we have \<^prop>\<open>n = Suc(Suc k)\<close>
and \<^prop>\<open>ev k\<close>. In each case the assumptions are available under the name
of the case; there is no fine-grained naming schema like there is for induction.

Sometimes some rules could not have been used to derive the given fact
because constructors clash. As an extreme example consider
rule inversion applied to \<^prop>\<open>ev(Suc 0)\<close>: neither rule \<open>ev0\<close> nor
rule \<open>evSS\<close> can yield \<^prop>\<open>ev(Suc 0)\<close> because \<open>Suc 0\<close> unifies
neither with \<open>0\<close> nor with \<^term>\<open>Suc(Suc n)\<close>. Impossible cases do not
have to be proved. Hence we can prove anything from \<^prop>\<open>ev(Suc 0)\<close>:
\<close>
(*<*)
notepad begin fix P
(*>*)
  assume "ev(Suc 0)" then have P by cases
(*<*)
end
(*>*)

text\<open>That is, \<^prop>\<open>ev(Suc 0)\<close> is simply not provable:\<close>

lemma "\<not> ev(Suc 0)"
proof
  assume "ev(Suc 0)" then show False by cases
qed

text\<open>Normally not all cases will be impossible. As a simple exercise,
prove that \mbox{\<^prop>\<open>\<not> ev(Suc(Suc(Suc 0)))\<close>.}

\subsection{Advanced Rule Induction}
\label{sec:advanced-rule-induction}

So far, rule induction was always applied to goals of the form \<open>I x y z \<Longrightarrow> \<dots>\<close>
where \<open>I\<close> is some inductively defined predicate and \<open>x\<close>, \<open>y\<close>, \<open>z\<close>
are variables. In some rare situations one needs to deal with an assumption where
not all arguments \<open>r\<close>, \<open>s\<close>, \<open>t\<close> are variables:
\begin{isabelle}
\isacom{lemma} \<open>"I r s t \<Longrightarrow> \<dots>"\<close>
\end{isabelle}
Applying the standard form of
rule induction in such a situation will lead to strange and typically unprovable goals.
We can easily reduce this situation to the standard one by introducing
new variables \<open>x\<close>, \<open>y\<close>, \<open>z\<close> and reformulating the goal like this:
\begin{isabelle}
\isacom{lemma} \<open>"I x y z \<Longrightarrow> x = r \<Longrightarrow> y = s \<Longrightarrow> z = t \<Longrightarrow> \<dots>"\<close>
\end{isabelle}
Standard rule induction will work fine now, provided the free variables in
\<open>r\<close>, \<open>s\<close>, \<open>t\<close> are generalized via \<open>arbitrary\<close>.

However, induction can do the above transformation for us, behind the curtains, so we never
need to see the expanded version of the lemma. This is what we need to write:
\begin{isabelle}
\isacom{lemma} \<open>"I r s t \<Longrightarrow> \<dots>"\<close>\isanewline
\isacom{proof}\<open>(induction "r" "s" "t" arbitrary: \<dots> rule: I.induct)\<close>\index{inductionrule@\<open>induction ... rule:\<close>}\index{arbitrary@\<open>arbitrary:\<close>}
\end{isabelle}
Like for rule inversion, cases that are impossible because of constructor clashes
will not show up at all. Here is a concrete example:\<close>

lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof(induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev (Suc n)"
  proof \<comment> \<open>contradiction\<close>
    assume "ev(Suc n)"
    thus False
    proof cases \<comment> \<open>rule inversion\<close>
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

text\<open>
Remarks:
\begin{itemize}
\item 
Instead of the \isacom{case} and \<open>?case\<close> magic we have spelled all formulas out.
This is merely for greater clarity.
\item
We only need to deal with one case because the @{thm[source] ev0} case is impossible.
\item
The form of the \<open>IH\<close> shows us that internally the lemma was expanded as explained
above: \noquotes{@{prop[source]"ev x \<Longrightarrow> x = Suc m \<Longrightarrow> \<not> ev m"}}.
\item
The goal \<^prop>\<open>\<not> ev (Suc n)\<close> may surprise. The expanded version of the lemma
would suggest that we have a \isacom{fix} \<open>m\<close> \isacom{assume} \<^prop>\<open>Suc(Suc n) = Suc m\<close>
and need to show \<^prop>\<open>\<not> ev m\<close>. What happened is that Isabelle immediately
simplified \<^prop>\<open>Suc(Suc n) = Suc m\<close> to \<^prop>\<open>Suc n = m\<close> and could then eliminate
\<open>m\<close>. Beware of such nice surprises with this advanced form of induction.
\end{itemize}
\begin{warn}
This advanced form of induction does not support the \<open>IH\<close>
naming schema explained in \autoref{sec:assm-naming}:
the induction hypotheses are instead found under the name \<open>hyps\<close>,
as they are for the simpler
\<open>induct\<close> method.
\end{warn}
\index{induction|)}
\index{cases@\<open>cases\<close>|)}
\index{case@\isacom{case}|)}
\index{case?@\<open>?case\<close>|)}
\index{rule induction|)}
\index{rule inversion|)}

\subsection*{Exercises}


\exercise
Give a structured proof by rule inversion:
\<close>

lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
(*<*)oops(*>*)

text\<open>
\endexercise

\begin{exercise}
Give a structured proof of \<^prop>\<open>\<not> ev(Suc(Suc(Suc 0)))\<close>
by rule inversions. If there are no cases to be proved you can close
a proof immediately with \isacom{qed}.
\end{exercise}

\begin{exercise}
Recall predicate \<open>star\<close> from \autoref{sec:star} and \<open>iter\<close>
from Exercise~\ref{exe:iter}. Prove \<^prop>\<open>iter r n x y \<Longrightarrow> star r x y\<close>
in a structured style; do not just sledgehammer each case of the
required induction.
\end{exercise}

\begin{exercise}
Define a recursive function \<open>elems ::\<close> \<^typ>\<open>'a list \<Rightarrow> 'a set\<close>
and prove \<^prop>\<open>x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys\<close>.
\end{exercise}

\begin{exercise}
Extend Exercise~\ref{exe:cfg} with a function that checks if some
\mbox{\<open>alpha list\<close>} is a balanced
string of parentheses. More precisely, define a \mbox{recursive} function
\<open>balanced :: nat \<Rightarrow> alpha list \<Rightarrow> bool\<close> such that \<^term>\<open>balanced n w\<close>
is true iff (informally) \<open>S (a\<^sup>n @ w)\<close>. Formally, prove that
\<^prop>\<open>balanced n w \<longleftrightarrow> S (replicate n a @ w)\<close> where
\<^const>\<open>replicate\<close> \<open>::\<close> \<^typ>\<open>nat \<Rightarrow> 'a \<Rightarrow> 'a list\<close> is predefined
and \<^term>\<open>replicate n x\<close> yields the list \<open>[x, \<dots>, x]\<close> of length \<open>n\<close>.
\end{exercise}
\<close>

(*<*)
end
(*>*)
