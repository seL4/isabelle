(*<*)
theory Isar
imports LaTeXsugar
begin
ML{* quick_and_dirty := true *}
(*>*)
text{*
Apply-scripts are unreadable and hard to maintain. The language of choice
for larger proofs is \concept{Isar}. The two key features of Isar are:
\begin{itemize}
\item It is structured, not linear.
\item It is readable without running it because
you need to state what you are proving at any given point.
\end{itemize}
Whereas apply-scripts are like assembly language programs, Isar proofs
are like structured programs with comments. A typical Isar proof looks like this:
*}text{*
\begin{tabular}{@ {}l}
\isacom{proof}\\
\quad\isacom{assume} @{text"\""}$\mathit{formula}_0$@{text"\""}\\
\quad\isacom{have} @{text"\""}$\mathit{formula}_1$@{text"\""} \quad\isacom{by} @{text simp}\\
\quad\vdots\\
\quad\isacom{have} @{text"\""}$\mathit{formula}_n$@{text"\""} \quad\isacom{by} @{text blast}\\
\quad\isacom{show} @{text"\""}$\mathit{formula}_{n+1}$@{text"\""} \quad\isacom{by} @{text \<dots>}\\
\isacom{qed}
\end{tabular}
*}text{*
It proves $\mathit{formula}_0 \Longrightarrow \mathit{formula}_{n+1}$
(provided each proof step succeeds).
The intermediate \isacom{have} statements are merely stepping stones
on the way towards the \isacom{show} statement that proves the actual
goal. In more detail, this is the Isar core syntax:
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{proof} &=& \isacom{by} \textit{method}\\
      &$\mid$& \isacom{proof} [\textit{method}] \ \textit{step}$^*$ \ \isacom{qed}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{step} &=& \isacom{fix} \textit{variables} \\
      &$\mid$& \isacom{assume} \textit{proposition} \\
      &$\mid$& [\isacom{from} \textit{fact}$^+$] (\isacom{have} $\mid$ \isacom{show}) \ \textit{proposition} \ \textit{proof}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{proposition} &=& [\textit{name}:] @{text"\""}\textit{formula}@{text"\""}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{fact} &=& \textit{name} \ $\mid$ \ \dots
\end{tabular}
\medskip

\noindent A proof can either be an atomic \isacom{by} with a single proof
method which must finish off the statement being proved, for example @{text
auto}.  Or it can be a \isacom{proof}--\isacom{qed} block of multiple
steps. Such a block can optionally begin with a proof method that indicates
how to start off the proof, e.g.\ \mbox{@{text"(induction xs)"}}.

A step either assumes a proposition or states a proposition
together with its proof. The optional \isacom{from} clause
indicates which facts are to be used in the proof.
Intermediate propositions are stated with \isacom{have}, the overall goal
with \isacom{show}. A step can also introduce new local variables with
\isacom{fix}. Logically, \isacom{fix} introduces @{text"\<And>"}-quantified
variables, \isacom{assume} introduces the assumption of an implication
(@{text"\<Longrightarrow>"}) and \isacom{have}/\isacom{show} the conclusion.

Propositions are optionally named formulas. These names can be referred to in
later \isacom{from} clauses. In the simplest case, a fact is such a name.
But facts can also be composed with @{text OF} and @{text of} as shown in
\S\ref{sec:forward-proof}---hence the \dots\ in the above grammar.  Note
that assumptions, intermediate \isacom{have} statements and global lemmas all
have the same status and are thus collectively referred to as
\concept{facts}.

Fact names can stand for whole lists of facts. For example, if @{text f} is
defined by command \isacom{fun}, @{text"f.simps"} refers to the whole list of
recursion equations defining @{text f}. Individual facts can be selected by
writing @{text"f.simps(2)"}, whole sublists by @{text"f.simps(2-4)"}.


\section{Isar by example}

We show a number of proofs of Cantor's theorem that a function from a set to
its powerset cannot be surjective, illustrating various features of Isar. The
constant @{const surj} is predefined.
*}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

text{*
The \isacom{proof} command lacks an explicit method how to perform
the proof. In such cases Isabelle tries to use some standard introduction
rule, in the above case for @{text"\<not>"}:
\[
\inferrule{
\mbox{@{thm (prem 1) notI}}}
{\mbox{@{thm (concl) notI}}}
\]
In order to prove @{prop"~ P"}, assume @{text P} and show @{text False}.
Thus we may assume @{prop"surj f"}. The proof shows that names of propositions
may be (single!) digits---meaningful names are hard to invent and are often
not necessary. Both \isacom{have} steps are obvious. The second one introduces
the diagonal set @{term"{x. x \<notin> f x}"}, the key idea in the proof.
If you wonder why @{text 2} directly implies @{text False}: from @{text 2}
it follows that @{prop"a \<notin> f a \<longleftrightarrow> a \<in> f a"}.

\subsection{@{text this}, @{text then}, @{text hence} and @{text thus}}

Labels should be avoided. They interrupt the flow of the reader who has to
scan the context for the point where the label was introduced. Ideally, the
proof is a linear flow, where the output of one step becomes the input of the
next step, piping the previously proved fact into the next proof, just like
in a UNIX pipe. In such cases the predefined name @{text this} can be used
to refer to the proposition proved in the previous step. This allows us to
eliminate all labels from our proof (we suppress the \isacom{lemma} statement):
*}
(*<*)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
(*>*)
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text{* We have also taken the opportunity to compress the two \isacom{have}
steps into one.

To compact the text further, Isar has a few convenient abbreviations:
\medskip

\begin{tabular}{rcl}
\isacom{then} &=& \isacom{from} @{text this}\\
\isacom{thus} &=& \isacom{then} \isacom{show}\\
\isacom{hence} &=& \isacom{then} \isacom{have}
\end{tabular}
\medskip

\noindent
With the help of these abbreviations the proof becomes
*}
(*<*)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
(*>*)
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed
text{*

There are two further linguistic variations:
\medskip

\begin{tabular}{rcl}
(\isacom{have}$\mid$\isacom{show}) \ \textit{prop} \ \isacom{using} \ \textit{facts}
&=&
\isacom{from} \ \textit{facts} \ (\isacom{have}$\mid$\isacom{show}) \ \textit{prop}\\
\isacom{with} \ \textit{facts} &=& \isacom{from} \ \textit{facts} \isa{this}
\end{tabular}
\medskip

\noindent The \isacom{using} idiom de-emphasizes the used facts by moving them
behind the proposition.

\subsection{Structured lemma statements: \isacom{fixes}, \isacom{assumes}, \isacom{shows}}

Lemmas can also be stated in a more structured fashion. To demonstrate this
feature with Cantor's theorem, we rephrase @{prop"\<not> surj f"}
a little:
*}

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"

txt{* The optional \isacom{fixes} part allows you to state the types of
variables up front rather than by decorating one of their occurrences in the
formula with a type constraint. The key advantage of the structured format is
the \isacom{assumes} part that allows you to name each assumption; multiple
assumptions can be separated by \isacom{and}. The
\isacom{shows} part gives the goal. The actual theorem that will come out of
the proof is @{prop"surj f \<Longrightarrow> False"}, but during the proof the assumption
@{prop"surj f"} is available under the name @{text s} like any other fact.
*}

proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def)
  thus "False" by blast
qed

text{* In the \isacom{have} step the assumption @{prop"surj f"} is now
referenced by its name @{text s}. The duplication of @{prop"surj f"} in the
above proofs (once in the statement of the lemma, once in its proof) has been
eliminated.

\begin{warn}
Note the dash after the \isacom{proof}
command.  It is the null method that does nothing to the goal. Leaving it out
would ask Isabelle to try some suitable introduction rule on the goal @{const
False}---but there is no suitable introduction rule and \isacom{proof}
would fail.
\end{warn}

Stating a lemma with \isacom{assumes}-\isacom{shows} implicitly introduces the
name @{text assms} that stands for the list of all assumptions. You can refer
to individual assumptions by @{text"assms(1)"}, @{text"assms(2)"} etc,
thus obviating the need to name them individually.

\section{Proof patterns}

We show a number of important basic proof patterns. Many of them arise from
the rules of natural deduction that are applied by \isacom{proof} by
default. The patterns are phrased in terms of \isacom{show} but work for
\isacom{have} and \isacom{lemma}, too.

We start with two forms of \concept{case analysis}:
starting from a formula @{text P} we have the two cases @{text P} and
@{prop"~P"}, and starting from a fact @{prop"P \<or> Q"}
we have the two cases @{text P} and @{text Q}:
*}text_raw{*
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "R" proof-(*>*)
show "R"
proof cases
  assume "P"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
next
  assume "\<not> P"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)
text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "R" proof-(*>*)
have "P \<or> Q" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
then show "R"
proof
  assume "P"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
next
  assume "Q"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
How to prove a logical equivalence:
\end{isamarkuptext}%
\isa{%
*}
(*<*)lemma "P\<longleftrightarrow>Q" proof-(*>*)
show "P \<longleftrightarrow> Q"
proof
  assume "P"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "Q" (*<*)sorry(*>*) txt_raw{*\ $\dots$\\*}
next
  assume "Q"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "P" (*<*)sorry(*>*) txt_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)
text_raw {* }
\medskip
\begin{isamarkuptext}%
Proofs by contradiction:
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "\<not> P" proof-(*>*)
show "\<not> P"
proof
  assume "P"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "False" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P" proof-(*>*)
show "P"
proof (rule ccontr)
  assume "\<not>P"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "False" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
The name @{thm[source] ccontr} stands for ``classical contradiction''.

How to prove quantified formulas:
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "ALL x. P x" proof-(*>*)
show "\<forall>x. P(x)"
proof
  fix x
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "P(x)" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "EX x. P(x)" proof-(*>*)
show "\<exists>x. P(x)"
proof
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "P(witness)" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed
(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
In the proof of \noquotes{@{prop[source]"\<forall>x. P(x)"}},
the step \isacom{fix}~@{text x} introduces a locally fixed variable @{text x}
into the subproof, the proverbial ``arbitrary but fixed value''.
Instead of @{text x} we could have chosen any name in the subproof.
In the proof of \noquotes{@{prop[source]"\<exists>x. P(x)"}},
@{text witness} is some arbitrary
term for which we can prove that it satisfies @{text P}.

How to reason forward from \noquotes{@{prop[source] "\<exists>x. P(x)"}}:
\end{isamarkuptext}%
*}
(*<*)lemma True proof- assume 1: "EX x. P x"(*>*)
have "\<exists>x. P(x)" (*<*)by(rule 1)(*>*)txt_raw{*\ $\dots$\\*}
then obtain x where p: "P(x)" by blast
(*<*)oops(*>*)
text{*
After the \isacom{obtain} step, @{text x} (we could have chosen any name)
is a fixed local
variable, and @{text p} is the name of the fact
\noquotes{@{prop[source] "P(x)"}}.
This pattern works for one or more @{text x}.
As an example of the \isacom{obtain} command, here is the proof of
Cantor's theorem in more detail:
*}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence  "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where  "{x. x \<notin> f x} = f a"  by blast
  hence  "a \<notin> f a \<longleftrightarrow> a \<in> f a"  by blast
  thus "False" by blast
qed

text_raw{*
\begin{isamarkuptext}%

Finally, how to prove set equality and subset relationship:
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "A = (B::'a set)" proof-(*>*)
show "A = B"
proof
  show "A \<subseteq> B" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
next
  show "B \<subseteq> A" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "A <= (B::'a set)" proof-(*>*)
show "A \<subseteq> B"
proof
  fix x
  assume "x \<in> A"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "x \<in> B" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\begin{isamarkuptext}%
\section{Streamlining proofs}

\subsection{Pattern matching and quotations}

In the proof patterns shown above, formulas are often duplicated.
This can make the text harder to read, write and maintain. Pattern matching
is an abbreviation mechanism to avoid such duplication. Writing
\begin{quote}
\isacom{show} \ \textit{formula} @{text"("}\isacom{is} \textit{pattern}@{text")"}
\end{quote}
matches the pattern against the formula, thus instantiating the unknowns in
the pattern for later use. As an example, consider the proof pattern for
@{text"\<longleftrightarrow>"}:
\end{isamarkuptext}%
*}
(*<*)lemma "formula\<^isub>1 \<longleftrightarrow> formula\<^isub>2" proof-(*>*)
show "formula\<^isub>1 \<longleftrightarrow> formula\<^isub>2" (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "?R" (*<*)sorry(*>*) txt_raw{*\ $\dots$\\*}
next
  assume "?R"
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "?L" (*<*)sorry(*>*) txt_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text{* Instead of duplicating @{text"formula\<^isub>i"} in the text, we introduce
the two abbreviations @{text"?L"} and @{text"?R"} by pattern matching.
Pattern matching works wherever a formula is stated, in particular
with \isacom{have} and \isacom{lemma}.

The unknown @{text"?thesis"} is implicitly matched against any goal stated by
\isacom{lemma} or \isacom{show}. Here is a typical example: *}

lemma "formula"
proof -
  txt_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show ?thesis (*<*)sorry(*>*) txt_raw{*\ $\dots$\\*}
qed

text{* 
Unknowns can also be instantiated with \isacom{let} commands
\begin{quote}
\isacom{let} @{text"?t"} = @{text"\""}\textit{some-big-term}@{text"\""}
\end{quote}
Later proof steps can refer to @{text"?t"}:
\begin{quote}
\isacom{have} @{text"\""}\dots @{text"?t"} \dots@{text"\""}
\end{quote}
\begin{warn}
Names of facts are introduced with @{text"name:"} and refer to proved
theorems. Unknowns @{text"?X"} refer to terms or formulas.
\end{warn}

Although abbreviations shorten the text, the reader needs to remember what
they stand for. Similarly for names of facts. Names like @{text 1}, @{text 2}
and @{text 3} are not helpful and should only be used in short proofs. For
longer proofs, descriptive names are better. But look at this example:
\begin{quote}
\isacom{have} \ @{text"x_gr_0: \"x > 0\""}\\
$\vdots$\\
\isacom{from} @{text "x_gr_0"} \dots
\end{quote}
The name is longer than the fact it stands for! Short facts do not need names,
one can refer to them easily by quoting them:
\begin{quote}
\isacom{have} \ @{text"\"x > 0\""}\\
$\vdots$\\
\isacom{from} @{text "`x>0`"} \dots
\end{quote}
Note that the quotes around @{text"x>0"} are \concept{back quotes}.
They refer to the fact not by name but by value.

\subsection{\isacom{moreover}}

Sometimes one needs a number of facts to enable some deduction. Of course
one can name these facts individually, as shown on the right,
but one can also combine them with \isacom{moreover}, as shown on the left:
*}text_raw{*
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P" proof-(*>*)
have "P\<^isub>1" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
moreover have "P\<^isub>2" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
moreover
txt_raw{*\\$\vdots$\\\hspace{-1.4ex}*}(*<*)have "True" ..(*>*)
moreover have "P\<^isub>n" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
ultimately have "P"  (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
(*<*)oops(*>*)

text_raw {* }
\end{minipage}
&
\qquad
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P" proof-(*>*)
have lab\<^isub>1: "P\<^isub>1" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
have lab\<^isub>2: "P\<^isub>2" (*<*)sorry(*>*)txt_raw{*\ $\dots$*}
txt_raw{*\\$\vdots$\\\hspace{-1.4ex}*}
have lab\<^isub>n: "P\<^isub>n" (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
from lab\<^isub>1 lab\<^isub>2 txt_raw{*\ $\dots$\\*}
have "P"  (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\begin{isamarkuptext}%
The \isacom{moreover} version is no shorter but expresses the structure more
clearly and avoids new names.

\subsection{Raw proof blocks}

Sometimes one would like to prove some lemma locally within a proof.
A lemma that shares the current context of assumptions but that
has its own assumptions and is generalized over its locally fixed
variables at the end. This is what a \concept{raw proof block} does:
\begin{quote}
@{text"{"} \isacom{fix} @{text"x\<^isub>1 \<dots> x\<^isub>n"}\\
\mbox{}\ \ \ \isacom{assume} @{text"A\<^isub>1 \<dots> A\<^isub>m"}\\
\mbox{}\ \ \ $\vdots$\\
\mbox{}\ \ \ \isacom{have} @{text"B"}\\
@{text"}"}
\end{quote}
proves @{text"\<lbrakk> A\<^isub>1; \<dots> ; A\<^isub>m \<rbrakk> \<Longrightarrow> B"}
where all @{text"x\<^isub>i"} have been replaced by unknowns @{text"?x\<^isub>i"}.
\begin{warn}
The conclusion of a raw proof block is \emph{not} indicated by \isacom{show}
but is simply the final \isacom{have}.
\end{warn}

As an example we prove a simple fact about divisibility on integers.
The definition of @{text "dvd"} is @{thm dvd_def}.
\end{isamarkuptext}%
*}

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  { fix k assume k: "a+b = b*k"
    have "\<exists>k'. a = b*k'"
    proof
      show "a = b*(k - 1)" using k by(simp add: algebra_simps)
    qed }
  then show ?thesis using assms by(auto simp add: dvd_def)
qed

text{* Note that the result of a raw proof block has no name. In this example
it was directly piped (via \isacom{then}) into the final proof, but it can
also be named for later reference: you simply follow the block directly by a
\isacom{note} command:
\begin{quote}
\isacom{note} \ @{text"name = this"}
\end{quote}
This introduces a new name @{text name} that refers to @{text this},
the fact just proved, in this case the preceding block. In general,
\isacom{note} introduces a new name for one or more facts.

\section{Case analysis and induction}

\subsection{Datatype case analysis}

We have seen case analysis on formulas. Now we want to distinguish
which form some term takes: is it @{text 0} or of the form @{term"Suc n"},
is it @{term"[]"} or of the form @{term"x#xs"}, etc. Here is a typical example
proof by case analysis on the form of @{text xs}:
*}

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

text{* Function @{text tl} (''tail'') is defined by @{thm tl.simps(1)} and
@{thm tl.simps(2)}. Note that the result type of @{const length} is @{typ nat}
and @{prop"0 - 1 = (0::nat)"}.

This proof pattern works for any term @{text t} whose type is a datatype.
The goal has to be proved for each constructor @{text C}:
\begin{quote}
\isacom{fix} \ @{text"x\<^isub>1 \<dots> x\<^isub>n"} \isacom{assume} @{text"\"t = C x\<^isub>1 \<dots> x\<^isub>n\""}
\end{quote}
Each case can be written in a more compact form by means of the \isacom{case}
command:
\begin{quote}
\isacom{case} @{text "(C x\<^isub>1 \<dots> x\<^isub>n)"}
\end{quote}
This is equivalent to the explicit \isacom{fix}-\isacom{assume} line
but also gives the assumption @{text"\"t = C x\<^isub>1 \<dots> x\<^isub>n\""} a name: @{text C},
like the constructor.
Here is the \isacom{case} version of the proof above:
*}
(*<*)lemma "length(tl xs) = length xs - 1"(*>*)
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

text{* Remember that @{text Nil} and @{text Cons} are the alphanumeric names
for @{text"[]"} and @{text"#"}. The names of the assumptions
are not used because they are directly piped (via \isacom{thus})
into the proof of the claim.

\subsection{Structural induction}

We illustrate structural induction with an example based on natural numbers:
the sum (@{text"\<Sum>"}) of the first @{text n} natural numbers
(@{text"{0..n::nat}"}) is equal to \mbox{@{term"n*(n+1) div 2::nat"}}.
Never mind the details, just focus on the pattern:
*}

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n assume "\<Sum>{0..n::nat} = n*(n+1) div 2"
  thus "\<Sum>{0..Suc n} = Suc n*(Suc n+1) div 2" by simp
qed

text{* Except for the rewrite steps, everything is explicitly given. This
makes the proof easily readable, but the duplication means it is tedious to
write and maintain. Here is how pattern
matching can completely avoid any duplication: *}

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text{* The first line introduces an abbreviation @{text"?P n"} for the goal.
Pattern matching @{text"?P n"} with the goal instantiates @{text"?P"} to the
function @{term"\<lambda>n. \<Sum>{0..n::nat} = n*(n+1) div 2"}.  Now the proposition to
be proved in the base case can be written as @{text"?P 0"}, the induction
hypothesis as @{text"?P n"}, and the conclusion of the induction step as
@{text"?P(Suc n)"}.

Induction also provides the \isacom{case} idiom that abbreviates
the \isacom{fix}-\isacom{assume} step. The above proof becomes
*}
(*<*)lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"(*>*)
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed

text{*
The unknown @{text "?case"} is set in each case to the required
claim, i.e.\ @{text"?P 0"} and \mbox{@{text"?P(Suc n)"}} in the above proof,
without requiring the user to define a @{text "?P"}. The general
pattern for induction over @{typ nat} is shown on the left-hand side:
*}text_raw{*
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P(n::nat)" proof -(*>*)
show "P(n)"
proof (induction n)
  case 0
  txt_raw{*\\\mbox{}\ \ $\vdots$\\\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*) txt_raw{*\ $\dots$\\*}
next
  case (Suc n)
  txt_raw{*\\\mbox{}\ \ $\vdots$\\\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*) txt_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
~\\
~\\
\isacom{let} @{text"?case = \"P(0)\""}\\
~\\
~\\
~\\[1ex]
\isacom{fix} @{text n} \isacom{assume} @{text"Suc: \"P(n)\""}\\
\isacom{let} @{text"?case = \"P(Suc n)\""}\\
\end{minipage}
\end{tabular}
\medskip
*}
text{*
On the right side you can see what the \isacom{case} command
on the left stands for.

In case the goal is an implication, induction does one more thing: the
proposition to be proved in each case is not the whole implication but only
its conclusion; the premises of the implication are immediately made
assumptions of that case. That is, if in the above proof we replace
\isacom{show}~@{text"P(n)"} by
\mbox{\isacom{show}~@{text"A(n) \<Longrightarrow> P(n)"}}
then \isacom{case}~@{text 0} stands for
\begin{quote}
\isacom{assume} \ @{text"0: \"A(0)\""}\\
\isacom{let} @{text"?case = \"P(0)\""}
\end{quote}
and \isacom{case}~@{text"(Suc n)"} stands for
\begin{quote}
\isacom{fix} @{text n}\\
\isacom{assume} @{text"Suc:"}
  \begin{tabular}[t]{l}@{text"\"A(n) \<Longrightarrow> P(n)\""}\\@{text"\"A(Suc n)\""}\end{tabular}\\
\isacom{let} @{text"?case = \"P(Suc n)\""}
\end{quote}
The list of assumptions @{text Suc} is actually subdivided
into @{text"Suc.IH"}, the induction hypotheses (here @{text"A(n) \<Longrightarrow> P(n)"})
and @{text"Suc.prems"}, the premises of the goal being proved
(here @{text"A(Suc n)"}).

Induction works for any datatype.
Proving a goal @{text"\<lbrakk> A\<^isub>1(x); \<dots>; A\<^isub>k(x) \<rbrakk> \<Longrightarrow> P(x)"}
by induction on @{text x} generates a proof obligation for each constructor
@{text C} of the datatype. The command @{text"case (C x\<^isub>1 \<dots> x\<^isub>n)"}
performs the following steps:
\begin{enumerate}
\item \isacom{fix} @{text"x\<^isub>1 \<dots> x\<^isub>n"}
\item \isacom{assume} the induction hypotheses (calling them @{text C.IH})
 and the premises \mbox{@{text"A\<^isub>i(C x\<^isub>1 \<dots> x\<^isub>n)"}} (calling them @{text"C.prems"})
 and calling the whole list @{text C}
\item \isacom{let} @{text"?case = \"P(C x\<^isub>1 \<dots> x\<^isub>n)\""}
\end{enumerate}

\subsection{Rule induction}

Recall the inductive and recursive definitions of even numbers in
\autoref{sec:inductive-defs}:
*}

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun even :: "nat \<Rightarrow> bool" where
"even 0 = True" |
"even (Suc 0) = False" |
"even (Suc(Suc n)) = even n"

text{* We recast the proof of @{prop"ev n \<Longrightarrow> even n"} in Isar. The
left column shows the actual proof text, the right column shows
the implicit effect of the two \isacom{case} commands:*}text_raw{*
\begin{tabular}{@ {}l@ {\qquad}l@ {}}
\begin{minipage}[t]{.5\textwidth}
\isa{%
*}

lemma "ev n \<Longrightarrow> even n"
proof(induction rule: ev.induct)
  case ev0
  show ?case by simp
next
  case evSS



  thus ?case by simp
qed

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.5\textwidth}
~\\
~\\
\isacom{let} @{text"?case = \"even 0\""}\\
~\\
~\\
\isacom{fix} @{text n}\\
\isacom{assume} @{text"evSS:"}
  \begin{tabular}[t]{l} @{text"\"ev n\""}\\@{text"\"even n\""}\end{tabular}\\
\isacom{let} @{text"?case = \"even(Suc(Suc n))\""}\\
\end{minipage}
\end{tabular}
\medskip
*}
text{*
The proof resembles structural induction, but the induction rule is given
explicitly and the names of the cases are the names of the rules in the
inductive definition.
Let us examine the two assumptions named @{thm[source]evSS}:
@{prop "ev n"} is the premise of rule @{thm[source]evSS}, which we may assume
because we are in the case where that rule was used; @{prop"even n"}
is the induction hypothesis.
\begin{warn}
Because each \isacom{case} command introduces a list of assumptions
named like the case name, which is the name of a rule of the inductive
definition, those rules now need to be accessed with a qualified name, here
@{thm[source] ev.ev0} and @{thm[source] ev.evSS}
\end{warn}

In the case @{thm[source]evSS} of the proof above we have pretended that the
system fixes a variable @{text n}.  But unless the user provides the name
@{text n}, the system will just invent its own name that cannot be referred
to.  In the above proof, we do not need to refer to it, hence we do not give
it a specific name. In case one needs to refer to it one writes
\begin{quote}
\isacom{case} @{text"(evSS m)"}
\end{quote}
just like \isacom{case}~@{text"(Suc n)"} in earlier structural inductions.
The name @{text m} is an arbitrary choice. As a result,
case @{thm[source] evSS} is derived from a renamed version of
rule @{thm[source] evSS}: @{text"ev m \<Longrightarrow> ev(Suc(Suc m))"}.
Here is an example with a (contrived) intermediate step that refers to @{text m}:
*}

lemma "ev n \<Longrightarrow> even n"
proof(induction rule: ev.induct)
  case ev0 show ?case by simp
next
  case (evSS m)
  have "even(Suc(Suc m)) = even m" by simp
  thus ?case using `even m` by blast
qed

text{*
\indent
In general, let @{text I} be a (for simplicity unary) inductively defined
predicate and let the rules in the definition of @{text I}
be called @{text "rule\<^isub>1"}, \dots, @{text "rule\<^isub>n"}. A proof by rule
induction follows this pattern:
*}

(*<*)
inductive I where rule\<^isub>1: "I()" |  rule\<^isub>2: "I()" |  rule\<^isub>n: "I()"
lemma "I x \<Longrightarrow> P x" proof-(*>*)
show "I x \<Longrightarrow> P x"
proof(induction rule: I.induct)
  case rule\<^isub>1
  txt_raw{*\\[-.4ex]\mbox{}\ \ $\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
next
  txt_raw{*\\[-.4ex]$\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}*}
(*<*)
  case rule\<^isub>2
  show ?case sorry
(*>*)
next
  case rule\<^isub>n
  txt_raw{*\\[-.4ex]\mbox{}\ \ $\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*)txt_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text{*
One can provide explicit variable names by writing
\isacom{case}~@{text"(rule\<^isub>i x\<^isub>1 \<dots> x\<^isub>k)"}, thus renaming the first @{text k}
free variables in rule @{text i} to @{text"x\<^isub>1 \<dots> x\<^isub>k"},
going through rule @{text i} from left to right.

\subsection{Assumption naming}

In any induction, \isacom{case}~@{text name} sets up a list of assumptions
also called @{text name}, which is subdivided into three parts:
\begin{description}
\item[@{text name.IH}] contains the induction hypotheses.
\item[@{text name.hyps}] contains all the other hypotheses of this case in the
induction rule. For rule inductions these are the hypotheses of rule
@{text name}, for structural inductions these are empty.
\item[@{text name.prems}] contains the (suitably instantiated) premises
of the statement being proved, i.e. the @{text A\<^isub>i} when
proving @{text"\<lbrakk> A\<^isub>1; \<dots>; A\<^isub>n \<rbrakk> \<Longrightarrow> A"}.
\end{description}
\begin{warn}
Proof method @{text induct} differs from @{text induction}
only in this naming policy: @{text induct} does not distinguish
@{text IH} from @{text hyps} but subsumes @{text IH} under @{text hyps}.
\end{warn}

More complicated inductive proofs than the ones we have seen so far
often need to refer to specific assumptions---just @{text name} or even
@{text name.prems} and @{text name.IH} can be too unspecific.
This is where the indexing of fact lists comes in handy, e.g.\
@{text"name.IH(2)"} or @{text"name.prems(1-2)"}.

\subsection{Rule inversion}

Rule inversion is case analysis of which rule could have been used to
derive some fact. The name \concept{rule inversion} emphasizes that we are
reasoning backwards: by which rules could some given fact have been proved?
For the inductive definition of @{const ev}, rule inversion can be summarized
like this:
@{prop[display]"ev n \<Longrightarrow> n = 0 \<or> (EX k. n = Suc(Suc k) \<and> ev k)"}
The realisation in Isabelle is a case analysis.
A simple example is the proof that @{prop"ev n \<Longrightarrow> ev (n - 2)"}. We
already went through the details informally in \autoref{sec:Logic:even}. This
is the Isar proof:
*}
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

text{* The key point here is that a case analysis over some inductively
defined predicate is triggered by piping the given fact
(here: \isacom{from}~@{text this}) into a proof by @{text cases}.
Let us examine the assumptions available in each case. In case @{text ev0}
we have @{text"n = 0"} and in case @{text evSS} we have @{prop"n = Suc(Suc k)"}
and @{prop"ev k"}. In each case the assumptions are available under the name
of the case; there is no fine grained naming schema like for induction.

Sometimes some rules could not have been used to derive the given fact
because constructors clash. As an extreme example consider
rule inversion applied to @{prop"ev(Suc 0)"}: neither rule @{text ev0} nor
rule @{text evSS} can yield @{prop"ev(Suc 0)"} because @{text"Suc 0"} unifies
neither with @{text 0} nor with @{term"Suc(Suc n)"}. Impossible cases do not
have to be proved. Hence we can prove anything from @{prop"ev(Suc 0)"}:
*}
(*<*)
notepad begin fix P
(*>*)
  assume "ev(Suc 0)" then have P by cases
(*<*)
end
(*>*)

text{* That is, @{prop"ev(Suc 0)"} is simply not provable: *}

lemma "\<not> ev(Suc 0)"
proof
  assume "ev(Suc 0)" then show False by cases
qed

text{* Normally not all cases will be impossible. As a simple exercise,
prove that \mbox{@{prop"\<not> ev(Suc(Suc(Suc 0)))"}.}
*}

(*
lemma "\<not> ev(Suc(Suc(Suc 0)))"
proof
  assume "ev(Suc(Suc(Suc 0)))"
  then show False
  proof cases
    case evSS
    from `ev(Suc 0)` show False by cases
  qed
qed
*)

(*<*)
end
(*>*)
