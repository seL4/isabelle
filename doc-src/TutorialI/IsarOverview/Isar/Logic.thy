(*<*)theory Logic = Main:(*>*)

section{*Logic \label{sec:Logic}*}

subsection{*Propositional logic*}

subsubsection{*Introduction rules*}

text{* We start with a really trivial toy proof to introduce the basic
features of structured proofs. *}
lemma "A \<longrightarrow> A"
proof (rule impI)
  assume a: "A"
  show "A" by(rule a)
qed
text{*\noindent
The operational reading: the \isakeyword{assume}-\isakeyword{show} block
proves @{prop"A \<Longrightarrow> A"},
which rule @{thm[source]impI} (@{thm impI})
turns into the desired @{prop"A \<longrightarrow> A"}.
However, this text is much too detailed for comfort. Therefore Isar
implements the following principle:
\begin{quote}\em
Command \isakeyword{proof} automatically tries to select an introduction rule
based on the goal and a predefined list of rules.
\end{quote}
Here @{thm[source]impI} is applied automatically:
*}

lemma "A \<longrightarrow> A"
proof
  assume a: "A"
  show "A" by(rule a)
qed

text{* Trivial proofs, in particular those by assumption, should be trivial
to perform. Proof ``.'' does just that (and a bit more). Thus
naming of assumptions is often superfluous: *}
lemma "A \<longrightarrow> A"
proof
  assume "A"
  show "A" .
qed

text{* To hide proofs by assumption further, \isakeyword{by}@{text"(method)"}
first applies @{text method} and then tries to solve all remaining subgoals
by assumption: *}
lemma "A \<longrightarrow> A \<and> A"
proof
  assume "A"
  show "A \<and> A" by(rule conjI)
qed
text{*\noindent Rule @{thm[source]conjI} is of course @{thm conjI}.
A drawback of these implicit proofs by assumption is that it
is no longer obvious where an assumption is used.

Proofs of the form \isakeyword{by}@{text"(rule"}~\emph{name}@{text")"} can be
abbreviated to ``..''
if \emph{name} refers to one of the predefined introduction rules:
*}

lemma "A \<longrightarrow> A \<and> A"
proof
  assume "A"
  show "A \<and> A" ..
qed
text{*\noindent
This is what happens: first the matching introduction rule @{thm[source]conjI}
is applied (first ``.''), then the two subgoals are solved by assumption
(second ``.''). *}

subsubsection{*Elimination rules*}

text{*A typical elimination rule is @{thm[source]conjE}, $\land$-elimination:
@{thm[display,indent=5]conjE}  In the following proof it is applied
by hand, after its first (\emph{major}) premise has been eliminated via
@{text"[OF AB]"}: *}
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  show "B \<and> A"
  proof (rule conjE[OF AB])  -- {*@{text"conjE[OF AB]"}: @{thm conjE[OF AB]} *}
    assume "A" "B"
    show ?thesis ..
  qed
qed
text{*\noindent Note that the term @{text"?thesis"} always stands for the
``current goal'', i.e.\ the enclosing \isakeyword{show} (or
\isakeyword{have}) statement.

This is too much proof text. Elimination rules should be selected
automatically based on their major premise, the formula or rather connective
to be eliminated. In Isar they are triggered by propositions being fed
\emph{into} a proof. Syntax:
\begin{center}
\isakeyword{from} \emph{fact} \isakeyword{show} \emph{proposition} \emph{proof}
\end{center}
where \emph{fact} stands for the name of a previously proved
proposition, e.g.\ an assumption, an intermediate result or some global
theorem, which may also be modified with @{text of}, @{text OF} etc.
The \emph{fact} is ``piped'' into the \emph{proof}, which can deal with it
how it choses. If the \emph{proof} starts with a plain \isakeyword{proof},
an elimination rule (from a predefined list) is applied
whose first premise is solved by the \emph{fact}. Thus the proof above
is equivalent to the following one: *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed

text{* Now we come a second important principle:
\begin{quote}\em
Try to arrange the sequence of propositions in a UNIX-like pipe,
such that the proof of each proposition builds on the previous proposition.
\end{quote}
The previous proposition can be referred to via the fact @{text this}.
This greatly reduces the need for explicit naming of propositions:
*}
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from this show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed

text{*\noindent Because of the frequency of \isakeyword{from}~@{text
this} Isar provides two abbreviations:
\begin{center}
\begin{tabular}{rcl}
\isakeyword{then} &=& \isakeyword{from} @{text this} \\
\isakeyword{thus} &=& \isakeyword{then} \isakeyword{show}
\end{tabular}
\end{center}
\medskip

Here is an alternative proof that operates purely by forward reasoning: *}
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume ab: "A \<and> B"
  from ab have a: "A" ..
  from ab have b: "B" ..
  from b a show "B \<and> A" ..
qed
text{*\noindent
It is worth examining this text in detail because it exhibits a number of new concepts.

For a start, this is the first time we have proved intermediate propositions
(\isakeyword{have}) on the way to the final \isakeyword{show}. This is the
norm in any nontrivial proof where one cannot bridge the gap between the
assumptions and the conclusion in one step. Both \isakeyword{have}s above are
proved automatically via @{thm[source]conjE} triggered by
\isakeyword{from}~@{text ab}.

The \isakeyword{show} command illustrates two things:
\begin{itemize}
\item \isakeyword{from} can be followed by any number of facts.
Given \isakeyword{from}~@{text f}$_1$~\dots~@{text f}$_n$, the
\isakeyword{proof} step after \isakeyword{show}
tries to find an elimination rule whose first $n$ premises can be proved
by the given facts in the given order.
\item If there is no matching elimination rule, introduction rules are tried,
again using the facts to prove the premises.
\end{itemize}
In this case, the proof succeeds with @{thm[source]conjI}. Note that the proof
would fail had we written \isakeyword{from}~@{text"a b"}
instead of \isakeyword{from}~@{text"b a"}.

This treatment of facts fed into a proof is not restricted to implicit
application of introduction and elimination rules but applies to explicit
application of rules as well. Thus you could replace the final ``..'' above
with \isakeyword{by}@{text"(rule conjI)"}. 
*}

subsection{*More constructs*}

text{* In the previous proof of @{prop"A \<and> B \<longrightarrow> B \<and> A"} we needed to feed
more than one fact into a proof step, a frequent situation. Then the
UNIX-pipe model appears to break down and we need to name the different
facts to refer to them. But this can be avoided:
*}
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume ab: "A \<and> B"
  from ab have "B" ..
  moreover
  from ab have "A" ..
  ultimately show "B \<and> A" ..
qed
text{*\noindent You can combine any number of facts @{term A1} \dots\ @{term
An} into a sequence by separating their proofs with
\isakeyword{moreover}. After the final fact, \isakeyword{ultimately} stands
for \isakeyword{from}~@{term A1}~\dots~@{term An}.  This avoids having to
introduce names for all of the sequence elements.  *}

text{* Although we have only seen a few introduction and elemination rules so
far, Isar's predefined rules include all the usual natural deduction
rules. We conclude our exposition of propositional logic with an extended
example --- which rules are used implicitly where? *}
lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
proof
  assume n: "\<not> (A \<and> B)"
  show "\<not> A \<or> \<not> B"
  proof (rule ccontr)
    assume nn: "\<not> (\<not> A \<or> \<not> B)"
    have "\<not> A"
    proof
      assume "A"
      have "\<not> B"
      proof
        assume "B"
        have "A \<and> B" ..
        with n show False ..
      qed
      hence "\<not> A \<or> \<not> B" ..
      with nn show False ..
    qed
    hence "\<not> A \<or> \<not> B" ..
    with nn show False ..
  qed
qed
text{*\noindent
Rule @{thm[source]ccontr} (``classical contradiction'') is
@{thm ccontr[no_vars]}.
Apart from demonstrating the strangeness of classical
arguments by contradiction, this example also introduces two new
abbreviations:
\begin{center}
\begin{tabular}{lcl}
\isakeyword{hence} &=& \isakeyword{then} \isakeyword{have} \\
\isakeyword{with}~\emph{facts} &=&
\isakeyword{from}~\emph{facts} @{text this}
\end{tabular}
\end{center}
*}

subsection{*Avoiding duplication*}

text{* So far our examples have been a bit unnatural: normally we want to
prove rules expressed with @{text"\<Longrightarrow>"}, not @{text"\<longrightarrow>"}. Here is an example:
*}
lemma "A \<and> B \<Longrightarrow> B \<and> A"
proof
  assume "A \<and> B" thus "B" ..
next
  assume "A \<and> B" thus "A" ..
qed
text{*\noindent The \isakeyword{proof} always works on the conclusion,
@{prop"B \<and> A"} in our case, thus selecting $\land$-introduction. Hence
we must show @{prop B} and @{prop A}; both are proved by
$\land$-elimination and the proofs are separated by \isakeyword{next}:
\begin{description}
\item[\isakeyword{next}] deals with multiple subgoals. For example,
when showing @{term"A \<and> B"} we need to show both @{term A} and @{term
B}.  Each subgoal is proved separately, in \emph{any} order. The
individual proofs are separated by \isakeyword{next}.
\end{description}

This is all very well as long as formulae are small. Let us now look at some
devices to avoid repeating (possibly large) formulae. A very general method
is pattern matching: *}

lemma "large_A \<and> large_B \<Longrightarrow> large_B \<and> large_A"
      (is "?AB \<Longrightarrow> ?B \<and> ?A")
proof
  assume "?AB" thus "?B" ..
next
  assume "?AB" thus "?A" ..
qed
text{*\noindent Any formula may be followed by
@{text"("}\isakeyword{is}~\emph{pattern}@{text")"} which causes the pattern
to be matched against the formula, instantiating the @{text"?"}-variables in
the pattern. Subsequent uses of these variables in other terms simply causes
them to be replaced by the terms they stand for.

We can simplify things even more by stating the theorem by means of the
\isakeyword{assumes} and \isakeyword{shows} elements which allow direct
naming of assumptions: *}

lemma assumes AB: "large_A \<and> large_B"
  shows "large_B \<and> large_A" (is "?B \<and> ?A")
proof
  from AB show "?B" ..
next
  from AB show "?A" ..
qed
text{*\noindent Note the difference between @{text ?AB}, a term, and
@{text AB}, a fact.

Finally we want to start the proof with $\land$-elimination so we
don't have to perform it twice, as above. Here is a slick way to
achieve this: *}

lemma assumes AB: "large_A \<and> large_B"
  shows "large_B \<and> large_A" (is "?B \<and> ?A")
using AB
proof
  assume "?A" "?B" show ?thesis ..
qed
text{*\noindent Command \isakeyword{using} can appear before a proof
and adds further facts to those piped into the proof. Here @{text AB}
is the only such fact and it triggers $\land$-elimination. Another
frequent idiom is as follows:
\begin{center}
\isakeyword{from} \emph{major facts}~
\isakeyword{show} \emph{proposition}~
\isakeyword{using} \emph{minor facts}~
\emph{proof}
\end{center}
\medskip

Sometimes it is necessary to suppress the implicit application of rules in a
\isakeyword{proof}. For example \isakeyword{show}~@{prop"A \<or> B"} would
trigger $\lor$-introduction, requiring us to prove @{prop A}. A simple
``@{text"-"}'' prevents this \emph{faux pas}: *}

lemma assumes AB: "A \<or> B" shows "B \<or> A"
proof -
  from AB show ?thesis
  proof
    assume A show ?thesis ..
  next
    assume B show ?thesis ..
  qed
qed
text{*\noindent Could \isakeyword{using} help to eliminate this ``@{text"-"}''? *}

subsection{*Predicate calculus*}

text{* Command \isakeyword{fix} introduces new local variables into a
proof. The pair \isakeyword{fix}-\isakeyword{show} corresponds to @{text"\<And>"}
(the universal quantifier at the
meta-level) just like \isakeyword{assume}-\isakeyword{show} corresponds to
@{text"\<Longrightarrow>"}. Here is a sample proof, annotated with the rules that are
applied implicitly: *}
lemma assumes P: "\<forall>x. P x" shows "\<forall>x. P(f x)"
proof                       --"@{thm[source]allI}: @{thm allI}"
  fix a
  from P show "P(f a)" ..  --"@{thm[source]allE}: @{thm allE}"
qed
text{*\noindent Note that in the proof we have chosen to call the bound
variable @{term a} instead of @{term x} merely to show that the choice of
local names is irrelevant.

Next we look at @{text"\<exists>"} which is a bit more tricky.
*}

lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
  from Pf show ?thesis
  proof              -- "@{thm[source]exE}: @{thm exE}"
    fix x
    assume "P(f x)"
    show ?thesis ..  -- "@{thm[source]exI}: @{thm exI}"
  qed
qed
text{*\noindent Explicit $\exists$-elimination as seen above can become
cumbersome in practice.  The derived Isar language element
\isakeyword{obtain} provides a more appealing form of generalized
existence reasoning: *}

lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
  from Pf obtain x where "P(f x)" ..
  thus "\<exists>y. P y" ..
qed
text{*\noindent Note how the proof text follows the usual mathematical style
of concluding $P(x)$ from $\exists x. P(x)$, while carefully introducing $x$
as a new local variable.  Technically, \isakeyword{obtain} is similar to
\isakeyword{fix} and \isakeyword{assume} together with a soundness proof of
the elimination involved.

Here is a proof of a well known tautology.
Figure out which rule is used where!  *}

lemma assumes ex: "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  from ex obtain x where "\<forall>y. P x y" ..
  hence "P x y" ..
  thus "\<exists>x. P x y" ..
qed

text{* So far we have confined ourselves to single step proofs. Of course
powerful automatic methods can be used just as well. Here is an example,
Cantor's theorem that there is no surjective function from a set to its
powerset: *}
theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume "y \<in> ?S"
      with fy show False by blast
    next
      assume "y \<notin> ?S"
      with fy show False by blast
    qed
  qed
qed
text{*\noindent
For a start, the example demonstrates two new constructs:
\begin{itemize}
\item \isakeyword{let} introduces an abbreviation for a term, in our case
the witness for the claim.
\item Proof by @{text"cases"} starts a proof by cases. Note that it remains
implicit what the two cases are: it is merely expected that the two subproofs
prove @{text"P \<Longrightarrow> ?thesis"} and @{text"\<not>P \<Longrightarrow> ?thesis"} (in that order)
for some @{term P}.
\end{itemize}
If you wonder how to \isakeyword{obtain} @{term y}:
via the predefined elimination rule @{thm rangeE[no_vars]}.

Method @{text blast} is used because the contradiction does not follow easily
by just a single rule. If you find the proof too cryptic for human
consumption, here is a more detailed version; the beginning up to
\isakeyword{obtain} stays unchanged. *}

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume "y \<in> ?S"
      hence "y \<notin> f y"   by simp
      hence "y \<notin> ?S"    by(simp add:fy)
      thus False        by contradiction
    next
      assume "y \<notin> ?S"
      hence "y \<in> f y"   by simp
      hence "y \<in> ?S"    by(simp add:fy)
      thus False        by contradiction
    qed
  qed
qed
text{*\noindent Method @{text contradiction} succeeds if both $P$ and
$\neg P$ are among the assumptions and the facts fed into that step, in any order.

As it happens, Cantor's theorem can be proved automatically by best-first
search. Depth-first search would diverge, but best-first search successfully
navigates through the large search space:
*}

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
by best
text{*\noindent Of course this only works in the context of HOL's carefully
constructed introduction and elimination rules for set theory.
*}

subsection{*Further refinements*}

text{* Thus subsection discusses some further tricks that can make
life easier although they are not essential. We start with some small
syntactic items.*}

subsubsection{*\isakeyword{and}*}

text{* Propositions (following \isakeyword{assume} etc) may but need not be
separated by \isakeyword{and}. This is not just for readability
(\isakeyword{from} \isa{A} \isakeyword{and} \isa{B} looks nicer than
\isakeyword{from} \isa{A} \isa{B}) but for structuring lists of propositions
into possibly named blocks. For example in
\begin{center}
\isakeyword{assume} \isa{A:} $A_1$ $A_2$ \isakeyword{and} \isa{B:} $A_3$
\isakeyword{and} $A_4$
\end{center}
label \isa{A} refers to the list of propositions $A_1$ $A_2$ and
label \isa{B} to $A_3$. *}

subsubsection{*\isakeyword{fixes}*}

text{* Sometimes it is necessary to decorate a proposition with type
constraints, as in Cantor's theorem above. These type constraints tend
to make the theorem less readable. The situation can be improved a
little by combining the type constraint with an outer @{text"\<And>"}: *}

theorem "\<And>f :: 'a \<Rightarrow> 'a set. \<exists>S. S \<notin> range f"
(*<*)oops(*>*)
text{*\noindent However, now @{term f} is bound and we need a
\isakeyword{fix}~\isa{f} in the proof before we can refer to @{term f}.
This is avoided by \isakeyword{fixes}: *}

theorem fixes f :: "'a \<Rightarrow> 'a set" shows "\<exists>S. S \<notin> range f"
(*<*)oops(*>*)
text{* \noindent
But the real strength of \isakeyword{fixes} lies in the possibility to
introduce concrete syntax locally:*}

lemma comm_mono:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix ">" 60) and
       f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "++" 70)
  assumes comm: "\<And>x y::'a. x ++ y = y ++ x" and
          mono: "\<And>x y z::'a. x > y \<Longrightarrow> x ++ z > y ++ z"
  shows "x > y \<Longrightarrow> z ++ x > z ++ y"
by(simp add: comm mono)

text{*\noindent The concrete syntax is dropped at the end of the proof and the
theorem becomes @{thm[display,margin=50]comm_mono} *}

subsubsection{*\isakeyword{obtain}*}

text{* The \isakeyword{obtain} construct can introduce multiple
witnesses and propositions as in the following proof fragment:*}

lemma assumes A: "\<exists>x y. P x y \<and> Q x y" shows "R"
proof -
  from A obtain x y where P: "P x y" and Q: "Q x y"  by blast
(*<*)oops(*>*)
text{* Remember also that one does not even need to start with a formula
containing @{text"\<exists>"} as we saw in the proof of Cantor's theorem.
*}

subsubsection{*Combining proof styles*}

text{* Finally, whole ``scripts'' (tactic-based proofs in the style of
\cite{LNCS2283}) may appear in the leaves of the proof tree, although this is
best avoided.  Here is a contrived example: *}

lemma "A \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> B"
proof
  assume a: "A"
  show "(A \<longrightarrow>B) \<longrightarrow> B"
    apply(rule impI)
    apply(erule impE)
    apply(rule a)
    apply assumption
    done
qed

text{*\noindent You may need to resort to this technique if an
automatic step fails to prove the desired proposition.

When converting a proof from tactic-style into Isar you can proceeed
in a top-down manner: parts of the proof can be left in script form
while to outer structure is already expressed in Isar. *}

(*<*)end(*>*)
