(*<*)theory Logic = Main:(*>*)
text{* We begin by looking at a simplified grammar for Isar proofs
where paranthesis are used for grouping and $^?$ indicates an optional item:
\begin{center}
\begin{tabular}{lrl}
\emph{proof} & ::= & \isakeyword{proof} \emph{method}$^?$
                     \emph{statement}*
                     \isakeyword{qed} \\
                 &$\mid$& \isakeyword{by} \emph{method}\\[1ex]
\emph{statement} &::= & \isakeyword{fix} \emph{variables} \\
             &$\mid$& \isakeyword{assume} \emph{proposition}
                      (\isakeyword{and} \emph{proposition})*\\
             &$\mid$& (\isakeyword{from} \emph{label}$^*$ $\mid$
                       \isakeyword{then})$^?$ 
                    (\isakeyword{show} $\mid$ \isakeyword{have})
                      \emph{string} \emph{proof} \\[1ex]
\emph{proposition} &::=& (\emph{label}{\bf:})$^?$ \emph{string}
\end{tabular}
\end{center}

This is a typical proof skeleton:
\begin{center}
\begin{tabular}{@ {}ll}
\isakeyword{proof}\\
\hspace*{3ex}\isakeyword{assume} @{text"\""}\emph{the-assm}@{text"\""}\\
\hspace*{3ex}\isakeyword{have} @{text"\""}\dots@{text"\""}  & -- intermediate result\\
\hspace*{3ex}\vdots\\
\hspace*{3ex}\isakeyword{have} @{text"\""}\dots@{text"\""}  & -- intermediate result\\
\hspace*{3ex}\isakeyword{show} @{text"\""}\emph{the-concl}@{text"\""}\\
\isakeyword{qed}
\end{tabular}
\end{center}
It proves \emph{the-assm}~@{text"\<Longrightarrow>"}~\emph{the-concl}.
Text starting with ``--'' is a comment.
*}

section{*Logic*}

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
which rule @{thm[source]impI} turns into the desired @{prop"A \<longrightarrow> A"}.
However, this text is much too detailled for comfort. Therefore Isar
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
to perform. Method ``.'' does just that (and a bit more --- see later). Thus
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
  assume A
  show "A \<and> A" by(rule conjI)
qed

text{*\noindent A drawback of these implicit proofs by assumption is that it
is no longer obvious where an assumption is used.

Proofs of the form \isakeyword{by}@{text"(rule"}~\emph{name}@{text")"} can be
abbreviated to ``..''
if \emph{name} is one of the predefined introduction rules:
*}

lemma "A \<longrightarrow> A \<and> A"
proof
  assume A
  show "A \<and> A" ..
qed

text{*\noindent
This is what happens: first the matching introduction rule @{thm[source]conjI}
is applied (first ``.''), then the two subgoals are solved by assumption
(second ``.''). *}

subsubsection{*Elimination rules*}

text{*A typical elimination rule is @{thm[source]conjE}, $\land$-elimination:
@{thm[display,indent=5]conjE[no_vars]}  In the following proof it is applied
by hand, after its first (``\emph{major}'') premise has been eliminated via
@{text"[OF AB]"}: *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  show "B \<and> A"
  proof (rule conjE[OF AB])  -- {*@{prop"(A \<Longrightarrow> B \<Longrightarrow> R) \<Longrightarrow> R"}*}
    assume A and B
    show ?thesis ..
  qed
qed

text{*\noindent Note that the term @{text"?thesis"} always stands for the
``current goal'', i.e.\ the enclosing \isakeyword{show} (or
\isakeyword{have}).

This is too much proof text. Elimination rules should be selected
automatically based on their major premise, the formula or rather connective
to be eliminated. In Isar they are triggered by propositions being fed
\emph{into} a proof block. Syntax:
\begin{center}
\isakeyword{from} \emph{fact} \isakeyword{show} \emph{proposition}
\end{center}
where \emph{fact} stands for the name of a previously proved
proposition, e.g.\ an assumption, an intermediate result or some global
theorem. The fact may also be modified with @{text of}, @{text OF} etc.
This command applies an elimination rule (from a predefined list)
whose first premise is solved by the fact. Thus: *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB show "B \<and> A"
  proof
    assume A and B
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
    assume A and B
    show ?thesis ..
  qed
qed

text{*\noindent
A final simplification: \isakeyword{from}~@{text this} can be
abbreviated to \isakeyword{thus}.
\medskip

Here is an alternative proof that operates purely by forward reasoning: *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume ab: "A \<and> B"
  from ab have a: A ..
  from ab have b: B ..
  from b a show "B \<and> A" ..
qed

text{*\noindent
It is worth examining this text in detail because it exhibits a number of new features.

For a start, this is the first time we have proved intermediate propositions
(\isakeyword{have}) on the way to the final \isakeyword{show}. This is the
norm in any nontrival proof where one cannot bridge the gap between the
assumptions and the conclusion in one step. Both \isakeyword{have}s above are
proved automatically via @{thm[source]conjE} triggered by
\isakeyword{from}~@{text ab}.

The \isakeyword{show} command illustrates two things:
\begin{itemize}
\item \isakeyword{from} can be followed by any number of facts.
Given \isakeyword{from}~@{text f}$_1$~\dots~@{text f}$_n$, \isakeyword{show}
tries to find an elimination rule whose first $n$ premises can be proved
by the given facts in the given order.
\item If there is no matching elimination rule, introduction rules are tried,
again using the facts to prove the premises.
\end{itemize}
In this case, the proof succeeds with @{thm[source]conjI}. Note that the proof
would fail if we had written \isakeyword{from}~@{text"a b"}
instead of \isakeyword{from}~@{text"b a"}.

This treatment of facts fed into a proof is not restricted to implicit
application of introduction and elimination rules but applies to explicit
application of rules as well. Thus you could replace the final ``..'' above
with \isakeyword{by}@{text"(rule conjI)"}. 

Note that Isar's predefined introduction and elimination rules include all the
usual natural deduction rules for propositional logic. We conclude this
section with an extended example --- which rules are used implicitly where?
Rule @{thm[source]ccontr} is @{thm ccontr[no_vars]}.
*}

lemma "\<not>(A \<and> B) \<longrightarrow> \<not>A \<or> \<not>B"
proof
  assume n: "\<not>(A \<and> B)"
  show "\<not>A \<or> \<not>B"
  proof (rule ccontr)
    assume nn: "\<not>(\<not>A \<or> \<not>B)"
    from n show False
    proof
      show "A \<and> B"
      proof
	show A
	proof (rule ccontr)
	  assume "\<not>A"
	  have "\<not>A \<or> \<not>B" ..
	  from nn this show False ..
	qed
      next
	show B
	proof (rule ccontr)
	  assume "\<not>B"
	  have "\<not>A \<or> \<not>B" ..
	  from nn this show False ..
	qed
      qed
    qed
  qed
qed;

text{*\noindent Apart from demonstrating the strangeness of classical
arguments by contradiction, this example also introduces a new language
feature to deal with multiple subgoals: \isakeyword{next}.  When showing
@{term"A \<and> B"} we need to show both @{term A} and @{term B}.  Each subgoal
is proved separately, in \emph{any} order. The individual proofs are
separated by \isakeyword{next}.  *}

subsection{*Avoiding duplication*}

text{* So far our examples have been a bit unnatural: normally we want to
prove rules expressed with @{text"\<Longrightarrow>"}, not @{text"\<longrightarrow>"}. Here is an example:
*}

lemma "(A \<Longrightarrow> False) \<Longrightarrow> \<not> A"
proof
  assume "A \<Longrightarrow> False" "A"
  thus False .
qed

text{*\noindent The \isakeyword{proof} always works on the conclusion,
@{prop"\<not>A"} in our case, thus selecting $\neg$-introduction. Hence we can
additionally assume @{prop"A"}. Why does ``.'' prove @{prop False}? Because
``.'' tries any of the assumptions, including proper rules (here: @{prop"A \<Longrightarrow>
False"}), such that all of its premises can be solved directly by some other
assumption (here: @{prop A}).

This is all very well as long as formulae are small. Let us now look at some
devices to avoid repeating (possibly large) formulae. A very general method
is pattern matching: *}

lemma "(large_formula \<Longrightarrow> False) \<Longrightarrow> \<not> large_formula"
      (is "(?P \<Longrightarrow> _) \<Longrightarrow> _")
proof
  assume "?P \<Longrightarrow> False" ?P
  thus False .
qed

text{*\noindent Any formula may be followed by
@{text"("}\isakeyword{is}~\emph{pattern}@{text")"} which causes the pattern
to be matched against the formula, instantiating the @{text"?"}-variables in
the pattern. Subsequent uses of these variables in other terms simply causes
them to be replaced by the terms they stand for.

We can simplify things even more by stating the theorem by means of the
\isakeyword{assumes} and \isakeyword{shows} primitives which allow direct
naming of assumptions: *}

lemma assumes A: "large_formula \<Longrightarrow> False"
  shows "\<not> large_formula" (is "\<not> ?P")
proof
  assume ?P
  with A show False .
qed

text{*\noindent Here we have used the abbreviation
\begin{center}
\isakeyword{with}~\emph{facts} \quad = \quad
\isakeyword{from}~\emph{facts} \isakeyword{and} @{text this}
\end{center}

Sometimes it is necessary to supress the implicit application of rules in a
\isakeyword{proof}. For example \isakeyword{show}~@{prop"A \<or> B"} would
trigger $\lor$-introduction, requiring us to prove @{prop A}. A simple
``@{text"-"}'' prevents this \emph{faut pas}: *}

lemma assumes AB: "A \<or> B" shows "B \<or> A"
proof -
  from AB show ?thesis
  proof
    assume A show ?thesis ..
  next
    assume B show ?thesis ..
  qed
qed

subsection{*Predicate calculus*}

text{* Command \isakeyword{fix} introduces new local variables into a
proof. It corresponds to @{text"\<And>"} (the universal quantifier at the
meta-level) just like \isakeyword{assume}-\isakeyword{show} corresponds to
@{text"\<Longrightarrow>"}. Here is a sample proof, annotated with the rules that are
applied implictly: *}

lemma assumes P: "\<forall>x. P x" shows "\<forall>x. P(f x)"
proof  -- "@{thm[source]allI}: @{thm allI[no_vars]}"
  fix a
  from P show "P(f a)" ..  --"@{thm[source]allE}: @{thm allE[no_vars]}"
qed

text{*\noindent Note that in the proof we have chosen to call the bound
variable @{term a} instead of @{term x} merely to show that the choice of
names is irrelevant.

Next we look at @{text"\<exists>"} which is a bit more tricky.
*}

lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
  from Pf show ?thesis
  proof  -- "@{thm[source]exE}: @{thm exE[no_vars]}"
    fix a
    assume "P(f a)"
    show ?thesis ..  --"@{thm[source]exI}: @{thm exI[no_vars]}"
  qed
qed

text {*\noindent
Explicit $\exists$-elimination as seen above can become
cumbersome in practice.  The derived Isar language element
\isakeyword{obtain} provides a more handsome way to perform
generalized existence reasoning:
*}

lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
  from Pf obtain a where "P(f a)" ..
  thus "\<exists>y. P y" ..
qed

text {*\noindent Note how the proof text follows the usual mathematical style
of concluding $P(x)$ from $\exists x. P(x)$, while carefully introducing $x$
as a new local variable.  Technically, \isakeyword{obtain} is similar to
\isakeyword{fix} and \isakeyword{assume} together with a soundness proof of
the elimination involved.  Thus it behaves similar to any other forward proof
element.

Here is a proof of a well known tautology which employs another useful
abbreviation: \isakeyword{hence} abbreviates \isakeyword{from}~@{text
this}~\isakeyword{have}.  Figure out which rule is used where!  *}

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
For a start, the example demonstrates two new language elements:
\begin{itemize}
\item \isakeyword{let} introduces an abbreviation for a term, in our case
the witness for the claim, because the term occurs multiple times in the proof.
\item Proof by @{text"cases"} starts a proof by cases. Note that it remains
implicit what the two cases are: it is merely expected that the two subproofs
prove @{prop"P \<Longrightarrow> Q"} and @{prop"\<not>P \<Longrightarrow> Q"} for suitable @{term P} and
@{term Q}.
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
      assume A: "y \<in> ?S"
      hence isin: "y \<in> f y"   by(simp add:fy)
      from A have "y \<notin> f y"   by simp
      with isin show False    by contradiction
    next
      assume A: "y \<notin> ?S"
      hence notin: "y \<notin> f y"   by(simp add:fy)
      from A have "y \<in> f y"    by simp
      with notin show False    by contradiction
    qed
  qed
qed

text {*\noindent Method @{text contradiction} succeeds if both $P$ and
$\neg P$ are among the assumptions and the facts fed into that step.

As it happens, Cantor's theorem can be proved automatically by best-first
search. Depth-first search would diverge, but best-first search successfully
navigates through the large search space:
*}

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
by best

text{*\noindent Of course this only works in the context of HOL's carefully
constructed introduction and elimination rules for set theory.

Finally, whole scripts may appear in the leaves of the proof tree, although
this is best avoided.  Here is a contrived example: *}

lemma "A \<longrightarrow> (A \<longrightarrow>B) \<longrightarrow> B"
proof
  assume a: A
  show "(A \<longrightarrow>B) \<longrightarrow> B"
    apply(rule impI)
    apply(erule impE)
    apply(rule a)
    apply assumption
    done
qed

text{*\noindent You may need to resort to this technique if an automatic step
fails to prove the desired proposition. *}


section{*Case distinction and induction*}


subsection{*Case distinction*}

text{* We have already met the @{text cases} method for performing
binary case splits. Here is another example: *}

lemma "P \<or> \<not> P"
proof cases
  assume "P" thus ?thesis ..
next
  assume "\<not> P" thus ?thesis ..
qed

text{*\noindent As always, the cases can be tackled in any order.

This form is appropriate if @{term P} is textually small.  However, if
@{term P} is large, we don't want to repeat it. This can be avoided by
the following idiom *}

lemma "P \<or> \<not> P"
proof (cases "P")
  case True thus ?thesis ..
next
  case False thus ?thesis ..
qed

text{*\noindent which is simply a shorthand for the previous
proof. More precisely, the phrases \isakeyword{case}~@{prop
True}/@{prop False} abbreviate the corresponding assumptions @{prop P}
and @{prop"\<not>P"}.

The same game can be played with other datatypes, for example lists:
*}
(*<*)declare length_tl[simp del](*>*)
lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis by simp
qed

text{*\noindent Here \isakeyword{case}~@{text Nil} abbreviates
\isakeyword{assume}~@{prop"x = []"} and \isakeyword{case}~@{text Cons}
abbreviates \isakeyword{assume}~@{text"xs = _ # _"}. The names of the head
and tail of @{text xs} have been chosen by the system. Therefore we cannot
refer to them (this would lead to brittle proofs) and have not even shown
them. Luckily, the proof is simple enough we do not need to refer to them.
However, in general one may have to. Hence Isar offers a simple scheme for
naming those variables: Replace the anonymous @{text Cons} by, for example,
@{text"(Cons y ys)"}, which abbreviates \isakeyword{fix}~@{text"y ys"}
\isakeyword{assume}~@{text"xs = Cons y ys"}, i.e.\ @{prop"xs = y # ys"}. Here
is a (somewhat contrived) example: *}

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case (Cons y ys)
  hence "length(tl xs) = length ys  \<and>  length xs = length ys + 1"
    by simp
  thus ?thesis by simp
qed

text{* New case distincion rules can be declared any time, even with
named cases. *}


subsection{*Induction*}


subsubsection{*Structural induction*}

text{* We start with a simple inductive proof where both cases are proved automatically: *}

lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)"
by (induct n, simp_all)

text{*\noindent If we want to expose more of the structure of the
proof, we can use pattern matching to avoid having to repeat the goal
statement: *}

lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text{* \noindent We could refine this further to show more of the equational
proof. Instead we explore the same avenue as for case distinctions:
introducing context via the \isakeyword{case} command: *}

lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc thus ?case by simp
qed

text{* \noindent The implicitly defined @{text ?case} refers to the
corresponding case to be proved, i.e.\ @{text"?P 0"} in the first case and
@{text"?P(Suc n)"} in the second case. Context \isakeyword{case}~@{text 0} is
empty whereas \isakeyword{case}~@{text Suc} assumes @{text"?P n"}. Again we
have the same problem as with case distinctions: we cannot refer to @{term n}
in the induction step because it has not been introduced via \isakeyword{fix}
(in contrast to the previous proof). The solution is the same as above:
replace @{term Suc} by @{text"(Suc i)"}: *}

lemma fixes n::nat shows "n < n*n + 1"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc i) thus "Suc i < Suc i * Suc i + 1" by simp
qed

text{* \noindent Of course we could again have written
\isakeyword{thus}~@{text ?case} instead of giving the term explicitly
but we wanted to use @{term i} somewehere.

Let us now tackle a more ambitious lemma: proving complete induction
@{prop[display,indent=5]"(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n) \<Longrightarrow> P n"}
via structural induction. It is well known that one needs to prove
something more general first: *}

lemma cind_lemma:
  assumes A: "(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  shows "\<And>m. m < n \<Longrightarrow> P(m::nat)"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n m)
  show ?case
  proof cases
    assume eq: "m = n"
    from Suc A have "P n" by blast
    with eq show "P m" by simp
  next
    assume neq: "m \<noteq> n"
    with Suc have "m < n" by simp
    with Suc show "P m" by blast
  qed
qed

text{* \noindent Let us first examine the statement of the lemma.
In contrast to the style advertized in the
Tutorial~\cite{LNCS2283}, structured Isar proofs do not need to
introduce @{text"\<forall>"} or @{text"\<longrightarrow>"} into a theorem to strengthen it
for induction --- we use @{text"\<And>"} and @{text"\<Longrightarrow>"} instead. This
simplifies the proof and means we don't have to convert between the
two kinds of connectives. As usual, at the end of the proof
@{text"\<And>"} disappears and the bound variable is turned into a
@{text"?"}-variable. Thus @{thm[source]cind_lemma} becomes
@{thm[display,indent=5] cind_lemma} Complete induction is an easy
corollary: instantiation followed by
simplification, @{thm[source] cind_lemma[of _ n "Suc n", simplified]},
yields @{thm[display,indent=5] cind_lemma[of _ n "Suc n", simplified]}

Now we examine the proof.  So what is this funny case @{text"(Suc n m)"}? It
looks confusing at first and reveals that the very suggestive @{text"(Suc
n)"} used above is not the whole truth. The variable names after the case
name (here: @{term Suc}) are the names of the parameters of that subgoal. So
far the only parameters where the arguments to the constructor, but now we
have an additonal parameter coming from the @{text"\<And>m"} in the main
\isakeyword{shows} clause. Thus  Thus @{text"(Suc n m)"} does not mean that
constructor @{term Suc} is applied to two arguments but that the two
parameters in the @{term Suc} case are to be named @{text n} and @{text
m}. *}

subsubsection{*Rule induction*}

text{* We define our own version of reflexive transitive closure of a
relation *}

consts rtc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"   ("_*" [1000] 999)
inductive "r*"
intros
refl:  "(x,x) \<in> r*"
step:  "\<lbrakk> (x,y) \<in> r; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

text{* \noindent and prove that @{term"r*"} is indeed transitive: *}

lemma assumes A: "(x,y) \<in> r*"
  shows "(y,z) \<in> r* \<Longrightarrow> (x,z) \<in> r*" (is "PROP ?P x y")
proof -
  from A show "PROP ?P x y"
  proof induct
    fix x show "PROP ?P x x" .
  next
    fix x' x y
    assume "(x',x) \<in> r" and
           "PROP ?P x y" -- "The induction hypothesis"
    thus "PROP ?P x' y" by(blast intro: rtc.step)
  qed
qed

text{*\noindent Rule induction is triggered by a fact $(x_1,\dots,x_n) \in R$
piped into the proof, here \isakeyword{from}~@{text A}. The proof itself
follows the two rules of the inductive definition very closely.  The only
surprising thing should be the keyword @{text PROP}: because of certain
syntactic subleties it is required in front of terms of type @{typ prop} (the
type of meta-level propositions) which are not obviously of type @{typ prop}
(e.g.\ @{text"?P x y"}) because they do not contain a tell-tale constant such
as @{text"\<And>"} or @{text"\<Longrightarrow>"}.

However, the proof is rather terse. Here is a more readable version:
*}

lemma assumes A: "(x,y) \<in> r*" and B: "(y,z) \<in> r*"
  shows "(x,z) \<in> r*"
proof -
  from A B show ?thesis
  proof induct
    fix x assume "(x,z) \<in> r*"  -- "B[x := z]"
    thus "(x,z) \<in> r*" .
  next
    fix x' x y
    assume step: "(x',x) \<in> r" and
           IH: "(y,z) \<in> r* \<Longrightarrow> (x,z) \<in> r*" and
           B:  "(y,z) \<in> r*"
    from step IH[OF B] show "(x',z) \<in> r*" by(rule rtc.step)
  qed
qed

text{*\noindent We start the proof with \isakeyword{from}~@{text"A
B"}. Only @{text A} is ``consumed'' by the first proof step, here
induction. Since @{text B} is left over we don't just prove @{text
?thesis} but in fact @{text"B \<Longrightarrow> ?thesis"}, just as in the previous
proof, only more elegantly. The base case is trivial. In the
assumptions for the induction step we can see very clearly how things
fit together and permit ourselves the obvious forward step
@{text"IH[OF B]"}. *}

(*<*)end(*>*)
