(*<*)theory Logic = Main:(*>*)

text{*
We begin by looking at a simplified grammar for Isar proofs:
\begin{center}
\begin{tabular}{lrl}
\emph{proof} & ::= & \isacommand{proof} \emph{method}$^?$
                     \emph{statement}*
                     \isacommand{qed} \\
                 &$\mid$& \isacommand{by} \emph{method}\\[1ex]
\emph{statement} &::= & \isacommand{fix} \emph{variables} \\
             &$\mid$& \isacommand{assume} proposition* \\
             &$\mid$& (\isacommand{from} \emph{label}$^*$ $\mid$
                       \isacommand{then})$^?$ \\
                   && (\isacommand{show} $\mid$ \isacommand{have})
                      \emph{proposition} \emph{proof} \\[1ex]
\emph{proposition} &::=& (\emph{label}{\bf:})$^?$ \emph{string}
\end{tabular}
\end{center}
where paranthesis are used for grouping and $^?$ indicates an optional item.

This is a typical proof skeleton:

\begin{center}
\begin{tabular}{@ {}ll}
\isacommand{proof}\\
\hspace*{3ex}\isacommand{assume} "\emph{the-assm}"\\
\hspace*{3ex}\isacommand{have} "\dots"  & -- "intermediate result"\\
\hspace*{3ex}\vdots\\
\hspace*{3ex}\isacommand{have} "\dots"  & -- "intermediate result"\\
\hspace*{3ex}\isacommand{show} "\emph{the-concl}"\\
\isacommand{qed}
\end{tabular}
\end{center}
It proves \emph{the-assm}~@{text"\<Longrightarrow>"}~\emph{the-concl}.
*}

section{*Logic*}

subsection{*Propositional logic*}

subsubsection{*Introduction rules*}

lemma "A \<longrightarrow> A"
proof (rule impI)
  assume A: "A"
  show "A" by(rule A)
qed

text{*\noindent
The operational reading: the assume-show block proves @{prop"A \<Longrightarrow> A"},
which rule @{thm[source]impI} turns into the desired @{prop"A \<longrightarrow> A"}.
However, this text is much too detailled for comfort. Therefore Isar
implements the following principle:
\begin{quote}\em
Command \isacommand{proof} automatically tries select an introduction rule
based on the goal and a predefined list of rules.
\end{quote}
Here @{thm[source]impI} is applied automatically:
*}

lemma "A \<longrightarrow> A"
proof
  assume A: "A"
  show "A" by(rule A)
qed

text{* Trivial proofs, in particular those by assumption, should be trivial
to perform. Method "." does just that (and a bit more --- see later). Thus
naming of assumptions is often superfluous: *}

lemma "A \<longrightarrow> A"
proof
  assume "A"
  have "A" .
qed

text{* To hide proofs by assumption further, \isacommand{by}@{text"(method)"}
first applies @{text method} and then tries to solve all remaining subgoals
by assumption: *}

lemma "A \<longrightarrow> A & A"
proof
  assume A
  show "A & A" by(rule conjI)
qed

text{*\noindent A drawback of these implicit proofs by assumption is that it
is no longer obvious where an assumption is used.

Proofs of the form \isacommand{by}@{text"(rule <name>)"} can be abbreviated
to ".." if @{text"<name>"} is one of the predefined introduction rules.  Thus
*}

lemma "A \<longrightarrow> A \<and> A"
proof
  assume A
  show "A \<and> A" ..
qed

text{*\noindent
What happens: first the matching introduction rule @{thm[source]conjI}
is applied (first "."), then the two subgoals are solved by assumption
(second "."). *}

subsubsection{*Elimination rules*}

text{*A typical elimination rule is @{thm[source]conjE}, $\land$-elimination:
@{thm[display,indent=5]conjE[no_vars]}  In the following proof it is applied
by hand, after its first (``\emph{major}'') premise has been eliminated via
@{text"[OF AB]"}: *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  show "B \<and> A"
  proof (rule conjE[OF AB])
    assume A and B
    show ?thesis ..
  qed
qed

text{*\noindent Note that the term @{text"?thesis"} always stands for the
``current goal'', i.e.\ the enclosing \isacommand{show} (or
\isacommand{have}).

This is too much proof text. Elimination rules should be selected
automatically based on their major premise, the formula or rather connective
to be eliminated. In Isar they are triggered by propositions being fed
\emph{into} a proof block. Syntax:
\begin{center}
\isacommand{from} \emph{fact} \isacommand{show} \emph{proposition}
\end{center}
where \emph{fact} stands for the name of a previously proved proved
proposition, e.g.\ an assumption, an intermediate result or some global
theorem. The fact may also be modified with @{text of}, @{text OF} etc.
This command applies a elimination rule (from a predefined list)
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
A final simplification: \isacommand{from}~@{text this} can be
abbreviated to \isacommand{thus}.
\bigskip

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
(\isacommand{have}) on the way to the final \isacommand{show}. This is the
norm in any nontrival proof where one cannot bridge the gap between the
assumptions and the conclusion in one step. Both \isacommand{have}s above are
proved automatically via @{thm[source]conjE} triggered by
\isacommand{from}~@{text ab}.

The \isacommand{show} command illustrates two things:
\begin{itemize}
\item \isacommand{from} can be followed by any number of facts.
Given \isacommand{from}~@{text f}$_1$~\dots~@{text f}$_n$, \isacommand{show}
tries to find an elimination rule whose first $n$ premises can be proved
by the given facts in the given order.
\item If there is no matching elimination rule, introduction rules are tried,
again using the facts to prove the premises.
\end{itemize}
In this case, the proof succeeds with @{thm[source]conjI}. Note that the proof would fail if we had written \isacommand{from}~@{text"a b"}
instead of \isacommand{from}~@{text"b a"}.

This treatment of facts fed into a proof is not restricted to implicit
application of introduction and elimination rules but applies to explicit
application of rules as well. Thus you could replace the final ``..'' above
with \isacommand{by}@{text"(rule conjI)"}. 

Note Isar's predefined introduction and elimination rules include all the
usual natural deduction rules for propositional logic. We conclude this
section with an extended example --- which rules are used implicitly where?
Rule @{thm[source]ccontr} is @{thm ccontr[no_vars]}.
*}

lemma "\<not>(A \<and> B) \<longrightarrow> \<not>A \<or> \<not>B"
proof
  assume n: "\<not>(A \<and> B)"
  show "\<not>A \<or> \<not>B"
  proof (rule ccontr)
    assume nn: "\<not>(\<not> A \<or> \<not>B)"
    from n show False
    proof
      show "A \<and> B"
      proof
	show A
	proof (rule ccontr)
	  assume "\<not>A"
	  have "\<not> A \<or> \<not> B" ..
	  from nn this show False ..
	qed
      next
	show B
	proof (rule ccontr)
	  assume "\<not>B"
	  have "\<not> A \<or> \<not> B" ..
	  from nn this show False ..
	qed
      qed
    qed
  qed
qed;

text{*\noindent Apart from demonstrating the strangeness of classical
arguments by contradiction, this example also introduces a new language
feature to deal with multiple subgoals: \isacommand{next}.  When showing
@{term"A \<and> B"} we need to show both @{term A} and @{term B}.  Each subgoal
is proved separately, in \emph{any} order. The individual proofs are
separated by \isacommand{next}.  *}

subsection{*Becoming more concise*}

text{* So far our examples have been a bit unnatural: normally we want to
prove rules expressed with @{text"\<Longrightarrow>"}, not @{text"\<longrightarrow>"}. Here is an example:
*}

lemma "\<lbrakk> A \<Longrightarrow> False \<rbrakk> \<Longrightarrow> \<not> A"
proof
  assume "A \<Longrightarrow> False" "A"
  thus False .
qed

text{*\noindent The \isacommand{proof} always works on the conclusion,
@{prop"\<not>A"} in our case, thus selecting $\neg$-introduction. Hence we can
additionally assume @{prop"A"}.

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
@{text"("}\isacommand{is}~\emph{pattern}@{text")"} which causes the pattern
to be matched against the formula, instantiating the ?-variables in the
pattern. Subsequent uses of these variables in other terms simply causes them
to be replaced by the terms they stand for.

We can simplify things even more by stating the theorem by means of the
\isacommand{assumes} and \isacommand{shows} primitives which allow direct
naming of assumptions: *}

lemma assumes A: "large_formula \<Longrightarrow> False"
      shows "\<not> large_formula" (is "\<not> ?P")
proof
  assume ?P
  with A show False .
qed

text{*\noindent Here we have used the abbreviation
\begin{center}
\isacommand{with}~\emph{facts} \quad = \quad
\isacommand{from}~\emph{facts} \isacommand{and} @{text this}
\end{center}

Sometimes it is necessary to supress the implicit application of rules in a
\isacommand{proof}. For example \isacommand{show}~@{prop"A \<or> B"} would
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

text{* Command \isacommand{fix} introduces new local variables into a
proof. It corresponds to @{text"\<And>"} (the universal quantifier at the
meta-level) just like \isacommand{assume}-\isacommand{show} corresponds to
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
 ``\isakeyword{obtain}'' provides a more handsome way to perform
generalized existence reasoning:
*}

lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
  from Pf obtain x where "P(f x)" ..
  thus "\<exists>y. P y" ..
qed

text {*\noindent Note how the proof text follows the usual mathematical style
of concluding $P x$ from $\exists x. P(x)$, while carefully introducing $x$
as a new local variable.
Technically, \isakeyword{obtain} is similar to \isakeyword{fix} and
\isakeyword{assume} together with a soundness proof of the
elimination involved.  Thus it behaves similar to any other forward
proof element.

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
    proof (cases)
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
\item Proof by @{text"(cases)"} starts a proof by cases. Note that it remains
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
    proof (cases)
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

section{*Induction*}

lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)"
by (induct n, simp_all)

lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

(* Could refine further, but not necessary *)

lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc thus ?case by simp
qed




consts itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec
"itrev []     ys = ys"
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma "\<And>ys. itrev xs ys = rev xs @ ys"
by (induct xs, simp_all)

(* The !! just disappears. Even more pronounced for \<Longrightarrow> *)

lemma r: assumes A: "(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  shows "\<And>m. m < n \<Longrightarrow> P(m::nat)"
proof (induct n)
  case 0 hence False by simp thus ?case ..
next
  case (Suc n m)
  show ?case
  proof (cases)
    assume eq: "m = n"
    have "P n" sorry
    with eq show "P m" by simp
  next
    assume neq: "m \<noteq> n"
    with Suc have "m < n" by simp
    with Suc show "P m" by blast
  qed
  


thm r
thm r[of _ n "Suc n", simplified]

lemma "(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n) \<Longrightarrow> P n"

lemma assumes P0: "P 0" and P1: "P(Suc 0)"
      and P2: "\<And>k. P k \<Longrightarrow> P(Suc (Suc k))" shows "P n"
proof (induct n rule: nat_less_induct)
thm nat_less_induct
  fix n assume "\<forall>m. m < n \<longrightarrow> P m"
  show "P n"
  proof (cases n)
    assume "n=0" thus "P n" by simp
  next
    fix m assume n: "n = Suc m"
    show "P n"
    proof (cases m)
      assume "m=0" with n show "P n" by simp
    next
      fix l assume "m = Suc l"
      with  n show "P n" apply simp

by (case_tac "n" 1);
by (case_tac "nat" 2);
by (ALLGOALS (blast_tac (claset() addIs prems@[less_trans])));
qed "nat_induct2";

consts rtc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"   ("_*" [1000] 999)
inductive "r*"
intros
rtc_refl[iff]:  "(x,x) \<in> r*"
rtc_step:       "\<lbrakk> (x,y) \<in> r; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

lemma [intro]: "(x,y) : r \<Longrightarrow> (x,y) \<in> r*"
by(blast intro: rtc_step);

lemma assumes A:"(x,y) \<in> r*" and B:"(y,z) \<in> r*" shows "(x,z) \<in> r*"
proof -
  from A B show ?thesis
  proof (induct)
    fix x assume "(x,z) \<in> r*" thus "(x,z) \<in> r*" .
  next
    fix x y 
qed

text{*
\begin{exercise}
Show that the converse of @{thm[source]rtc_step} also holds:
@{prop[display]"[| (x,y) : r*; (y,z) : r |] ==> (x,z) : r*"}
\end{exercise}*}



text{*As always, the different cases can be tackled in any order.*}

(*<*)end(*>*)
