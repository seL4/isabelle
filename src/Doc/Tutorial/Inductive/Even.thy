(*<*)theory Even imports "../Setup" begin(*>*)

section\<open>The Set of Even Numbers\<close>

text \<open>
\index{even numbers!defining inductively|(}%
The set of even numbers can be inductively defined as the least set
containing 0 and closed under the operation $+2$.  Obviously,
\emph{even} can also be expressed using the divides relation (\<open>dvd\<close>). 
We shall prove below that the two formulations coincide.  On the way we
shall examine the primary means of reasoning about inductively defined
sets: rule induction.
\<close>

subsection\<open>Making an Inductive Definition\<close>

text \<open>
Using \commdx{inductive\protect\_set}, we declare the constant \<open>even\<close> to be
a set of natural numbers with the desired properties.
\<close>

inductive_set even :: "nat set" where
zero[intro!]: "0 \<in> even" |
step[intro!]: "n \<in> even \<Longrightarrow> (Suc (Suc n)) \<in> even"

text \<open>
An inductive definition consists of introduction rules.  The first one
above states that 0 is even; the second states that if $n$ is even, then so
is~$n+2$.  Given this declaration, Isabelle generates a fixed point
definition for \<^term>\<open>even\<close> and proves theorems about it,
thus following the definitional approach (see {\S}\ref{sec:definitional}).
These theorems
include the introduction rules specified in the declaration, an elimination
rule for case analysis and an induction rule.  We can refer to these
theorems by automatically-generated names.  Here are two examples:
@{named_thms[display,indent=0] even.zero[no_vars] (even.zero) even.step[no_vars] (even.step)}

The introduction rules can be given attributes.  Here
both rules are specified as \isa{intro!},%
\index{intro"!@\isa {intro"!} (attribute)}
directing the classical reasoner to 
apply them aggressively. Obviously, regarding 0 as even is safe.  The
\<open>step\<close> rule is also safe because $n+2$ is even if and only if $n$ is
even.  We prove this equivalence later.
\<close>

subsection\<open>Using Introduction Rules\<close>

text \<open>
Our first lemma states that numbers of the form $2\times k$ are even.
Introduction rules are used to show that specific values belong to the
inductive set.  Such proofs typically involve 
induction, perhaps over some other inductive set.
\<close>

lemma two_times_even[intro!]: "2*k \<in> even"
apply (induct_tac k)
 apply auto
done
(*<*)
lemma "2*k \<in> even"
apply (induct_tac k)
(*>*)
txt \<open>
\noindent
The first step is induction on the natural number \<open>k\<close>, which leaves
two subgoals:
@{subgoals[display,indent=0,margin=65]}
Here \<open>auto\<close> simplifies both subgoals so that they match the introduction
rules, which are then applied automatically.

Our ultimate goal is to prove the equivalence between the traditional
definition of \<open>even\<close> (using the divides relation) and our inductive
definition.  One direction of this equivalence is immediate by the lemma
just proved, whose \<open>intro!\<close> attribute ensures it is applied automatically.
\<close>
(*<*)oops(*>*)
lemma dvd_imp_even: "2 dvd n \<Longrightarrow> n \<in> even"
by (auto simp add: dvd_def)

subsection\<open>Rule Induction \label{sec:rule-induction}\<close>

text \<open>
\index{rule induction|(}%
From the definition of the set
\<^term>\<open>even\<close>, Isabelle has
generated an induction rule:
@{named_thms [display,indent=0,margin=40] even.induct [no_vars] (even.induct)}
A property \<^term>\<open>P\<close> holds for every even number provided it
holds for~\<open>0\<close> and is closed under the operation
\isa{Suc(Suc \(\cdot\))}.  Then \<^term>\<open>P\<close> is closed under the introduction
rules for \<^term>\<open>even\<close>, which is the least set closed under those rules. 
This type of inductive argument is called \textbf{rule induction}. 

Apart from the double application of \<^term>\<open>Suc\<close>, the induction rule above
resembles the familiar mathematical induction, which indeed is an instance
of rule induction; the natural numbers can be defined inductively to be
the least set containing \<open>0\<close> and closed under~\<^term>\<open>Suc\<close>.

Induction is the usual way of proving a property of the elements of an
inductively defined set.  Let us prove that all members of the set
\<^term>\<open>even\<close> are multiples of two.
\<close>

lemma even_imp_dvd: "n \<in> even \<Longrightarrow> 2 dvd n"
txt \<open>
We begin by applying induction.  Note that \<open>even.induct\<close> has the form
of an elimination rule, so we use the method \<open>erule\<close>.  We get two
subgoals:
\<close>
apply (erule even.induct)
txt \<open>
@{subgoals[display,indent=0]}
We unfold the definition of \<open>dvd\<close> in both subgoals, proving the first
one and simplifying the second:
\<close>
apply (simp_all add: dvd_def)
txt \<open>
@{subgoals[display,indent=0]}
The next command eliminates the existential quantifier from the assumption
and replaces \<open>n\<close> by \<open>2 * k\<close>.
\<close>
apply clarify
txt \<open>
@{subgoals[display,indent=0]}
To conclude, we tell Isabelle that the desired value is
\<^term>\<open>Suc k\<close>.  With this hint, the subgoal falls to \<open>simp\<close>.
\<close>
apply (rule_tac x = "Suc k" in exI, simp)
(*<*)done(*>*)

text \<open>
Combining the previous two results yields our objective, the
equivalence relating \<^term>\<open>even\<close> and \<open>dvd\<close>. 
%
%we don't want [iff]: discuss?
\<close>

theorem even_iff_dvd: "(n \<in> even) = (2 dvd n)"
by (blast intro: dvd_imp_even even_imp_dvd)


subsection\<open>Generalization and Rule Induction \label{sec:gen-rule-induction}\<close>

text \<open>
\index{generalizing for induction}%
Before applying induction, we typically must generalize
the induction formula.  With rule induction, the required generalization
can be hard to find and sometimes requires a complete reformulation of the
problem.  In this  example, our first attempt uses the obvious statement of
the result.  It fails:
\<close>

lemma "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
apply (erule even.induct)
oops
(*<*)
lemma "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
apply (erule even.induct)
(*>*)
txt \<open>
Rule induction finds no occurrences of \<^term>\<open>Suc(Suc n)\<close> in the
conclusion, which it therefore leaves unchanged.  (Look at
\<open>even.induct\<close> to see why this happens.)  We have these subgoals:
@{subgoals[display,indent=0]}
The first one is hopeless.  Rule induction on
a non-variable term discards information, and usually fails.
How to deal with such situations
in general is described in {\S}\ref{sec:ind-var-in-prems} below.
In the current case the solution is easy because
we have the necessary inverse, subtraction:
\<close>
(*<*)oops(*>*)
lemma even_imp_even_minus_2: "n \<in> even \<Longrightarrow> n - 2 \<in> even"
apply (erule even.induct)
 apply auto
done
(*<*)
lemma "n \<in>  even \<Longrightarrow> n - 2 \<in> even"
apply (erule even.induct)
(*>*)
txt \<open>
This lemma is trivially inductive.  Here are the subgoals:
@{subgoals[display,indent=0]}
The first is trivial because \<open>0 - 2\<close> simplifies to \<open>0\<close>, which is
even.  The second is trivial too: \<^term>\<open>Suc (Suc n) - 2\<close> simplifies to
\<^term>\<open>n\<close>, matching the assumption.%
\index{rule induction|)}  %the sequel isn't really about induction

\medskip
Using our lemma, we can easily prove the result we originally wanted:
\<close>
(*<*)oops(*>*)
lemma Suc_Suc_even_imp_even: "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
by (drule even_imp_even_minus_2, simp)

text \<open>
We have just proved the converse of the introduction rule \<open>even.step\<close>.
This suggests proving the following equivalence.  We give it the
\attrdx{iff} attribute because of its obvious value for simplification.
\<close>

lemma [iff]: "((Suc (Suc n)) \<in> even) = (n \<in> even)"
by (blast dest: Suc_Suc_even_imp_even)


subsection\<open>Rule Inversion \label{sec:rule-inversion}\<close>

text \<open>
\index{rule inversion|(}%
Case analysis on an inductive definition is called \textbf{rule
inversion}.  It is frequently used in proofs about operational
semantics.  It can be highly effective when it is applied
automatically.  Let us look at how rule inversion is done in
Isabelle/HOL\@.

Recall that \<^term>\<open>even\<close> is the minimal set closed under these two rules:
@{thm [display,indent=0] even.intros [no_vars]}
Minimality means that \<^term>\<open>even\<close> contains only the elements that these
rules force it to contain.  If we are told that \<^term>\<open>a\<close>
belongs to
\<^term>\<open>even\<close> then there are only two possibilities.  Either \<^term>\<open>a\<close> is \<open>0\<close>
or else \<^term>\<open>a\<close> has the form \<^term>\<open>Suc(Suc n)\<close>, for some suitable \<^term>\<open>n\<close>
that belongs to
\<^term>\<open>even\<close>.  That is the gist of the \<^term>\<open>cases\<close> rule, which Isabelle proves
for us when it accepts an inductive definition:
@{named_thms [display,indent=0,margin=40] even.cases [no_vars] (even.cases)}
This general rule is less useful than instances of it for
specific patterns.  For example, if \<^term>\<open>a\<close> has the form
\<^term>\<open>Suc(Suc n)\<close> then the first case becomes irrelevant, while the second
case tells us that \<^term>\<open>n\<close> belongs to \<^term>\<open>even\<close>.  Isabelle will generate
this instance for us:
\<close>

inductive_cases Suc_Suc_cases [elim!]: "Suc(Suc n) \<in> even"

text \<open>
The \commdx{inductive\protect\_cases} command generates an instance of
the \<open>cases\<close> rule for the supplied pattern and gives it the supplied name:
@{named_thms [display,indent=0] Suc_Suc_cases [no_vars] (Suc_Suc_cases)}
Applying this as an elimination rule yields one case where \<open>even.cases\<close>
would yield two.  Rule inversion works well when the conclusions of the
introduction rules involve datatype constructors like \<^term>\<open>Suc\<close> and \<open>#\<close>
(list ``cons''); freeness reasoning discards all but one or two cases.

In the \isacommand{inductive\_cases} command we supplied an
attribute, \<open>elim!\<close>,
\index{elim"!@\isa {elim"!} (attribute)}%
indicating that this elimination rule can be
applied aggressively.  The original
\<^term>\<open>cases\<close> rule would loop if used in that manner because the
pattern~\<^term>\<open>a\<close> matches everything.

The rule \<open>Suc_Suc_cases\<close> is equivalent to the following implication:
@{term [display,indent=0] "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"}
Just above we devoted some effort to reaching precisely
this result.  Yet we could have obtained it by a one-line declaration,
dispensing with the lemma \<open>even_imp_even_minus_2\<close>. 
This example also justifies the terminology
\textbf{rule inversion}: the new rule inverts the introduction rule
\<open>even.step\<close>.  In general, a rule can be inverted when the set of elements
it introduces is disjoint from those of the other introduction rules.

For one-off applications of rule inversion, use the \methdx{ind_cases} method. 
Here is an example:
\<close>

(*<*)lemma "Suc(Suc n) \<in> even \<Longrightarrow> P"(*>*)
apply (ind_cases "Suc(Suc n) \<in> even")
(*<*)oops(*>*)

text \<open>
The specified instance of the \<open>cases\<close> rule is generated, then applied
as an elimination rule.

To summarize, every inductive definition produces a \<open>cases\<close> rule.  The
\commdx{inductive\protect\_cases} command stores an instance of the
\<open>cases\<close> rule for a given pattern.  Within a proof, the
\<open>ind_cases\<close> method applies an instance of the \<open>cases\<close>
rule.

The even numbers example has shown how inductive definitions can be
used.  Later examples will show that they are actually worth using.%
\index{rule inversion|)}%
\index{even numbers!defining inductively|)}
\<close>

(*<*)end(*>*)
