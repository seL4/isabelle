(*<*)theory Even imports Main begin
ML_file "../../antiquote_setup.ML" 
setup Antiquote_Setup.setup
(*>*)

section{* The Set of Even Numbers *}

text {*
\index{even numbers!defining inductively|(}%
The set of even numbers can be inductively defined as the least set
containing 0 and closed under the operation $+2$.  Obviously,
\emph{even} can also be expressed using the divides relation (@{text dvd}). 
We shall prove below that the two formulations coincide.  On the way we
shall examine the primary means of reasoning about inductively defined
sets: rule induction.
*}

subsection{* Making an Inductive Definition *}

text {*
Using \commdx{inductive\protect\_set}, we declare the constant @{text even} to be
a set of natural numbers with the desired properties.
*}

inductive_set even :: "nat set" where
zero[intro!]: "0 \<in> even" |
step[intro!]: "n \<in> even \<Longrightarrow> (Suc (Suc n)) \<in> even"

text {*
An inductive definition consists of introduction rules.  The first one
above states that 0 is even; the second states that if $n$ is even, then so
is~$n+2$.  Given this declaration, Isabelle generates a fixed point
definition for @{term even} and proves theorems about it,
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
@{text step} rule is also safe because $n+2$ is even if and only if $n$ is
even.  We prove this equivalence later.
*}

subsection{*Using Introduction Rules*}

text {*
Our first lemma states that numbers of the form $2\times k$ are even.
Introduction rules are used to show that specific values belong to the
inductive set.  Such proofs typically involve 
induction, perhaps over some other inductive set.
*}

lemma two_times_even[intro!]: "2*k \<in> even"
apply (induct_tac k)
 apply auto
done
(*<*)
lemma "2*k \<in> even"
apply (induct_tac k)
(*>*)
txt {*
\noindent
The first step is induction on the natural number @{text k}, which leaves
two subgoals:
@{subgoals[display,indent=0,margin=65]}
Here @{text auto} simplifies both subgoals so that they match the introduction
rules, which are then applied automatically.

Our ultimate goal is to prove the equivalence between the traditional
definition of @{text even} (using the divides relation) and our inductive
definition.  One direction of this equivalence is immediate by the lemma
just proved, whose @{text "intro!"} attribute ensures it is applied automatically.
*}
(*<*)oops(*>*)
lemma dvd_imp_even: "2 dvd n \<Longrightarrow> n \<in> even"
by (auto simp add: dvd_def)

subsection{* Rule Induction \label{sec:rule-induction} *}

text {*
\index{rule induction|(}%
From the definition of the set
@{term even}, Isabelle has
generated an induction rule:
@{named_thms [display,indent=0,margin=40] even.induct [no_vars] (even.induct)}
A property @{term P} holds for every even number provided it
holds for~@{text 0} and is closed under the operation
\isa{Suc(Suc \(\cdot\))}.  Then @{term P} is closed under the introduction
rules for @{term even}, which is the least set closed under those rules. 
This type of inductive argument is called \textbf{rule induction}. 

Apart from the double application of @{term Suc}, the induction rule above
resembles the familiar mathematical induction, which indeed is an instance
of rule induction; the natural numbers can be defined inductively to be
the least set containing @{text 0} and closed under~@{term Suc}.

Induction is the usual way of proving a property of the elements of an
inductively defined set.  Let us prove that all members of the set
@{term even} are multiples of two.
*}

lemma even_imp_dvd: "n \<in> even \<Longrightarrow> 2 dvd n"
txt {*
We begin by applying induction.  Note that @{text even.induct} has the form
of an elimination rule, so we use the method @{text erule}.  We get two
subgoals:
*}
apply (erule even.induct)
txt {*
@{subgoals[display,indent=0]}
We unfold the definition of @{text dvd} in both subgoals, proving the first
one and simplifying the second:
*}
apply (simp_all add: dvd_def)
txt {*
@{subgoals[display,indent=0]}
The next command eliminates the existential quantifier from the assumption
and replaces @{text n} by @{text "2 * k"}.
*}
apply clarify
txt {*
@{subgoals[display,indent=0]}
To conclude, we tell Isabelle that the desired value is
@{term "Suc k"}.  With this hint, the subgoal falls to @{text simp}.
*}
apply (rule_tac x = "Suc k" in exI, simp)
(*<*)done(*>*)

text {*
Combining the previous two results yields our objective, the
equivalence relating @{term even} and @{text dvd}. 
%
%we don't want [iff]: discuss?
*}

theorem even_iff_dvd: "(n \<in> even) = (2 dvd n)"
by (blast intro: dvd_imp_even even_imp_dvd)


subsection{* Generalization and Rule Induction \label{sec:gen-rule-induction} *}

text {*
\index{generalizing for induction}%
Before applying induction, we typically must generalize
the induction formula.  With rule induction, the required generalization
can be hard to find and sometimes requires a complete reformulation of the
problem.  In this  example, our first attempt uses the obvious statement of
the result.  It fails:
*}

lemma "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
apply (erule even.induct)
oops
(*<*)
lemma "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
apply (erule even.induct)
(*>*)
txt {*
Rule induction finds no occurrences of @{term "Suc(Suc n)"} in the
conclusion, which it therefore leaves unchanged.  (Look at
@{text even.induct} to see why this happens.)  We have these subgoals:
@{subgoals[display,indent=0]}
The first one is hopeless.  Rule induction on
a non-variable term discards information, and usually fails.
How to deal with such situations
in general is described in {\S}\ref{sec:ind-var-in-prems} below.
In the current case the solution is easy because
we have the necessary inverse, subtraction:
*}
(*<*)oops(*>*)
lemma even_imp_even_minus_2: "n \<in> even \<Longrightarrow> n - 2 \<in> even"
apply (erule even.induct)
 apply auto
done
(*<*)
lemma "n \<in>  even \<Longrightarrow> n - 2 \<in> even"
apply (erule even.induct)
(*>*)
txt {*
This lemma is trivially inductive.  Here are the subgoals:
@{subgoals[display,indent=0]}
The first is trivial because @{text "0 - 2"} simplifies to @{text 0}, which is
even.  The second is trivial too: @{term "Suc (Suc n) - 2"} simplifies to
@{term n}, matching the assumption.%
\index{rule induction|)}  %the sequel isn't really about induction

\medskip
Using our lemma, we can easily prove the result we originally wanted:
*}
(*<*)oops(*>*)
lemma Suc_Suc_even_imp_even: "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
by (drule even_imp_even_minus_2, simp)

text {*
We have just proved the converse of the introduction rule @{text even.step}.
This suggests proving the following equivalence.  We give it the
\attrdx{iff} attribute because of its obvious value for simplification.
*}

lemma [iff]: "((Suc (Suc n)) \<in> even) = (n \<in> even)"
by (blast dest: Suc_Suc_even_imp_even)


subsection{* Rule Inversion \label{sec:rule-inversion} *}

text {*
\index{rule inversion|(}%
Case analysis on an inductive definition is called \textbf{rule
inversion}.  It is frequently used in proofs about operational
semantics.  It can be highly effective when it is applied
automatically.  Let us look at how rule inversion is done in
Isabelle/HOL\@.

Recall that @{term even} is the minimal set closed under these two rules:
@{thm [display,indent=0] even.intros [no_vars]}
Minimality means that @{term even} contains only the elements that these
rules force it to contain.  If we are told that @{term a}
belongs to
@{term even} then there are only two possibilities.  Either @{term a} is @{text 0}
or else @{term a} has the form @{term "Suc(Suc n)"}, for some suitable @{term n}
that belongs to
@{term even}.  That is the gist of the @{term cases} rule, which Isabelle proves
for us when it accepts an inductive definition:
@{named_thms [display,indent=0,margin=40] even.cases [no_vars] (even.cases)}
This general rule is less useful than instances of it for
specific patterns.  For example, if @{term a} has the form
@{term "Suc(Suc n)"} then the first case becomes irrelevant, while the second
case tells us that @{term n} belongs to @{term even}.  Isabelle will generate
this instance for us:
*}

inductive_cases Suc_Suc_cases [elim!]: "Suc(Suc n) \<in> even"

text {*
The \commdx{inductive\protect\_cases} command generates an instance of
the @{text cases} rule for the supplied pattern and gives it the supplied name:
@{named_thms [display,indent=0] Suc_Suc_cases [no_vars] (Suc_Suc_cases)}
Applying this as an elimination rule yields one case where @{text even.cases}
would yield two.  Rule inversion works well when the conclusions of the
introduction rules involve datatype constructors like @{term Suc} and @{text "#"}
(list ``cons''); freeness reasoning discards all but one or two cases.

In the \isacommand{inductive\_cases} command we supplied an
attribute, @{text "elim!"},
\index{elim"!@\isa {elim"!} (attribute)}%
indicating that this elimination rule can be
applied aggressively.  The original
@{term cases} rule would loop if used in that manner because the
pattern~@{term a} matches everything.

The rule @{text Suc_Suc_cases} is equivalent to the following implication:
@{term [display,indent=0] "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"}
Just above we devoted some effort to reaching precisely
this result.  Yet we could have obtained it by a one-line declaration,
dispensing with the lemma @{text even_imp_even_minus_2}. 
This example also justifies the terminology
\textbf{rule inversion}: the new rule inverts the introduction rule
@{text even.step}.  In general, a rule can be inverted when the set of elements
it introduces is disjoint from those of the other introduction rules.

For one-off applications of rule inversion, use the \methdx{ind_cases} method. 
Here is an example:
*}

(*<*)lemma "Suc(Suc n) \<in> even \<Longrightarrow> P"(*>*)
apply (ind_cases "Suc(Suc n) \<in> even")
(*<*)oops(*>*)

text {*
The specified instance of the @{text cases} rule is generated, then applied
as an elimination rule.

To summarize, every inductive definition produces a @{text cases} rule.  The
\commdx{inductive\protect\_cases} command stores an instance of the
@{text cases} rule for a given pattern.  Within a proof, the
@{text ind_cases} method applies an instance of the @{text cases}
rule.

The even numbers example has shown how inductive definitions can be
used.  Later examples will show that they are actually worth using.%
\index{rule inversion|)}%
\index{even numbers!defining inductively|)}
*}

(*<*)end(*>*)
