(*<*)
theory AdvancedInd = Main:;
(*>*)

text{*\noindent
Now that we have learned about rules and logic, we take another look at the
finer points of induction. The two questions we answer are: what to do if the
proposition to be proved is not directly amenable to induction
(\S\ref{sec:ind-var-in-prems}), and how to utilize (\S\ref{sec:complete-ind})
and even derive (\S\ref{sec:derive-ind}) new induction schemas. We conclude
with an extended example of induction (\S\ref{sec:CTL-revisited}).
*};

subsection{*Massaging the Proposition*};

text{*\label{sec:ind-var-in-prems}
Often we have assumed that the theorem we want to prove is already in a form
that is amenable to induction, but sometimes it isn't.
Here is an example.
Since @{term"hd"} and @{term"last"} return the first and last element of a
non-empty list, this lemma looks easy to prove:
*};

lemma "xs \<noteq> [] \<Longrightarrow> hd(rev xs) = last xs"
apply(induct_tac xs)

txt{*\noindent
But induction produces the warning
\begin{quote}\tt
Induction variable occurs also among premises!
\end{quote}
and leads to the base case
@{subgoals[display,indent=0,goals_limit=1]}
After simplification, it becomes
\begin{isabelle}
\ 1.\ xs\ {\isasymnoteq}\ []\ {\isasymLongrightarrow}\ hd\ []\ =\ last\ []
\end{isabelle}
We cannot prove this equality because we do not know what @{term hd} and
@{term last} return when applied to @{term"[]"}.

We should not have ignored the warning. Because the induction
formula is only the conclusion, induction does not affect the occurrence of @{term xs} in the premises.  
Thus the case that should have been trivial
becomes unprovable. Fortunately, the solution is easy:\footnote{A very similar
heuristic applies to rule inductions; see \S\ref{sec:rtc}.}
\begin{quote}
\emph{Pull all occurrences of the induction variable into the conclusion
using @{text"\<longrightarrow>"}.}
\end{quote}
Thus we should state the lemma as an ordinary 
implication~(@{text"\<longrightarrow>"}), letting
@{text rule_format} (\S\ref{sec:forward}) convert the
result to the usual @{text"\<Longrightarrow>"} form:
*};
(*<*)oops;(*>*)
lemma hd_rev [rule_format]: "xs \<noteq> [] \<longrightarrow> hd(rev xs) = last xs";
(*<*)
apply(induct_tac xs);
(*>*)

txt{*\noindent
This time, induction leaves us with a trivial base case:
@{subgoals[display,indent=0,goals_limit=1]}
And @{text"auto"} completes the proof.

If there are multiple premises $A@1$, \dots, $A@n$ containing the
induction variable, you should turn the conclusion $C$ into
\[ A@1 \longrightarrow \cdots A@n \longrightarrow C \]
Additionally, you may also have to universally quantify some other variables,
which can yield a fairly complex conclusion.  However, @{text rule_format} 
can remove any number of occurrences of @{text"\<forall>"} and
@{text"\<longrightarrow>"}.
*}

(*<*)
by auto;
(*>*)
(*
Here is a simple example (which is proved by @{text"blast"}):
lemma simple[rule_format]:  "\<forall>y. A y \<longrightarrow> B y \<longrightarrow> B y \<and> A y";
by blast;
*)

text{*
A second reason why your proposition may not be amenable to induction is that
you want to induct on a whole term, rather than an individual variable. In
general, when inducting on some term $t$ you must rephrase the conclusion $C$
as
\[ \forall y@1 \dots y@n.~ x = t \longrightarrow C \]
where $y@1 \dots y@n$ are the free variables in $t$ and $x$ is new, and
perform induction on $x$ afterwards. An example appears in
\S\ref{sec:complete-ind} below.

The very same problem may occur in connection with rule induction. Remember
that it requires a premise of the form $(x@1,\dots,x@k) \in R$, where $R$ is
some inductively defined set and the $x@i$ are variables.  If instead we have
a premise $t \in R$, where $t$ is not just an $n$-tuple of variables, we
replace it with $(x@1,\dots,x@k) \in R$, and rephrase the conclusion $C$ as
\[ \forall y@1 \dots y@n.~ (x@1,\dots,x@k) = t \longrightarrow C \]
For an example see \S\ref{sec:CTL-revisited} below.

Of course, all premises that share free variables with $t$ need to be pulled into
the conclusion as well, under the @{text"\<forall>"}, again using @{text"\<longrightarrow>"} as shown above.
*};

subsection{*Beyond Structural and Recursion Induction*};

text{*\label{sec:complete-ind}
So far, inductive proofs were by structural induction for
primitive recursive functions and recursion induction for total recursive
functions. But sometimes structural induction is awkward and there is no
recursive function that could furnish a more appropriate
induction schema. In such cases a general-purpose induction schema can
be helpful. We show how to apply such induction schemas by an example.

Structural induction on @{typ"nat"} is
usually known as mathematical induction. There is also \emph{complete}
induction, where you must prove $P(n)$ under the assumption that $P(m)$
holds for all $m<n$. In Isabelle, this is the theorem @{thm[source]nat_less_induct}:
@{thm[display]"nat_less_induct"[no_vars]}
Here is an example of its application.
*};

consts f :: "nat \<Rightarrow> nat";
axioms f_ax: "f(f(n)) < f(Suc(n))";

text{*\noindent
The axiom for @{term"f"} implies @{prop"n <= f n"}, which can
be proved by induction on \mbox{@{term"f n"}}. Following the recipe outlined
above, we have to phrase the proposition as follows to allow induction:
*};

lemma f_incr_lem: "\<forall>i. k = f i \<longrightarrow> i \<le> f i";

txt{*\noindent
To perform induction on @{term k} using @{thm[source]nat_less_induct}, we use
the same general induction method as for recursion induction (see
\S\ref{sec:recdef-induction}):
*};

apply(induct_tac k rule: nat_less_induct);

txt{*\noindent
which leaves us with the following proof state:
@{subgoals[display,indent=0,margin=65]}
After stripping the @{text"\<forall>i"}, the proof continues with a case
distinction on @{term"i"}. The case @{prop"i = 0"} is trivial and we focus on
the other case:
*}

apply(rule allI)
apply(case_tac i)
 apply(simp)
txt{*
@{subgoals[display,indent=0]}
*}
by(blast intro!: f_ax Suc_leI intro: le_less_trans)

text{*\noindent
If you find the last step puzzling, here are the two lemmas it employs:
\begin{isabelle}
@{thm Suc_leI[no_vars]}
\rulename{Suc_leI}\isanewline
@{thm le_less_trans[no_vars]}
\rulename{le_less_trans}
\end{isabelle}
%
The proof goes like this (writing @{term"j"} instead of @{typ"nat"}).
Since @{prop"i = Suc j"} it suffices to show
\hbox{@{prop"j < f(Suc j)"}},
by @{thm[source]Suc_leI}\@.  This is
proved as follows. From @{thm[source]f_ax} we have @{prop"f (f j) < f (Suc j)"}
(1) which implies @{prop"f j <= f (f j)"} by the induction hypothesis.
Using (1) once more we obtain @{prop"f j < f(Suc j)"} (2) by the transitivity
rule @{thm[source]le_less_trans}.
Using the induction hypothesis once more we obtain @{prop"j <= f j"}
which, together with (2) yields @{prop"j < f (Suc j)"} (again by
@{thm[source]le_less_trans}).

This last step shows both the power and the danger of automatic proofs: they
will usually not tell you how the proof goes, because it can be very hard to
translate the internal proof into a human-readable format. Therefore
Chapter~\ref{sec:part2?} introduces a language for writing readable
proofs.

We can now derive the desired @{prop"i <= f i"} from @{thm[source]f_incr_lem}:
*};

lemmas f_incr = f_incr_lem[rule_format, OF refl];

text{*\noindent
The final @{thm[source]refl} gets rid of the premise @{text"?k = f ?i"}. 
We could have included this derivation in the original statement of the lemma:
*};

lemma f_incr[rule_format, OF refl]: "\<forall>i. k = f i \<longrightarrow> i \<le> f i";
(*<*)oops;(*>*)

text{*
\begin{warn}
We discourage the use of axioms because of the danger of
inconsistencies.  Axiom @{text f_ax} does
not introduce an inconsistency because, for example, the identity function
satisfies it.  Axioms can be useful in exploratory developments, say when 
you assume some well-known theorems so that you can quickly demonstrate some
point about methodology.  If your example turns into a substantial proof
development, you should replace the axioms by proofs.
\end{warn}

\bigskip
In general, @{text induct_tac} can be applied with any rule $r$
whose conclusion is of the form ${?}P~?x@1 \dots ?x@n$, in which case the
format is
\begin{quote}
\isacommand{apply}@{text"(induct_tac"} $y@1 \dots y@n$ @{text"rule:"} $r$@{text")"}
\end{quote}\index{*induct_tac}%
where $y@1, \dots, y@n$ are variables in the first subgoal.
A further example of a useful induction rule is @{thm[source]length_induct},
induction on the length of a list:\indexbold{*length_induct}
@{thm[display]length_induct[no_vars]}

In fact, @{text"induct_tac"} even allows the conclusion of
$r$ to be an (iterated) conjunction of formulae of the above form, in
which case the application is
\begin{quote}
\isacommand{apply}@{text"(induct_tac"} $y@1 \dots y@n$ @{text"and"} \dots\ @{text"and"} $z@1 \dots z@m$ @{text"rule:"} $r$@{text")"}
\end{quote}

\begin{exercise}
From the axiom and lemma for @{term"f"}, show that @{term"f"} is the
identity function.
\end{exercise}
*};

subsection{*Derivation of New Induction Schemas*};

text{*\label{sec:derive-ind}
Induction schemas are ordinary theorems and you can derive new ones
whenever you wish.  This section shows you how to, using the example
of @{thm[source]nat_less_induct}. Assume we only have structural induction
available for @{typ"nat"} and want to derive complete induction. This
requires us to generalize the statement first:
*};

lemma induct_lem: "(\<And>n::nat. \<forall>m<n. P m \<Longrightarrow> P n) \<Longrightarrow> \<forall>m<n. P m";
apply(induct_tac n);

txt{*\noindent
The base case is vacuously true. For the induction step (@{prop"m <
Suc n"}) we distinguish two cases: case @{prop"m < n"} is true by induction
hypothesis and case @{prop"m = n"} follows from the assumption, again using
the induction hypothesis:
*};
 apply(blast);
by(blast elim:less_SucE)

text{*\noindent
The elimination rule @{thm[source]less_SucE} expresses the case distinction:
@{thm[display]"less_SucE"[no_vars]}

Now it is straightforward to derive the original version of
@{thm[source]nat_less_induct} by manipulting the conclusion of the above lemma:
instantiate @{term"n"} by @{term"Suc n"} and @{term"m"} by @{term"n"} and
remove the trivial condition @{prop"n < Suc n"}. Fortunately, this
happens automatically when we add the lemma as a new premise to the
desired goal:
*};

theorem nat_less_induct: "(\<And>n::nat. \<forall>m<n. P m \<Longrightarrow> P n) \<Longrightarrow> P n";
by(insert induct_lem, blast);

text{*
Finally we should remind the reader that HOL already provides the mother of
all inductions, well-founded induction (see \S\ref{sec:Well-founded}).  For
example theorem @{thm[source]nat_less_induct} is
a special case of @{thm[source]wf_induct} where @{term r} is @{text"<"} on
@{typ nat}. The details can be found in theory \isa{Wellfounded_Recursion}.
*}
(*<*)end(*>*)
