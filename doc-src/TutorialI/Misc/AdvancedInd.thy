(*<*)
theory AdvancedInd = Main:;
(*>*)

text{*\noindent
Now that we have learned about rules and logic, we take another look at the
finer points of induction. The two questions we answer are: what to do if the
proposition to be proved is not directly amenable to induction, and how to
utilize and even derive new induction schemas.
*};

subsection{*Massaging the proposition\label{sec:ind-var-in-prems}*};

text{*
\noindent
So far we have assumed that the theorem we want to prove is already in a form
that is amenable to induction, but this is not always the case:
*};

lemma "xs \\<noteq> [] \\<Longrightarrow> hd(rev xs) = last xs";
apply(induct_tac xs);

txt{*\noindent
(where @{term"hd"} and @{term"last"} return the first and last element of a
non-empty list)
produces the warning
\begin{quote}\tt
Induction variable occurs also among premises!
\end{quote}
and leads to the base case
\begin{isabelle}
\ 1.\ xs\ {\isasymnoteq}\ []\ {\isasymLongrightarrow}\ hd\ (rev\ [])\ =\ last\ []
\end{isabelle}
which, after simplification, becomes
\begin{isabelle}
\ 1.\ xs\ {\isasymnoteq}\ []\ {\isasymLongrightarrow}\ hd\ []\ =\ last\ []
\end{isabelle}
We cannot prove this equality because we do not know what @{term"hd"} and
@{term"last"} return when applied to @{term"[]"}.

The point is that we have violated the above warning. Because the induction
formula is only the conclusion, the occurrence of @{term"xs"} in the premises is
not modified by induction. Thus the case that should have been trivial
becomes unprovable. Fortunately, the solution is easy:
\begin{quote}
\emph{Pull all occurrences of the induction variable into the conclusion
using @{text"\<longrightarrow>"}.}
\end{quote}
This means we should prove
*};
(*<*)oops;(*>*)
lemma hd_rev: "xs \\<noteq> [] \\<longrightarrow> hd(rev xs) = last xs";
(*<*)
by(induct_tac xs, auto);
(*>*)

text{*\noindent
This time, induction leaves us with the following base case
\begin{isabelle}
\ 1.\ []\ {\isasymnoteq}\ []\ {\isasymlongrightarrow}\ hd\ (rev\ [])\ =\ last\ []
\end{isabelle}
which is trivial, and @{text"auto"} finishes the whole proof.

If @{thm[source]hd_rev} is meant to be a simplification rule, you are
done. But if you really need the @{text"\<Longrightarrow>"}-version of
@{thm[source]hd_rev}, for example because you want to apply it as an
introduction rule, you need to derive it separately, by combining it with
modus ponens:
*};

lemmas hd_revI = hd_rev[THEN mp];
 
text{*\noindent
which yields the lemma we originally set out to prove.

In case there are multiple premises $A@1$, \dots, $A@n$ containing the
induction variable, you should turn the conclusion $C$ into
\[ A@1 \longrightarrow \cdots A@n \longrightarrow C \]
(see the remark?? in \S\ref{??}).
Additionally, you may also have to universally quantify some other variables,
which can yield a fairly complex conclusion.
Here is a simple example (which is proved by @{text"blast"}):
*};

lemma simple: "\\<forall>y. A y \\<longrightarrow> B y \<longrightarrow> B y & A y";
(*<*)by blast;(*>*)

text{*\noindent
You can get the desired lemma by explicit
application of modus ponens and @{thm[source]spec}:
*};

lemmas myrule = simple[THEN spec, THEN mp, THEN mp];

text{*\noindent
or the wholesale stripping of @{text"\<forall>"} and
@{text"\<longrightarrow>"} in the conclusion via @{text"rulify"} 
*};

lemmas myrule = simple[rulify];

text{*\noindent
yielding @{thm"myrule"[no_vars]}.
You can go one step further and include these derivations already in the
statement of your original lemma, thus avoiding the intermediate step:
*};

lemma myrule[rulify]:  "\\<forall>y. A y \\<longrightarrow> B y \<longrightarrow> B y & A y";
(*<*)
by blast;
(*>*)

text{*
\bigskip

A second reason why your proposition may not be amenable to induction is that
you want to induct on a whole term, rather than an individual variable. In
general, when inducting on some term $t$ you must rephrase the conclusion as
\[ \forall y@1 \dots y@n.~ x = t \longrightarrow C \] where $y@1 \dots y@n$
are the free variables in $t$ and $x$ is new, and perform induction on $x$
afterwards. An example appears below.
*};

subsection{*Beyond structural and recursion induction*};

text{*
So far, inductive proofs where by structural induction for
primitive recursive functions and recursion induction for total recursive
functions. But sometimes structural induction is awkward and there is no
recursive function in sight either that could furnish a more appropriate
induction schema. In such cases some existing standard induction schema can
be helpful. We show how to apply such induction schemas by an example.

Structural induction on @{typ"nat"} is
usually known as ``mathematical induction''. There is also ``complete
induction'', where you must prove $P(n)$ under the assumption that $P(m)$
holds for all $m<n$. In Isabelle, this is the theorem @{thm[source]less_induct}:
@{thm[display]"less_induct"[no_vars]}
Here is an example of its application.
*};

consts f :: "nat => nat";
axioms f_ax: "f(f(n)) < f(Suc(n))";

text{*\noindent
From the above axiom\footnote{In general, the use of axioms is strongly
discouraged, because of the danger of inconsistencies. The above axiom does
not introduce an inconsistency because, for example, the identity function
satisfies it.}
for @{term"f"} it follows that @{prop"n <= f n"}, which can
be proved by induction on @{term"f n"}. Following the recipy outlined
above, we have to phrase the proposition as follows to allow induction:
*};

lemma f_incr_lem: "\\<forall>i. k = f i \\<longrightarrow> i \\<le> f i";

txt{*\noindent
To perform induction on @{term"k"} using @{thm[source]less_induct}, we use the same
general induction method as for recursion induction (see
\S\ref{sec:recdef-induction}):
*};

apply(induct_tac k rule:less_induct);
(*<*)
apply(rule allI);
apply(case_tac i);
 apply(simp);
(*>*)
txt{*\noindent
which leaves us with the following proof state:
\begin{isabelle}
\ 1.\ {\isasymAnd}\mbox{n}.\ {\isasymforall}\mbox{m}.\ \mbox{m}\ <\ \mbox{n}\ {\isasymlongrightarrow}\ ({\isasymforall}\mbox{i}.\ \mbox{m}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i})\isanewline
\ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isasymforall}\mbox{i}.\ \mbox{n}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i}
\end{isabelle}
After stripping the @{text"\<forall>i"}, the proof continues with a case
distinction on @{term"i"}. The case @{prop"i = 0"} is trivial and we focus on
the other case:
\begin{isabelle}
\ 1.\ {\isasymAnd}\mbox{n}\ \mbox{i}\ \mbox{nat}.\isanewline
\ \ \ \ \ \ \ {\isasymlbrakk}{\isasymforall}\mbox{m}.\ \mbox{m}\ <\ \mbox{n}\ {\isasymlongrightarrow}\ ({\isasymforall}\mbox{i}.\ \mbox{m}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i});\ \mbox{i}\ =\ Suc\ \mbox{nat}{\isasymrbrakk}\isanewline
\ \ \ \ \ \ \ {\isasymLongrightarrow}\ \mbox{n}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i}
\end{isabelle}
*};

by(blast intro!: f_ax Suc_leI intro:le_less_trans);

text{*\noindent
It is not surprising if you find the last step puzzling.
The proof goes like this (writing @{term"j"} instead of @{typ"nat"}).
Since @{prop"i = Suc j"} it suffices to show
@{prop"j < f(Suc j)"} (by @{thm[source]Suc_leI}: @{thm"Suc_leI"[no_vars]}). This is
proved as follows. From @{thm[source]f_ax} we have @{prop"f (f j) < f (Suc j)"}
(1) which implies @{prop"f j <= f (f j)"} (by the induction hypothesis).
Using (1) once more we obtain @{prop"f j < f(Suc j)"} (2) by transitivity
(@{thm[source]le_less_trans}: @{thm"le_less_trans"[no_vars]}).
Using the induction hypothesis once more we obtain @{prop"j <= f j"}
which, together with (2) yields @{prop"j < f (Suc j)"} (again by
@{thm[source]le_less_trans}).

This last step shows both the power and the danger of automatic proofs: they
will usually not tell you how the proof goes, because it can be very hard to
translate the internal proof into a human-readable format. Therefore
\S\ref{sec:part2?} introduces a language for writing readable yet concise
proofs.

We can now derive the desired @{prop"i <= f i"} from @{text"f_incr"}:
*};

lemmas f_incr = f_incr_lem[rulify, OF refl];

text{*\noindent
The final @{thm[source]refl} gets rid of the premise @{text"?k = f ?i"}. Again,
we could have included this derivation in the original statement of the lemma:
*};

lemma f_incr[rulify, OF refl]: "\\<forall>i. k = f i \\<longrightarrow> i \\<le> f i";
(*<*)oops;(*>*)

text{*
\begin{exercise}
From the above axiom and lemma for @{term"f"} show that @{term"f"} is the
identity.
\end{exercise}

In general, @{text"induct_tac"} can be applied with any rule $r$
whose conclusion is of the form ${?}P~?x@1 \dots ?x@n$, in which case the
format is
\begin{quote}
\isacommand{apply}@{text"(induct_tac"} $y@1 \dots y@n$ @{text"rule:"} $r$@{text")"}
\end{quote}\index{*induct_tac}%
where $y@1, \dots, y@n$ are variables in the first subgoal.
In fact, @{text"induct_tac"} even allows the conclusion of
$r$ to be an (iterated) conjunction of formulae of the above form, in
which case the application is
\begin{quote}
\isacommand{apply}@{text"(induct_tac"} $y@1 \dots y@n$ @{text"and"} \dots\ @{text"and"} $z@1 \dots z@m$ @{text"rule:"} $r$@{text")"}
\end{quote}
*};

subsection{*Derivation of new induction schemas*};

text{*\label{sec:derive-ind}
Induction schemas are ordinary theorems and you can derive new ones
whenever you wish.  This section shows you how to, using the example
of @{thm[source]less_induct}. Assume we only have structural induction
available for @{typ"nat"} and want to derive complete induction. This
requires us to generalize the statement first:
*};

lemma induct_lem: "(\\<And>n::nat. \\<forall>m<n. P m \\<Longrightarrow> P n) \\<Longrightarrow> \\<forall>m<n. P m";
apply(induct_tac n);

txt{*\noindent
The base case is trivially true. For the induction step (@{prop"m <
Suc n"}) we distinguish two cases: @{prop"m < n"} is true by induction
hypothesis and @{prop"m = n"} follow from the assumption again using
the induction hypothesis:
*};

apply(blast);
(* apply(blast elim:less_SucE); *)
ML"set quick_and_dirty"
sorry;
ML"reset quick_and_dirty"

text{*\noindent
The elimination rule @{thm[source]less_SucE} expresses the case distinction:
@{thm[display]"less_SucE"[no_vars]}

Now it is straightforward to derive the original version of
@{thm[source]less_induct} by manipulting the conclusion of the above lemma:
instantiate @{term"n"} by @{term"Suc n"} and @{term"m"} by @{term"n"} and
remove the trivial condition @{prop"n < Sc n"}. Fortunately, this
happens automatically when we add the lemma as a new premise to the
desired goal:
*};

theorem less_induct: "(\\<And>n::nat. \\<forall>m<n. P m \\<Longrightarrow> P n) \\<Longrightarrow> P n";
by(insert induct_lem, blast);

text{*\noindent
Finally we should mention that HOL already provides the mother of all
inductions, \emph{wellfounded induction} (@{thm[source]wf_induct}):
@{thm[display]"wf_induct"[no_vars]}
where @{term"wf r"} means that the relation @{term"r"} is wellfounded.
For example @{thm[source]less_induct} is the special case where @{term"r"} is
@{text"<"} on @{typ"nat"}. For details see the library.
*};

(*<*)
end
(*>*)
