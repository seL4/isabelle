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
(where \isa{hd} and \isa{last} return the first and last element of a
non-empty list)
produces the warning
\begin{quote}\tt
Induction variable occurs also among premises!
\end{quote}
and leads to the base case
\begin{isabellepar}%
\ 1.\ xs\ {\isasymnoteq}\ []\ {\isasymLongrightarrow}\ hd\ (rev\ [])\ =\ last\ []
\end{isabellepar}%
which, after simplification, becomes
\begin{isabellepar}%
\ 1.\ xs\ {\isasymnoteq}\ []\ {\isasymLongrightarrow}\ hd\ []\ =\ last\ []
\end{isabellepar}%
We cannot prove this equality because we do not know what \isa{hd} and
\isa{last} return when applied to \isa{[]}.

The point is that we have violated the above warning. Because the induction
formula is only the conclusion, the occurrence of \isa{xs} in the premises is
not modified by induction. Thus the case that should have been trivial
becomes unprovable. Fortunately, the solution is easy:
\begin{quote}
\emph{Pull all occurrences of the induction variable into the conclusion
using \isa{\isasymlongrightarrow}.}
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
\begin{isabellepar}%
\ 1.\ []\ {\isasymnoteq}\ []\ {\isasymlongrightarrow}\ hd\ (rev\ [])\ =\ last\ []
\end{isabellepar}%
which is trivial, and \isa{auto} finishes the whole proof.

If \isa{hd\_rev} is meant to be a simplification rule, you are done. But if you
really need the \isa{\isasymLongrightarrow}-version of \isa{hd\_rev}, for
example because you want to apply it as an introduction rule, you need to
derive it separately, by combining it with modus ponens:
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
Here is a simple example (which is proved by \isa{blast}):
*};

lemma simple: "\\<forall>y. A y \\<longrightarrow> B y \<longrightarrow> B y & A y";
(*<*)by blast;(*>*)

text{*\noindent
You can get the desired lemma by explicit
application of modus ponens and \isa{spec}:
*};

lemmas myrule = simple[THEN spec, THEN mp, THEN mp];

text{*\noindent
or the wholesale stripping of \isa{\isasymforall} and
\isa{\isasymlongrightarrow} in the conclusion via \isa{rulify} 
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

Structural induction on \isa{nat} is
usually known as ``mathematical induction''. There is also ``complete
induction'', where you must prove $P(n)$ under the assumption that $P(m)$
holds for all $m<n$. In Isabelle, this is the theorem \isa{less\_induct}:
\begin{quote}
@{thm[display]"less_induct"[no_vars]}
\end{quote}
Here is an example of its application.
*};

consts f :: "nat => nat";
axioms f_ax: "f(f(n)) < f(Suc(n))";

text{*\noindent
From the above axiom\footnote{In general, the use of axioms is strongly
discouraged, because of the danger of inconsistencies. The above axiom does
not introduce an inconsistency because, for example, the identity function
satisfies it.}
for \isa{f} it follows that @{term"n <= f n"}, which can
be proved by induction on @{term"f n"}. Following the recipy outlined
above, we have to phrase the proposition as follows to allow induction:
*};

lemma f_incr_lem: "\\<forall>i. k = f i \\<longrightarrow> i \\<le> f i";

txt{*\noindent
To perform induction on \isa{k} using \isa{less\_induct}, we use the same
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
\begin{isabellepar}%
\ 1.\ {\isasymAnd}\mbox{n}.\ {\isasymforall}\mbox{m}.\ \mbox{m}\ <\ \mbox{n}\ {\isasymlongrightarrow}\ ({\isasymforall}\mbox{i}.\ \mbox{m}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i})\isanewline
\ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isasymforall}\mbox{i}.\ \mbox{n}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i}
\end{isabellepar}%
After stripping the \isa{\isasymforall i}, the proof continues with a case
distinction on \isa{i}. The case \isa{i = 0} is trivial and we focus on the
other case:
\begin{isabellepar}%
\ 1.\ {\isasymAnd}\mbox{n}\ \mbox{i}\ \mbox{nat}.\isanewline
\ \ \ \ \ \ \ {\isasymlbrakk}{\isasymforall}\mbox{m}.\ \mbox{m}\ <\ \mbox{n}\ {\isasymlongrightarrow}\ ({\isasymforall}\mbox{i}.\ \mbox{m}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i});\ \mbox{i}\ =\ Suc\ \mbox{nat}{\isasymrbrakk}\isanewline
\ \ \ \ \ \ \ {\isasymLongrightarrow}\ \mbox{n}\ =\ f\ \mbox{i}\ {\isasymlongrightarrow}\ \mbox{i}\ {\isasymle}\ f\ \mbox{i}
\end{isabellepar}%
*};

by(blast intro!: f_ax Suc_leI intro:le_less_trans);

text{*\noindent
It is not surprising if you find the last step puzzling.
The proof goes like this (writing \isa{j} instead of \isa{nat}).
Since @{term"i = Suc j"} it suffices to show
@{term"j < f(Suc j)"} (by \isa{Suc\_leI}: @{thm"Suc_leI"[no_vars]}). This is
proved as follows. From \isa{f\_ax} we have @{term"f (f j) < f (Suc j)"}
(1) which implies @{term"f j <= f (f j)"} (by the induction hypothesis).
Using (1) once more we obtain @{term"f j < f(Suc j)"} (2) by transitivity
(\isa{le_less_trans}: @{thm"le_less_trans"[no_vars]}).
Using the induction hypothesis once more we obtain @{term"j <= f j"}
which, together with (2) yields @{term"j < f (Suc j)"} (again by
\isa{le_less_trans}).

This last step shows both the power and the danger of automatic proofs: they
will usually not tell you how the proof goes, because it can be very hard to
translate the internal proof into a human-readable format. Therefore
\S\ref{sec:part2?} introduces a language for writing readable yet concise
proofs.

We can now derive the desired @{term"i <= f i"} from \isa{f\_incr}:
*};

lemmas f_incr = f_incr_lem[rulify, OF refl];

text{*\noindent
The final \isa{refl} gets rid of the premise \isa{?k = f ?i}. Again, we could
have included this derivation in the original statement of the lemma:
*};

lemma f_incr[rulify, OF refl]: "\\<forall>i. k = f i \\<longrightarrow> i \\<le> f i";
(*<*)oops;(*>*)

text{*
\begin{exercise}
From the above axiom and lemma for \isa{f} show that \isa{f} is the identity.
\end{exercise}

In general, \isa{induct\_tac} can be applied with any rule \isa{r}
whose conclusion is of the form \isa{?P ?x1 \dots ?xn}, in which case the
format is
\begin{ttbox}
apply(induct_tac y1 ... yn rule: r)
\end{ttbox}\index{*induct_tac}%
where \isa{y1}, \dots, \isa{yn} are variables in the first subgoal.
In fact, \isa{induct\_tac} even allows the conclusion of
\isa{r} to be an (iterated) conjunction of formulae of the above form, in
which case the application is
\begin{ttbox}
apply(induct_tac y1 ... yn and ... and z1 ... zm rule: r)
\end{ttbox}
*};

subsection{*Derivation of new induction schemas*};

text{*\label{sec:derive-ind}
Induction schemas are ordinary theorems and you can derive new ones
whenever you wish.  This section shows you how to, using the example
of \isa{less\_induct}. Assume we only have structural induction
available for @{typ"nat"} and want to derive complete induction. This
requires us to generalize the statement first:
*};

lemma induct_lem: "(\\<And>n::nat. \\<forall>m<n. P m \\<Longrightarrow> P n) ==> \\<forall>m<n. P m";
apply(induct_tac n);

txt{*\noindent
The base case is trivially true. For the induction step (@{term"m <
Suc n"}) we distinguish two cases: @{term"m < n"} is true by induction
hypothesis and @{term"m = n"} follow from the assumption again using
the induction hypothesis:
*};

apply(blast);
(* apply(blast elim:less_SucE); *)
ML"set quick_and_dirty"
sorry;
ML"reset quick_and_dirty"

text{*\noindent
The elimination rule \isa{less_SucE} expresses the case distinction:
\begin{quote}
@{thm[display]"less_SucE"[no_vars]}
\end{quote}

Now it is straightforward to derive the original version of
\isa{less\_induct} by manipulting the conclusion of the above lemma:
instantiate \isa{n} by @{term"Suc n"} and \isa{m} by \isa{n} and
remove the trivial condition @{term"n < Sc n"}. Fortunately, this
happens automatically when we add the lemma as a new premise to the
desired goal:
*};

theorem less_induct: "(\\<And>n::nat. \\<forall>m<n. P m \\<Longrightarrow> P n) ==> P n";
by(insert induct_lem, blast);

text{*\noindent
Finally we should mention that HOL already provides the mother of all
inductions, \emph{wellfounded induction} (\isa{wf\_induct}):
\begin{quote}
@{thm[display]"wf_induct"[no_vars]}
\end{quote}
where @{term"wf r"} means that the relation \isa{r} is wellfounded.
For example \isa{less\_induct} is the special case where \isa{r} is \isa{<} on @{typ"nat"}.
For details see the library.
*};

(*<*)
end
(*>*)
