(*<*)theory Star = Main:(*>*)

section{*The Reflexive Transitive Closure*}

text{*\label{sec:rtc}
An inductive definition may accept parameters, so it can express 
functions that yield sets.
Relations too can be defined inductively, since they are just sets of pairs.
A perfect example is the function that maps a relation to its
reflexive transitive closure.  This concept was already
introduced in \S\ref{sec:Relations}, where the operator @{text"\<^sup>*"} was
defined as a least fixed point because inductive definitions were not yet
available. But now they are:
*}

consts rtc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"   ("_*" [1000] 999)
inductive "r*"
intros
rtc_refl[iff]:  "(x,x) \<in> r*"
rtc_step:       "\<lbrakk> (x,y) \<in> r; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

text{*\noindent
The function @{term rtc} is annotated with concrete syntax: instead of
@{text"rtc r"} we can read and write @{term"r*"}. The actual definition
consists of two rules. Reflexivity is obvious and is immediately given the
@{text iff} attribute to increase automation. The
second rule, @{thm[source]rtc_step}, says that we can always add one more
@{term r}-step to the left. Although we could make @{thm[source]rtc_step} an
introduction rule, this is dangerous: the recursion in the second premise
slows down and may even kill the automatic tactics.

The above definition of the concept of reflexive transitive closure may
be sufficiently intuitive but it is certainly not the only possible one:
for a start, it does not even mention transitivity.
The rest of this section is devoted to proving that it is equivalent to
the standard definition. We start with a simple lemma:
*}

lemma [intro]: "(x,y) : r \<Longrightarrow> (x,y) \<in> r*"
by(blast intro: rtc_step);

text{*\noindent
Although the lemma itself is an unremarkable consequence of the basic rules,
it has the advantage that it can be declared an introduction rule without the
danger of killing the automatic tactics because @{term"r*"} occurs only in
the conclusion and not in the premise. Thus some proofs that would otherwise
need @{thm[source]rtc_step} can now be found automatically. The proof also
shows that @{text blast} is able to handle @{thm[source]rtc_step}. But
some of the other automatic tactics are more sensitive, and even @{text
blast} can be lead astray in the presence of large numbers of rules.

To prove transitivity, we need rule induction, i.e.\ theorem
@{thm[source]rtc.induct}:
@{thm[display]rtc.induct}
It says that @{text"?P"} holds for an arbitrary pair @{text"(?xb,?xa) \<in>
?r*"} if @{text"?P"} is preserved by all rules of the inductive definition,
i.e.\ if @{text"?P"} holds for the conclusion provided it holds for the
premises. In general, rule induction for an $n$-ary inductive relation $R$
expects a premise of the form $(x@1,\dots,x@n) \in R$.

Now we turn to the inductive proof of transitivity:
*}

lemma rtc_trans: "\<lbrakk> (x,y) \<in> r*; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"
apply(erule rtc.induct)

txt{*\noindent
Unfortunately, even the resulting base case is a problem
@{subgoals[display,indent=0,goals_limit=1]}
and maybe not what you had expected. We have to abandon this proof attempt.
To understand what is going on, let us look again at @{thm[source]rtc.induct}.
In the above application of @{text erule}, the first premise of
@{thm[source]rtc.induct} is unified with the first suitable assumption, which
is @{term"(x,y) \<in> r*"} rather than @{term"(y,z) \<in> r*"}. Although that
is what we want, it is merely due to the order in which the assumptions occur
in the subgoal, which it is not good practice to rely on. As a result,
@{text"?xb"} becomes @{term x}, @{text"?xa"} becomes
@{term y} and @{text"?P"} becomes @{term"%u v. (u,z) : r*"}, thus
yielding the above subgoal. So what went wrong?

When looking at the instantiation of @{text"?P"} we see that it does not
depend on its second parameter at all. The reason is that in our original
goal, of the pair @{term"(x,y)"} only @{term x} appears also in the
conclusion, but not @{term y}. Thus our induction statement is too
weak. Fortunately, it can easily be strengthened:
transfer the additional premise @{prop"(y,z):r*"} into the conclusion:*}
(*<*)oops(*>*)
lemma rtc_trans[rule_format]:
  "(x,y) \<in> r* \<Longrightarrow> (y,z) \<in> r* \<longrightarrow> (x,z) \<in> r*"

txt{*\noindent
This is not an obscure trick but a generally applicable heuristic:
\begin{quote}\em
When proving a statement by rule induction on $(x@1,\dots,x@n) \in R$,
pull all other premises containing any of the $x@i$ into the conclusion
using $\longrightarrow$.
\end{quote}
A similar heuristic for other kinds of inductions is formulated in
\S\ref{sec:ind-var-in-prems}. The @{text rule_format} directive turns
@{text"\<longrightarrow>"} back into @{text"\<Longrightarrow>"}: in the end we obtain the original
statement of our lemma.
*}

apply(erule rtc.induct)

txt{*\noindent
Now induction produces two subgoals which are both proved automatically:
@{subgoals[display,indent=0]}
*}

 apply(blast);
apply(blast intro: rtc_step);
done

text{*
Let us now prove that @{term"r*"} is really the reflexive transitive closure
of @{term r}, i.e.\ the least reflexive and transitive
relation containing @{term r}. The latter is easily formalized
*}

consts rtc2 :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"
inductive "rtc2 r"
intros
"(x,y) \<in> r \<Longrightarrow> (x,y) \<in> rtc2 r"
"(x,x) \<in> rtc2 r"
"\<lbrakk> (x,y) \<in> rtc2 r; (y,z) \<in> rtc2 r \<rbrakk> \<Longrightarrow> (x,z) \<in> rtc2 r"

text{*\noindent
and the equivalence of the two definitions is easily shown by the obvious rule
inductions:
*}

lemma "(x,y) \<in> rtc2 r \<Longrightarrow> (x,y) \<in> r*"
apply(erule rtc2.induct);
  apply(blast);
 apply(blast);
apply(blast intro: rtc_trans);
done

lemma "(x,y) \<in> r* \<Longrightarrow> (x,y) \<in> rtc2 r"
apply(erule rtc.induct);
 apply(blast intro: rtc2.intros);
apply(blast intro: rtc2.intros);
done

text{*
So why did we start with the first definition? Because it is simpler. It
contains only two rules, and the single step rule is simpler than
transitivity.  As a consequence, @{thm[source]rtc.induct} is simpler than
@{thm[source]rtc2.induct}. Since inductive proofs are hard enough
anyway, we should always pick the simplest induction schema available.
Hence @{term rtc} is the definition of choice.

\begin{exercise}\label{ex:converse-rtc-step}
Show that the converse of @{thm[source]rtc_step} also holds:
@{prop[display]"[| (x,y) : r*; (y,z) : r |] ==> (x,z) : r*"}
\end{exercise}
\begin{exercise}
Repeat the development of this section, but starting with a definition of
@{term rtc} where @{thm[source]rtc_step} is replaced by its converse as shown
in exercise~\ref{ex:converse-rtc-step}.
\end{exercise}
*}
(*<*)
lemma rtc_step2[rule_format]: "(x,y) : r* \<Longrightarrow> (y,z) : r --> (x,z) : r*"
apply(erule rtc.induct);
 apply blast;
apply(blast intro:rtc_step)
done

end
(*>*)
