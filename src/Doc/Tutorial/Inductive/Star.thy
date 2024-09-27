(*<*)theory Star imports Main begin(*>*)

section\<open>The Reflexive Transitive Closure\<close>

text\<open>\label{sec:rtc}
\index{reflexive transitive closure!defining inductively|(}%
An inductive definition may accept parameters, so it can express 
functions that yield sets.
Relations too can be defined inductively, since they are just sets of pairs.
A perfect example is the function that maps a relation to its
reflexive transitive closure.  This concept was already
introduced in \S\ref{sec:Relations}, where the operator \<open>\<^sup>*\<close> was
defined as a least fixed point because inductive definitions were not yet
available. But now they are:
\<close>

inductive_set
  rtc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"   ("_*" [1000] 999)
  for r :: "('a \<times> 'a)set"
where
  rtc_refl[iff]:  "(x,x) \<in> r*"
| rtc_step:       "\<lbrakk> (x,y) \<in> r; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

text\<open>\noindent
The function \<^term>\<open>rtc\<close> is annotated with concrete syntax: instead of
\<open>rtc r\<close> we can write \<^term>\<open>r*\<close>. The actual definition
consists of two rules. Reflexivity is obvious and is immediately given the
\<open>iff\<close> attribute to increase automation. The
second rule, @{thm[source]rtc_step}, says that we can always add one more
\<^term>\<open>r\<close>-step to the left. Although we could make @{thm[source]rtc_step} an
introduction rule, this is dangerous: the recursion in the second premise
slows down and may even kill the automatic tactics.

The above definition of the concept of reflexive transitive closure may
be sufficiently intuitive but it is certainly not the only possible one:
for a start, it does not even mention transitivity.
The rest of this section is devoted to proving that it is equivalent to
the standard definition. We start with a simple lemma:
\<close>

lemma [intro]: "(x,y) \<in> r \<Longrightarrow> (x,y) \<in> r*"
by(blast intro: rtc_step)

text\<open>\noindent
Although the lemma itself is an unremarkable consequence of the basic rules,
it has the advantage that it can be declared an introduction rule without the
danger of killing the automatic tactics because \<^term>\<open>r*\<close> occurs only in
the conclusion and not in the premise. Thus some proofs that would otherwise
need @{thm[source]rtc_step} can now be found automatically. The proof also
shows that \<open>blast\<close> is able to handle @{thm[source]rtc_step}. But
some of the other automatic tactics are more sensitive, and even \<open>blast\<close> can be lead astray in the presence of large numbers of rules.

To prove transitivity, we need rule induction, i.e.\ theorem
@{thm[source]rtc.induct}:
@{thm[display]rtc.induct}
It says that \<open>?P\<close> holds for an arbitrary pair @{thm (prem 1) rtc.induct}
if \<open>?P\<close> is preserved by all rules of the inductive definition,
i.e.\ if \<open>?P\<close> holds for the conclusion provided it holds for the
premises. In general, rule induction for an $n$-ary inductive relation $R$
expects a premise of the form $(x@1,\dots,x@n) \in R$.

Now we turn to the inductive proof of transitivity:
\<close>

lemma rtc_trans: "\<lbrakk> (x,y) \<in> r*; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"
apply(erule rtc.induct)

txt\<open>\noindent
Unfortunately, even the base case is a problem:
@{subgoals[display,indent=0,goals_limit=1]}
We have to abandon this proof attempt.
To understand what is going on, let us look again at @{thm[source]rtc.induct}.
In the above application of \<open>erule\<close>, the first premise of
@{thm[source]rtc.induct} is unified with the first suitable assumption, which
is \<^term>\<open>(x,y) \<in> r*\<close> rather than \<^term>\<open>(y,z) \<in> r*\<close>. Although that
is what we want, it is merely due to the order in which the assumptions occur
in the subgoal, which it is not good practice to rely on. As a result,
\<open>?xb\<close> becomes \<^term>\<open>x\<close>, \<open>?xa\<close> becomes
\<^term>\<open>y\<close> and \<open>?P\<close> becomes \<^term>\<open>\<lambda>u v. (u,z) \<in> r*\<close>, thus
yielding the above subgoal. So what went wrong?

When looking at the instantiation of \<open>?P\<close> we see that it does not
depend on its second parameter at all. The reason is that in our original
goal, of the pair \<^term>\<open>(x,y)\<close> only \<^term>\<open>x\<close> appears also in the
conclusion, but not \<^term>\<open>y\<close>. Thus our induction statement is too
general. Fortunately, it can easily be specialized:
transfer the additional premise \<^prop>\<open>(y,z)\<in>r*\<close> into the conclusion:\<close>
(*<*)oops(*>*)
lemma rtc_trans[rule_format]:
  "(x,y) \<in> r* \<Longrightarrow> (y,z) \<in> r* \<longrightarrow> (x,z) \<in> r*"

txt\<open>\noindent
This is not an obscure trick but a generally applicable heuristic:
\begin{quote}\em
When proving a statement by rule induction on $(x@1,\dots,x@n) \in R$,
pull all other premises containing any of the $x@i$ into the conclusion
using $\longrightarrow$.
\end{quote}
A similar heuristic for other kinds of inductions is formulated in
\S\ref{sec:ind-var-in-prems}. The \<open>rule_format\<close> directive turns
\<open>\<longrightarrow>\<close> back into \<open>\<Longrightarrow>\<close>: in the end we obtain the original
statement of our lemma.
\<close>

apply(erule rtc.induct)

txt\<open>\noindent
Now induction produces two subgoals which are both proved automatically:
@{subgoals[display,indent=0]}
\<close>

 apply(blast)
apply(blast intro: rtc_step)
done

text\<open>
Let us now prove that \<^term>\<open>r*\<close> is really the reflexive transitive closure
of \<^term>\<open>r\<close>, i.e.\ the least reflexive and transitive
relation containing \<^term>\<open>r\<close>. The latter is easily formalized
\<close>

inductive_set
  rtc2 :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"
  for r :: "('a \<times> 'a)set"
where
  "(x,y) \<in> r \<Longrightarrow> (x,y) \<in> rtc2 r"
| "(x,x) \<in> rtc2 r"
| "\<lbrakk> (x,y) \<in> rtc2 r; (y,z) \<in> rtc2 r \<rbrakk> \<Longrightarrow> (x,z) \<in> rtc2 r"

text\<open>\noindent
and the equivalence of the two definitions is easily shown by the obvious rule
inductions:
\<close>

lemma "(x,y) \<in> rtc2 r \<Longrightarrow> (x,y) \<in> r*"
apply(erule rtc2.induct)
  apply(blast)
 apply(blast)
apply(blast intro: rtc_trans)
done

lemma "(x,y) \<in> r* \<Longrightarrow> (x,y) \<in> rtc2 r"
apply(erule rtc.induct)
 apply(blast intro: rtc2.intros)
apply(blast intro: rtc2.intros)
done

text\<open>
So why did we start with the first definition? Because it is simpler. It
contains only two rules, and the single step rule is simpler than
transitivity.  As a consequence, @{thm[source]rtc.induct} is simpler than
@{thm[source]rtc2.induct}. Since inductive proofs are hard enough
anyway, we should always pick the simplest induction schema available.
Hence \<^term>\<open>rtc\<close> is the definition of choice.
\index{reflexive transitive closure!defining inductively|)}

\begin{exercise}\label{ex:converse-rtc-step}
Show that the converse of @{thm[source]rtc_step} also holds:
@{prop[display]"[| (x,y) \<in> r*; (y,z) \<in> r |] ==> (x,z) \<in> r*"}
\end{exercise}
\begin{exercise}
Repeat the development of this section, but starting with a definition of
\<^term>\<open>rtc\<close> where @{thm[source]rtc_step} is replaced by its converse as shown
in exercise~\ref{ex:converse-rtc-step}.
\end{exercise}
\<close>
(*<*)
lemma rtc_step2[rule_format]: "(x,y) \<in> r* \<Longrightarrow> (y,z) \<in> r \<longrightarrow> (x,z) \<in> r*"
apply(erule rtc.induct)
 apply blast
apply(blast intro: rtc_step)
done

end
(*>*)
