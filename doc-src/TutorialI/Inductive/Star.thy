(*<*)theory Star = Main:(*>*)

section{*The reflexive transitive closure*}

text{*\label{sec:rtc}
{\bf Say something about inductive relations as opposed to sets? Or has that
been said already? If not, explain induction!}

A perfect example of an inductive definition is the reflexive transitive
closure of a relation. This concept was already introduced in
\S\ref{sec:rtrancl}, but it was not shown how it is defined. In fact,
the operator @{text"^*"} is not defined inductively but via a least
fixed point because at that point in the theory hierarchy
inductive definitions are not yet available. But now they are:
*}

consts rtc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"   ("_*" [1000] 999)
inductive "r*"
intros
rtc_refl[iff]:  "(x,x) \<in> r*"
rtc_step:       "\<lbrakk> (x,y) \<in> r; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

text{*\noindent
The function @{term rtc} is annotated with concrete syntax: instead of
@{text"rtc r"} we can read and write {term"r*"}. The actual definition
consists of two rules. Reflexivity is obvious and is immediately declared an
equivalence rule.  Thus the automatic tools will apply it automatically. The
second rule, @{thm[source]rtc_step}, says that we can always add one more
@{term r}-step to the left. Although we could make @{thm[source]rtc_step} an
introduction rule, this is dangerous: the recursion slows down and may
even kill the automatic tactics.

The above definition of the concept of reflexive transitive closure may
be sufficiently intuitive but it is certainly not the only possible one:
for a start, it does not even mention transitivity explicitly.
The rest of this section is devoted to proving that it is equivalent to
the ``standard'' definition. We start with a simple lemma:
*}

lemma [intro]: "(x,y) : r \<Longrightarrow> (x,y) \<in> r*"
by(blast intro: rtc_step);

text{*\noindent
Although the lemma itself is an unremarkable consequence of the basic rules,
it has the advantage that it can be declared an introduction rule without the
danger of killing the automatic tactics because @{term"r*"} occurs only in
the conclusion and not in the premise. Thus some proofs that would otherwise
need @{thm[source]rtc_step} can now be found automatically. The proof also
shows that @{term blast} is quite able to handle @{thm[source]rtc_step}. But
some of the other automatic tactics are more sensitive, and even @{text
blast} can be lead astray in the presence of large numbers of rules.

Let us now turn to transitivity. It should be a consequence of the definition.
*}

lemma rtc_trans:
  "\<lbrakk> (x,y) \<in> r*; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

txt{*\noindent
The proof starts canonically by rule induction:
*}

apply(erule rtc.induct)(*pr(latex xsymbols symbols);*)(*<*)oops(*>*)
text{*\noindent
However, even the resulting base case is a problem
\begin{isabelle}
\ {\isadigit{1}}{\isachardot}\ {\isasymAnd}x{\isachardot}\ {\isacharparenleft}y{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}\ {\isasymLongrightarrow}\ {\isacharparenleft}x{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}
\end{isabelle}
and maybe not what you had expected. We have to abandon this proof attempt.
To understand what is going on,
let us look at the induction rule @{thm[source]rtc.induct}:
\[ \frac{(x,y) \in r^* \qquad \bigwedge x.~P~x~x \quad \dots}{P~x~y} \]
When applying this rule, $x$ becomes @{term x}, $y$ becomes
@{term y} and $P~x~y$ becomes @{prop"(x,z) : r*"}, thus
yielding the above subgoal. So what went wrong?

When looking at the instantiation of $P~x~y$ we see
that $P$ does not depend on its second parameter at
all. The reason is that in our original goal, of the pair @{term"(x,y)"} only
@{term x} appears also in the conclusion, but not @{term y}. Thus our
induction statement is too weak. Fortunately, it can easily be strengthened:
transfer the additional premise @{prop"(y,z):r*"} into the conclusion:
*}

lemma rtc_trans[rule_format]:
  "(x,y) \<in> r* \<Longrightarrow> (y,z) \<in> r* \<longrightarrow> (x,z) \<in> r*"

txt{*\noindent
This is not an obscure trick but a generally applicable heuristic:
\begin{quote}\em
Whe proving a statement by rule induction on $(x@1,\dots,x@n) \in R$,
pull all other premises containing any of the $x@i$ into the conclusion
using $\longrightarrow$.
\end{quote}
A similar heuristic for other kinds of inductions is formulated in
\S\ref{sec:ind-var-in-prems}. The @{text rule_format} directive turns
@{text"\<longrightarrow>"} back into @{text"\<Longrightarrow>"}. Thus in the end we obtain the original
statement of our lemma.

Now induction produces two subgoals which are both proved automatically:
\begin{isabelle}
\ {\isadigit{1}}{\isachardot}\ {\isasymAnd}x{\isachardot}\ {\isacharparenleft}x{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}\ {\isasymlongrightarrow}\ {\isacharparenleft}x{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymAnd}x\ y\ za{\isachardot}\isanewline
\ \ \ \ \ \ \ {\isasymlbrakk}{\isacharparenleft}x{\isacharcomma}\ y{\isacharparenright}\ {\isasymin}\ r{\isacharsemicolon}\ {\isacharparenleft}y{\isacharcomma}\ za{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}{\isacharsemicolon}\ {\isacharparenleft}za{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}\ {\isasymlongrightarrow}\ {\isacharparenleft}y{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}{\isasymrbrakk}\isanewline
\ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isacharparenleft}za{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}\ {\isasymlongrightarrow}\ {\isacharparenleft}x{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharasterisk}
\end{isabelle}
*}

apply(erule rtc.induct)(*pr(latex xsymbols symbols);*)
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
@{thm[source]rtc2.induct}. Since inductive proofs are hard enough, we should
certainly pick the simplest induction schema available for any concept.
Hence @{term rtc} is the definition of choice.

\begin{exercise}
Show that the converse of @{thm[source]rtc_step} also holds:
@{prop[display]"[| (x,y) : r*; (y,z) : r |] ==> (x,z) : r*"}
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
