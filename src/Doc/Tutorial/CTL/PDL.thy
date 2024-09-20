(*<*)theory PDL imports Base begin(*>*)

subsection\<open>Propositional Dynamic Logic --- PDL\<close>

text\<open>\index{PDL|(}
The formulae of PDL are built up from atomic propositions via
negation and conjunction and the two temporal
connectives \<open>AX\<close> and \<open>EF\<close>\@. Since formulae are essentially
syntax trees, they are naturally modelled as a datatype:%
\footnote{The customary definition of PDL
\<^cite>\<open>"HarelKT-DL"\<close> looks quite different from ours, but the two are easily
shown to be equivalent.}
\<close>

datatype formula = Atom "atom"
                  | Neg formula
                  | And formula formula
                  | AX formula
                  | EF formula

text\<open>\noindent
This resembles the boolean expression case study in
\S\ref{sec:boolex}.
A validity relation between states and formulae specifies the semantics.
The syntax annotation allows us to write \<open>s \<Turnstile> f\<close> instead of
\hbox{\<open>valid s f\<close>}. The definition is by recursion over the syntax:
\<close>

primrec valid :: "state \<Rightarrow> formula \<Rightarrow> bool"   (\<open>(_ \<Turnstile> _)\<close> [80,80] 80)
where
"s \<Turnstile> Atom a  = (a \<in> L s)" |
"s \<Turnstile> Neg f   = (\<not>(s \<Turnstile> f))" |
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)" |
"s \<Turnstile> AX f    = (\<forall>t. (s,t) \<in> M \<longrightarrow> t \<Turnstile> f)" |
"s \<Turnstile> EF f    = (\<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<Turnstile> f)"

text\<open>\noindent
The first three equations should be self-explanatory. The temporal formula
\<^term>\<open>AX f\<close> means that \<^term>\<open>f\<close> is true in \emph{A}ll ne\emph{X}t states whereas
\<^term>\<open>EF f\<close> means that there \emph{E}xists some \emph{F}uture state in which \<^term>\<open>f\<close> is
true. The future is expressed via \<open>\<^sup>*\<close>, the reflexive transitive
closure. Because of reflexivity, the future includes the present.

Now we come to the model checker itself. It maps a formula into the
set of states where the formula is true.  It too is defined by
recursion over the syntax:\<close>

primrec mc :: "formula \<Rightarrow> state set" where
"mc(Atom a)  = {s. a \<in> L s}" |
"mc(Neg f)   = -mc f" |
"mc(And f g) = mc f \<inter> mc g" |
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}" |
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> (M\<inverse> `` T))"

text\<open>\noindent
Only the equation for \<^term>\<open>EF\<close> deserves some comments. Remember that the
postfix \<open>\<inverse>\<close> and the infix \<open>``\<close> are predefined and denote the
converse of a relation and the image of a set under a relation.  Thus
\<^term>\<open>M\<inverse> `` T\<close> is the set of all predecessors of \<^term>\<open>T\<close> and the least
fixed point (\<^term>\<open>lfp\<close>) of \<^term>\<open>\<lambda>T. mc f \<union> M\<inverse> `` T\<close> is the least set
\<^term>\<open>T\<close> containing \<^term>\<open>mc f\<close> and all predecessors of \<^term>\<open>T\<close>. If you
find it hard to see that \<^term>\<open>mc(EF f)\<close> contains exactly those states from
which there is a path to a state where \<^term>\<open>f\<close> is true, do not worry --- this
will be proved in a moment.

First we prove monotonicity of the function inside \<^term>\<open>lfp\<close>
in order to make sure it really has a least fixed point.
\<close>

lemma mono_ef: "mono(\<lambda>T. A \<union> (M\<inverse> `` T))"
apply(rule monoI)
apply blast
done

text\<open>\noindent
Now we can relate model checking and semantics. For the \<open>EF\<close> case we need
a separate lemma:
\<close>

lemma EF_lemma:
  "lfp(\<lambda>T. A \<union> (M\<inverse> `` T)) = {s. \<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<in> A}"

txt\<open>\noindent
The equality is proved in the canonical fashion by proving that each set
includes the other; the inclusion is shown pointwise:
\<close>

apply(rule equalityI)
 apply(rule subsetI)
 apply(simp)(*<*)apply(rename_tac s)(*>*)

txt\<open>\noindent
Simplification leaves us with the following first subgoal
@{subgoals[display,indent=0,goals_limit=1]}
which is proved by \<^term>\<open>lfp\<close>-induction:
\<close>

 apply(erule lfp_induct_set)
  apply(rule mono_ef)
 apply(simp)
txt\<open>\noindent
Having disposed of the monotonicity subgoal,
simplification leaves us with the following goal:
\begin{isabelle}
\ {\isadigit{1}}{\isachardot}\ {\isasymAnd}x{\isachardot}\ x\ {\isasymin}\ A\ {\isasymor}\isanewline
\ \ \ \ \ \ \ \ \ x\ {\isasymin}\ M{\isasyminverse}\ {\isacharbackquote}{\isacharbackquote}\ {\isacharparenleft}lfp\ {\isacharparenleft}\dots{\isacharparenright}\ {\isasyminter}\ {\isacharbraceleft}x{\isachardot}\ {\isasymexists}t{\isachardot}\ {\isacharparenleft}x{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\isactrlsup {\isacharasterisk}\ {\isasymand}\ t\ {\isasymin}\ A{\isacharbraceright}{\isacharparenright}\isanewline
\ \ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isasymexists}t{\isachardot}\ {\isacharparenleft}x{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\isactrlsup {\isacharasterisk}\ {\isasymand}\ t\ {\isasymin}\ A
\end{isabelle}
It is proved by \<open>blast\<close>, using the transitivity of 
\isa{M\isactrlsup {\isacharasterisk}}.
\<close>

 apply(blast intro: rtrancl_trans)

txt\<open>
We now return to the second set inclusion subgoal, which is again proved
pointwise:
\<close>

apply(rule subsetI)
apply(simp, clarify)

txt\<open>\noindent
After simplification and clarification we are left with
@{subgoals[display,indent=0,goals_limit=1]}
This goal is proved by induction on \<^term>\<open>(s,t)\<in>M\<^sup>*\<close>. But since the model
checker works backwards (from \<^term>\<open>t\<close> to \<^term>\<open>s\<close>), we cannot use the
induction theorem @{thm[source]rtrancl_induct}: it works in the
forward direction. Fortunately the converse induction theorem
@{thm[source]converse_rtrancl_induct} already exists:
@{thm[display,margin=60]converse_rtrancl_induct[no_vars]}
It says that if \<^prop>\<open>(a,b)\<in>r\<^sup>*\<close> and we know \<^prop>\<open>P b\<close> then we can infer
\<^prop>\<open>P a\<close> provided each step backwards from a predecessor \<^term>\<open>z\<close> of
\<^term>\<open>b\<close> preserves \<^term>\<open>P\<close>.
\<close>

apply(erule converse_rtrancl_induct)

txt\<open>\noindent
The base case
@{subgoals[display,indent=0,goals_limit=1]}
is solved by unrolling \<^term>\<open>lfp\<close> once
\<close>

 apply(subst lfp_unfold[OF mono_ef])

txt\<open>
@{subgoals[display,indent=0,goals_limit=1]}
and disposing of the resulting trivial subgoal automatically:
\<close>

 apply(blast)

txt\<open>\noindent
The proof of the induction step is identical to the one for the base case:
\<close>

apply(subst lfp_unfold[OF mono_ef])
apply(blast)
done

text\<open>
The main theorem is proved in the familiar manner: induction followed by
\<open>auto\<close> augmented with the lemma as a simplification rule.
\<close>

theorem "mc f = {s. s \<Turnstile> f}"
apply(induct_tac f)
apply(auto simp add: EF_lemma)
done

text\<open>
\begin{exercise}
\<^term>\<open>AX\<close> has a dual operator \<^term>\<open>EN\<close> 
(``there exists a next state such that'')%
\footnote{We cannot use the customary \<open>EX\<close>: it is reserved
as the \textsc{ascii}-equivalent of \<open>\<exists>\<close>.}
with the intended semantics
@{prop[display]"(s \<Turnstile> EN f) = (\<exists>t. (s,t) \<in> M \<and> t \<Turnstile> f)"}
Fortunately, \<^term>\<open>EN f\<close> can already be expressed as a PDL formula. How?

Show that the semantics for \<^term>\<open>EF\<close> satisfies the following recursion equation:
@{prop[display]"(s \<Turnstile> EF f) = (s \<Turnstile> f | s \<Turnstile> EN(EF f))"}
\end{exercise}
\index{PDL|)}
\<close>
(*<*)
theorem main: "mc f = {s. s \<Turnstile> f}"
apply(induct_tac f)
apply(auto simp add: EF_lemma)
done

lemma aux: "s \<Turnstile> f = (s \<in> mc f)"
apply(simp add: main)
done

lemma "(s \<Turnstile> EF f) = (s \<Turnstile> f | s \<Turnstile> Neg(AX(Neg(EF f))))"
apply(simp only: aux)
apply(simp)
apply(subst lfp_unfold[OF mono_ef], fast)
done

end
(*>*)
