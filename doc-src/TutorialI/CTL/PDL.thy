(*<*)theory PDL = Base:(*>*)

subsection{*Propositional dynamic logic---PDL*}

text{*\index{PDL|(}
The formulae of PDL are built up from atomic propositions via the customary
propositional connectives of negation and conjunction and the two temporal
connectives @{text AX} and @{text EF}. Since formulae are essentially
(syntax) trees, they are naturally modelled as a datatype:
*}

datatype formula = Atom atom
                  | Neg formula
                  | And formula formula
                  | AX formula
                  | EF formula

text{*\noindent
This is almost the same as in the boolean expression case study in
\S\ref{sec:boolex}, except that what used to be called @{text Var} is now
called @{term Atom}.

The meaning of these formulae is given by saying which formula is true in
which state:
*}

consts valid :: "state \<Rightarrow> formula \<Rightarrow> bool"   ("(_ \<Turnstile> _)" [80,80] 80)

text{*\noindent
The concrete syntax annotation allows us to write @{term"s \<Turnstile> f"} instead of
@{text"valid s f"}.

The definition of @{text"\<Turnstile>"} is by recursion over the syntax:
*}

primrec
"s \<Turnstile> Atom a  = (a \<in> L s)"
"s \<Turnstile> Neg f   = (\<not>(s \<Turnstile> f))"
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)"
"s \<Turnstile> AX f    = (\<forall>t. (s,t) \<in> M \<longrightarrow> t \<Turnstile> f)"
"s \<Turnstile> EF f    = (\<exists>t. (s,t) \<in> M^* \<and> t \<Turnstile> f)";

text{*\noindent
The first three equations should be self-explanatory. The temporal formula
@{term"AX f"} means that @{term f} is true in all next states whereas
@{term"EF f"} means that there exists some future state in which @{term f} is
true. The future is expressed via @{text"^*"}, the transitive reflexive
closure. Because of reflexivity, the future includes the present.

Now we come to the model checker itself. It maps a formula into the set of
states where the formula is true and is defined by recursion over the syntax,
too:
*}

consts mc :: "formula \<Rightarrow> state set";
primrec
"mc(Atom a)  = {s. a \<in> L s}"
"mc(Neg f)   = -mc f"
"mc(And f g) = mc f \<inter> mc g"
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}"
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> M^-1 ^^ T)"

text{*\noindent
Only the equation for @{term EF} deserves some comments. Remember that the
postfix @{text"^-1"} and the infix @{text"^^"} are predefined and denote the
converse of a relation and the application of a relation to a set. Thus
@{term "M^-1 ^^ T"} is the set of all predecessors of @{term T} and the least
fixpoint (@{term lfp}) of @{term"\<lambda>T. mc f \<union> M^-1 ^^ T"} is the least set
@{term T} containing @{term"mc f"} and all predecessors of @{term T}. If you
find it hard to see that @{term"mc(EF f)"} contains exactly those states from
which there is a path to a state where @{term f} is true, do not worry---that
will be proved in a moment.

First we prove monotonicity of the function inside @{term lfp}
*}

lemma mono_ef: "mono(\<lambda>T. A \<union> M^-1 ^^ T)"
apply(rule monoI)
apply blast
done

text{*\noindent
in order to make sure it really has a least fixpoint.

Now we can relate model checking and semantics. For the @{text EF} case we need
a separate lemma:
*}

lemma EF_lemma:
  "lfp(\<lambda>T. A \<union> M^-1 ^^ T) = {s. \<exists>t. (s,t) \<in> M^* \<and> t \<in> A}"

txt{*\noindent
The equality is proved in the canonical fashion by proving that each set
contains the other; the containment is shown pointwise:
*}

apply(rule equalityI);
 apply(rule subsetI);
 apply(simp)
(*pr(latex xsymbols symbols);*)
txt{*\noindent
Simplification leaves us with the following first subgoal
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}s{\isachardot}\ s\ {\isasymin}\ lfp\ {\isacharparenleft}{\isasymlambda}T{\isachardot}\ A\ {\isasymunion}\ M{\isacharcircum}{\isacharminus}\isadigit{1}\ {\isacharcircum}{\isacharcircum}\ T{\isacharparenright}\ {\isasymLongrightarrow}\ {\isasymexists}t{\isachardot}\ {\isacharparenleft}s{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M{\isacharcircum}{\isacharasterisk}\ {\isasymand}\ t\ {\isasymin}\ A
\end{isabelle}
which is proved by @{term lfp}-induction:
*}

 apply(erule Lfp.induct)
  apply(rule mono_ef)
 apply(simp)
(*pr(latex xsymbols symbols);*)
txt{*\noindent
Having disposed of the monotonicity subgoal,
simplification leaves us with the following main goal
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}s{\isachardot}\ s\ {\isasymin}\ A\ {\isasymor}\isanewline
\ \ \ \ \ \ \ \ \ s\ {\isasymin}\ M{\isacharcircum}{\isacharminus}\isadigit{1}\ {\isacharcircum}{\isacharcircum}\ {\isacharparenleft}lfp\ {\isacharparenleft}{\dots}{\isacharparenright}\ {\isasyminter}\ {\isacharbraceleft}x{\isachardot}\ {\isasymexists}t{\isachardot}\ {\isacharparenleft}x{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M{\isacharcircum}{\isacharasterisk}\ {\isasymand}\ t\ {\isasymin}\ A{\isacharbraceright}{\isacharparenright}\isanewline
\ \ \ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isasymexists}t{\isachardot}\ {\isacharparenleft}s{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M{\isacharcircum}{\isacharasterisk}\ {\isasymand}\ t\ {\isasymin}\ A
\end{isabelle}
which is proved by @{text blast} with the help of a few lemmas about
@{text"^*"}:
*}

 apply(blast intro: r_into_rtrancl rtrancl_trans);

txt{*
We now return to the second set containment subgoal, which is again proved
pointwise:
*}

apply(rule subsetI)
apply(simp, clarify)
(*pr(latex xsymbols symbols);*)
txt{*\noindent
After simplification and clarification we are left with
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}s\ t{\isachardot}\ {\isasymlbrakk}{\isacharparenleft}s{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M{\isacharcircum}{\isacharasterisk}{\isacharsemicolon}\ t\ {\isasymin}\ A{\isasymrbrakk}\ {\isasymLongrightarrow}\ s\ {\isasymin}\ lfp\ {\isacharparenleft}{\isasymlambda}T{\isachardot}\ A\ {\isasymunion}\ M{\isacharcircum}{\isacharminus}\isadigit{1}\ {\isacharcircum}{\isacharcircum}\ T{\isacharparenright}
\end{isabelle}
This goal is proved by induction on @{term"(s,t)\<in>M^*"}. But since the model
checker works backwards (from @{term t} to @{term s}), we cannot use the
induction theorem @{thm[source]rtrancl_induct} because it works in the
forward direction. Fortunately the converse induction theorem
@{thm[source]converse_rtrancl_induct} already exists:
@{thm[display,margin=60]converse_rtrancl_induct[no_vars]}
It says that if @{prop"(a,b):r^*"} and we know @{prop"P b"} then we can infer
@{prop"P a"} provided each step backwards from a predecessor @{term z} of
@{term b} preserves @{term P}.
*}

apply(erule converse_rtrancl_induct)
(*pr(latex xsymbols symbols);*)
txt{*\noindent
The base case
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}t{\isachardot}\ t\ {\isasymin}\ A\ {\isasymLongrightarrow}\ t\ {\isasymin}\ lfp\ {\isacharparenleft}{\isasymlambda}T{\isachardot}\ A\ {\isasymunion}\ M{\isacharcircum}{\isacharminus}\isadigit{1}\ {\isacharcircum}{\isacharcircum}\ T{\isacharparenright}
\end{isabelle}
is solved by unrolling @{term lfp} once
*}

 apply(rule ssubst[OF lfp_unfold[OF mono_ef]])
(*pr(latex xsymbols symbols);*)
txt{*
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}t{\isachardot}\ t\ {\isasymin}\ A\ {\isasymLongrightarrow}\ t\ {\isasymin}\ A\ {\isasymunion}\ M{\isacharcircum}{\isacharminus}\isadigit{1}\ {\isacharcircum}{\isacharcircum}\ lfp\ {\isacharparenleft}{\isasymlambda}T{\isachardot}\ A\ {\isasymunion}\ M{\isacharcircum}{\isacharminus}\isadigit{1}\ {\isacharcircum}{\isacharcircum}\ T{\isacharparenright}
\end{isabelle}
and disposing of the resulting trivial subgoal automatically:
*}

 apply(blast)

txt{*\noindent
The proof of the induction step is identical to the one for the base case:
*}

apply(rule ssubst[OF lfp_unfold[OF mono_ef]])
apply(blast)
done

text{*
The main theorem is proved in the familiar manner: induction followed by
@{text auto} augmented with the lemma as a simplification rule.
*}

theorem "mc f = {s. s \<Turnstile> f}";
apply(induct_tac f);
apply(auto simp add:EF_lemma);
done;

text{*
\begin{exercise}
@{term AX} has a dual operator @{term EN}\footnote{We cannot use the customary @{text EX}
as that is the ASCII equivalent of @{text"\<exists>"}}
(``there exists a next state such that'') with the intended semantics
@{prop[display]"(s \<Turnstile> EN f) = (EX t. (s,t) : M & t \<Turnstile> f)"}
Fortunately, @{term"EN f"} can already be expressed as a PDL formula. How?

Show that the semantics for @{term EF} satisfies the following recursion equation:
@{prop[display]"(s \<Turnstile> EF f) = (s \<Turnstile> f | s \<Turnstile> EN(EF f))"}
\end{exercise}
\index{PDL|)}
*}
(*<*)
theorem main: "mc f = {s. s \<Turnstile> f}";
apply(induct_tac f);
apply(auto simp add:EF_lemma);
done;

lemma aux: "s \<Turnstile> f = (s : mc f)";
apply(simp add:main);
done;

lemma "(s \<Turnstile> EF f) = (s \<Turnstile> f | s \<Turnstile> Neg(AX(Neg(EF f))))";
apply(simp only:aux);
apply(simp);
apply(rule ssubst[OF lfp_unfold[OF mono_ef]], fast);
done

end
(*>*)
