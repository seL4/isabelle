(*<*)
theory simp = Main:
(*>*)

section{*Simplification*}

text{*\label{sec:simplification-II}\index{simplification|(}
This section discusses some additional nifty features not covered so far and
gives a short introduction to the simplification process itself. The latter
is helpful to understand why a particular rule does or does not apply in some
situation.
*}

subsection{*Advanced Features*}

subsubsection{*Congruence Rules*}

text{*\label{sec:simp-cong}
It is hardwired into the simplifier that while simplifying the conclusion $Q$
of $P \Imp Q$ it is legal to make uses of the assumption $P$. This
kind of contextual information can also be made available for other
operators. For example, @{prop"xs = [] --> xs@xs = xs"} simplifies to @{term
True} because we may use @{prop"xs = []"} when simplifying @{prop"xs@xs =
xs"}. The generation of contextual information during simplification is
controlled by so-called \bfindex{congruence rules}. This is the one for
@{text"\<longrightarrow>"}:
@{thm[display]imp_cong[no_vars]}
It should be read as follows:
In order to simplify @{prop"P-->Q"} to @{prop"P'-->Q'"},
simplify @{prop P} to @{prop P'}
and assume @{prop"P'"} when simplifying @{prop Q} to @{prop"Q'"}.

Here are some more examples.  The congruence rules for bounded
quantifiers supply contextual information about the bound variable:
@{thm[display,eta_contract=false,margin=60]ball_cong[no_vars]}
The congruence rule for conditional expressions supplies contextual
information for simplifying the @{text then} and @{text else} cases:
@{thm[display]if_cong[no_vars]}
A congruence rule can also \emph{prevent} simplification of some arguments.
Here is an alternative congruence rule for conditional expressions:
@{thm[display]if_weak_cong[no_vars]}
Only the first argument is simplified; the others remain unchanged.
This makes simplification much faster and is faithful to the evaluation
strategy in programming languages, which is why this is the default
congruence rule for @{text if}. Analogous rules control the evaluation of
@{text case} expressions.

You can declare your own congruence rules with the attribute @{text cong},
either globally, in the usual manner,
\begin{quote}
\isacommand{declare} \textit{theorem-name} @{text"[cong]"}
\end{quote}
or locally in a @{text"simp"} call by adding the modifier
\begin{quote}
@{text"cong:"} \textit{list of theorem names}
\end{quote}
The effect is reversed by @{text"cong del"} instead of @{text cong}.

\begin{warn}
The congruence rule @{thm[source]conj_cong}
@{thm[display]conj_cong[no_vars]}
\par\noindent
is occasionally useful but is not a default rule; you have to declare it explicitly.
\end{warn}
*}

subsubsection{*Permutative Rewrite Rules*}

text{*
\index{rewrite rule!permutative|bold}
\index{rewriting!ordered|bold}
\index{ordered rewriting|bold}
\index{simplification!ordered|bold}
An equation is a \bfindex{permutative rewrite rule} if the left-hand
side and right-hand side are the same up to renaming of variables.  The most
common permutative rule is commutativity: @{prop"x+y = y+x"}.  Other examples
include @{prop"(x-y)-z = (x-z)-y"} in arithmetic and @{prop"insert x (insert
y A) = insert y (insert x A)"} for sets. Such rules are problematic because
once they apply, they can be used forever. The simplifier is aware of this
danger and treats permutative rules by means of a special strategy, called
\bfindex{ordered rewriting}: a permutative rewrite
rule is only applied if the term becomes smaller with respect to a fixed
lexicographic ordering on terms. For example, commutativity rewrites
@{term"b+a"} to @{term"a+b"}, but then stops because @{term"a+b"} is strictly
smaller than @{term"b+a"}.  Permutative rewrite rules can be turned into
simplification rules in the usual manner via the @{text simp} attribute; the
simplifier recognizes their special status automatically.

Permutative rewrite rules are most effective in the case of
associative-commutative functions.  (Associativity by itself is not
permutative.)  When dealing with an AC-function~$f$, keep the
following points in mind:
\begin{itemize}\index{associative-commutative function}
  
\item The associative law must always be oriented from left to right,
  namely $f(f(x,y),z) = f(x,f(y,z))$.  The opposite orientation, if
  used with commutativity, can lead to nontermination.

\item To complete your set of rewrite rules, you must add not just
  associativity~(A) and commutativity~(C) but also a derived rule, {\bf
    left-com\-mut\-ativ\-ity} (LC): $f(x,f(y,z)) = f(y,f(x,z))$.
\end{itemize}
Ordered rewriting with the combination of A, C, and LC sorts a term
lexicographically:
\[\def\maps#1{~\stackrel{#1}{\leadsto}~}
 f(f(b,c),a) \maps{A} f(b,f(c,a)) \maps{C} f(b,f(a,c)) \maps{LC} f(a,f(b,c)) \]

Note that ordered rewriting for @{text"+"} and @{text"*"} on numbers is rarely
necessary because the built-in arithmetic prover often succeeds without
such tricks.
*}

subsection{*How it Works*}

text{*\label{sec:SimpHow}
Roughly speaking, the simplifier proceeds bottom-up (subterms are simplified
first) and a conditional equation is only applied if its condition could be
proved (again by simplification). Below we explain some special features of the rewriting process.
*}

subsubsection{*Higher-Order Patterns*}

text{*\index{simplification rule|(}
So far we have pretended the simplifier can deal with arbitrary
rewrite rules. This is not quite true.  Due to efficiency (and
potentially also computability) reasons, the simplifier expects the
left-hand side of each rule to be a so-called \emph{higher-order
pattern}~\cite{nipkow-patterns}\indexbold{higher-order
pattern}\indexbold{pattern, higher-order}. This restricts where
unknowns may occur.  Higher-order patterns are terms in $\beta$-normal
form (this will always be the case unless you have done something
strange) where each occurrence of an unknown is of the form
$\Var{f}~x@1~\dots~x@n$, where the $x@i$ are distinct bound
variables. Thus all ordinary rewrite rules, where all unknowns are
of base type, for example @{thm add_assoc}, are OK: if an unknown is
of base type, it cannot have any arguments. Additionally, the rule
@{text"(\<forall>x. ?P x \<and> ?Q x) = ((\<forall>x. ?P x) \<and> (\<forall>x. ?Q x))"} is also OK, in
both directions: all arguments of the unknowns @{text"?P"} and
@{text"?Q"} are distinct bound variables.

If the left-hand side is not a higher-order pattern, not all is lost
and the simplifier will still try to apply the rule, but only if it
matches \emph{directly}, i.e.\ without much $\lambda$-calculus hocus
pocus. For example, @{text"?f ?x \<in> range ?f = True"} rewrites
@{term"g a \<in> range g"} to @{term True}, but will fail to match
@{text"g(h b) \<in> range(\<lambda>x. g(h x))"}.  However, you can
replace the offending subterms (in our case @{text"?f ?x"}, which
is not a pattern) by adding new variables and conditions: @{text"?y =
?f ?x \<Longrightarrow> ?y \<in> range ?f = True"} is fine
as a conditional rewrite rule since conditions can be arbitrary
terms. However, this trick is not a panacea because the newly
introduced conditions may be hard to solve.
  
There is no restriction on the form of the right-hand
sides.  They may not contain extraneous term or type variables, though.
*}

subsubsection{*The Preprocessor*}

text{*\label{sec:simp-preprocessor}
When a theorem is declared a simplification rule, it need not be a
conditional equation already.  The simplifier will turn it into a set of
conditional equations automatically.  For example, @{prop"f x =
g x & h x = k x"} becomes the two separate
simplification rules @{prop"f x = g x"} and @{prop"h x = k x"}. In
general, the input theorem is converted as follows:
\begin{eqnarray}
\neg P &\mapsto& P = \hbox{\isa{False}} \nonumber\\
P \longrightarrow Q &\mapsto& P \Longrightarrow Q \nonumber\\
P \land Q &\mapsto& P,\ Q \nonumber\\
\forall x.~P~x &\mapsto& P~\Var{x}\nonumber\\
\forall x \in A.\ P~x &\mapsto& \Var{x} \in A \Longrightarrow P~\Var{x} \nonumber\\
@{text if}\ P\ @{text then}\ Q\ @{text else}\ R &\mapsto&
 P \Longrightarrow Q,\ \neg P \Longrightarrow R \nonumber
\end{eqnarray}
Once this conversion process is finished, all remaining non-equations
$P$ are turned into trivial equations $P =\isa{True}$.
For example, the formula 
\begin{center}@{prop"(p \<longrightarrow> t=u \<and> ~r) \<and> s"}\end{center}
is converted into the three rules
\begin{center}
@{prop"p \<Longrightarrow> t = u"},\quad  @{prop"p \<Longrightarrow> r = False"},\quad  @{prop"s = True"}.
\end{center}
\index{simplification rule|)}
\index{simplification|)}
*}
(*<*)
end
(*>*)
