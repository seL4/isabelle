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

subsection{*Advanced features*}

subsubsection{*Congruence rules*}

text{*\label{sec:simp-cong}
It is hardwired into the simplifier that while simplifying the conclusion $Q$
of $P \isasymImp Q$ it is legal to make uses of the assumptions $P$. This
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
The congruence rule for conditional expressions supply contextual
information for simplifying the arms:
@{thm[display]if_cong[no_vars]}
A congruence rule can also \emph{prevent} simplification of some arguments.
Here is an alternative congruence rule for conditional expressions:
@{thm[display]if_weak_cong[no_vars]}
Only the first argument is simplified; the others remain unchanged.
This makes simplification much faster and is faithful to the evaluation
strategy in programming languages, which is why this is the default
congruence rule for @{text if}. Analogous rules control the evaluaton of
@{text case} expressions.

You can delare your own congruence rules with the attribute @{text cong},
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
is occasionally useful but not a default rule; you have to use it explicitly.
\end{warn}
*}

subsubsection{*Permutative rewrite rules*}

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
rule is only applied if the term becomes ``smaller'' (w.r.t.\ some fixed
lexicographic ordering on terms). For example, commutativity rewrites
@{term"b+a"} to @{term"a+b"}, but then stops because @{term"a+b"} is strictly
smaller than @{term"b+a"}.  Permutative rewrite rules can be turned into
simplification rules in the usual manner via the @{text simp} attribute; the
simplifier recognizes their special status automatically.

Permutative rewrite rules are most effective in the case of
associative-commutative operators.  (Associativity by itself is not
permutative.)  When dealing with an AC-operator~$f$, keep the
following points in mind:
\begin{itemize}\index{associative-commutative operators}
  
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
necessary because the builtin arithmetic capabilities often take care of
this.
*}

subsection{*How it works*}

text{*\label{sec:SimpHow}
Roughly speaking, the simplifier proceeds bottom-up (subterms are simplified
first) and a conditional equation is only applied if its condition could be
proved (again by simplification). Below we explain some special 
*}

subsubsection{*Higher-order patterns*}

subsubsection{*Local assumptions*}

subsubsection{*The preprocessor*}

text{*
\index{simplification|)}
*}
(*<*)
end
(*>*)
