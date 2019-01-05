(*<*)
theory simp2 imports Main begin
(*>*)

section\<open>Simplification\<close>

text\<open>\label{sec:simplification-II}\index{simplification|(}
This section describes features not covered until now.  It also
outlines the simplification process itself, which can be helpful
when the simplifier does not do what you expect of it.
\<close>

subsection\<open>Advanced Features\<close>

subsubsection\<open>Congruence Rules\<close>

text\<open>\label{sec:simp-cong}
While simplifying the conclusion $Q$
of $P \Imp Q$, it is legal to use the assumption $P$.
For $\Imp$ this policy is hardwired, but 
contextual information can also be made available for other
operators. For example, \<^prop>\<open>xs = [] --> xs@xs = xs\<close> simplifies to \<^term>\<open>True\<close> because we may use \<^prop>\<open>xs = []\<close> when simplifying \<^prop>\<open>xs@xs =
xs\<close>. The generation of contextual information during simplification is
controlled by so-called \bfindex{congruence rules}. This is the one for
\<open>\<longrightarrow>\<close>:
@{thm[display]imp_cong[no_vars]}
It should be read as follows:
In order to simplify \<^prop>\<open>P-->Q\<close> to \<^prop>\<open>P'-->Q'\<close>,
simplify \<^prop>\<open>P\<close> to \<^prop>\<open>P'\<close>
and assume \<^prop>\<open>P'\<close> when simplifying \<^prop>\<open>Q\<close> to \<^prop>\<open>Q'\<close>.

Here are some more examples.  The congruence rules for bounded
quantifiers supply contextual information about the bound variable:
@{thm[display,eta_contract=false,margin=60]ball_cong[no_vars]}
One congruence rule for conditional expressions supplies contextual
information for simplifying the \<open>then\<close> and \<open>else\<close> cases:
@{thm[display]if_cong[no_vars]}
An alternative congruence rule for conditional expressions
actually \emph{prevents} simplification of some arguments:
@{thm[display]if_weak_cong[no_vars]}
Only the first argument is simplified; the others remain unchanged.
This makes simplification much faster and is faithful to the evaluation
strategy in programming languages, which is why this is the default
congruence rule for \<open>if\<close>. Analogous rules control the evaluation of
\<open>case\<close> expressions.

You can declare your own congruence rules with the attribute \attrdx{cong},
either globally, in the usual manner,
\begin{quote}
\isacommand{declare} \textit{theorem-name} \<open>[cong]\<close>
\end{quote}
or locally in a \<open>simp\<close> call by adding the modifier
\begin{quote}
\<open>cong:\<close> \textit{list of theorem names}
\end{quote}
The effect is reversed by \<open>cong del\<close> instead of \<open>cong\<close>.

\begin{warn}
The congruence rule @{thm[source]conj_cong}
@{thm[display]conj_cong[no_vars]}
\par\noindent
is occasionally useful but is not a default rule; you have to declare it explicitly.
\end{warn}
\<close>

subsubsection\<open>Permutative Rewrite Rules\<close>

text\<open>
\index{rewrite rules!permutative|bold}%
An equation is a \textbf{permutative rewrite rule} if the left-hand
side and right-hand side are the same up to renaming of variables.  The most
common permutative rule is commutativity: \<^prop>\<open>x+y = y+x\<close>.  Other examples
include \<^prop>\<open>(x-y)-z = (x-z)-y\<close> in arithmetic and \<^prop>\<open>insert x (insert
y A) = insert y (insert x A)\<close> for sets. Such rules are problematic because
once they apply, they can be used forever. The simplifier is aware of this
danger and treats permutative rules by means of a special strategy, called
\bfindex{ordered rewriting}: a permutative rewrite
rule is only applied if the term becomes smaller with respect to a fixed
lexicographic ordering on terms. For example, commutativity rewrites
\<^term>\<open>b+a\<close> to \<^term>\<open>a+b\<close>, but then stops because \<^term>\<open>a+b\<close> is strictly
smaller than \<^term>\<open>b+a\<close>.  Permutative rewrite rules can be turned into
simplification rules in the usual manner via the \<open>simp\<close> attribute; the
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

Note that ordered rewriting for \<open>+\<close> and \<open>*\<close> on numbers is rarely
necessary because the built-in arithmetic prover often succeeds without
such tricks.
\<close>

subsection\<open>How the Simplifier Works\<close>

text\<open>\label{sec:SimpHow}
Roughly speaking, the simplifier proceeds bottom-up: subterms are simplified
first.  A conditional equation is only applied if its condition can be
proved, again by simplification.  Below we explain some special features of
the rewriting process. 
\<close>

subsubsection\<open>Higher-Order Patterns\<close>

text\<open>\index{simplification rule|(}
So far we have pretended the simplifier can deal with arbitrary
rewrite rules. This is not quite true.  For reasons of feasibility,
the simplifier expects the
left-hand side of each rule to be a so-called \emph{higher-order
pattern}~@{cite "nipkow-patterns"}\indexbold{patterns!higher-order}. 
This restricts where
unknowns may occur.  Higher-order patterns are terms in $\beta$-normal
form.  (This means there are no subterms of the form $(\lambda x. M)(N)$.)  
Each occurrence of an unknown is of the form
$\Var{f}~x@1~\dots~x@n$, where the $x@i$ are distinct bound
variables. Thus all ordinary rewrite rules, where all unknowns are
of base type, for example @{thm add.assoc}, are acceptable: if an unknown is
of base type, it cannot have any arguments. Additionally, the rule
\<open>(\<forall>x. ?P x \<and> ?Q x) = ((\<forall>x. ?P x) \<and> (\<forall>x. ?Q x))\<close> is also acceptable, in
both directions: all arguments of the unknowns \<open>?P\<close> and
\<open>?Q\<close> are distinct bound variables.

If the left-hand side is not a higher-order pattern, all is not lost.
The simplifier will still try to apply the rule provided it
matches directly: without much $\lambda$-calculus hocus
pocus.  For example, \<open>(?f ?x \<in> range ?f) = True\<close> rewrites
\<^term>\<open>g a \<in> range g\<close> to \<^const>\<open>True\<close>, but will fail to match
\<open>g(h b) \<in> range(\<lambda>x. g(h x))\<close>.  However, you can
eliminate the offending subterms --- those that are not patterns ---
by adding new variables and conditions.
In our example, we eliminate \<open>?f ?x\<close> and obtain
 \<open>?y =
?f ?x \<Longrightarrow> (?y \<in> range ?f) = True\<close>, which is fine
as a conditional rewrite rule since conditions can be arbitrary
terms.  However, this trick is not a panacea because the newly
introduced conditions may be hard to solve.
  
There is no restriction on the form of the right-hand
sides.  They may not contain extraneous term or type variables, though.
\<close>

subsubsection\<open>The Preprocessor\<close>

text\<open>\label{sec:simp-preprocessor}
When a theorem is declared a simplification rule, it need not be a
conditional equation already.  The simplifier will turn it into a set of
conditional equations automatically.  For example, \<^prop>\<open>f x =
g x & h x = k x\<close> becomes the two separate
simplification rules \<^prop>\<open>f x = g x\<close> and \<^prop>\<open>h x = k x\<close>. In
general, the input theorem is converted as follows:
\begin{eqnarray}
\neg P &\mapsto& P = \hbox{\isa{False}} \nonumber\\
P \longrightarrow Q &\mapsto& P \Longrightarrow Q \nonumber\\
P \land Q &\mapsto& P,\ Q \nonumber\\
\forall x.~P~x &\mapsto& P~\Var{x}\nonumber\\
\forall x \in A.\ P~x &\mapsto& \Var{x} \in A \Longrightarrow P~\Var{x} \nonumber\\
\<open>if\<close>\ P\ \<open>then\<close>\ Q\ \<open>else\<close>\ R &\mapsto&
 P \Longrightarrow Q,\ \neg P \Longrightarrow R \nonumber
\end{eqnarray}
Once this conversion process is finished, all remaining non-equations
$P$ are turned into trivial equations $P =\isa{True}$.
For example, the formula 
\begin{center}\<^prop>\<open>(p \<longrightarrow> t=u \<and> ~r) \<and> s\<close>\end{center}
is converted into the three rules
\begin{center}
\<^prop>\<open>p \<Longrightarrow> t = u\<close>,\quad  \<^prop>\<open>p \<Longrightarrow> r = False\<close>,\quad  \<^prop>\<open>s = True\<close>.
\end{center}
\index{simplification rule|)}
\index{simplification|)}
\<close>
(*<*)
end
(*>*)
