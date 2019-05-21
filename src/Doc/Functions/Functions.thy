(*  Title:      Doc/Functions/Functions.thy
    Author:     Alexander Krauss, TU Muenchen

Tutorial for function definitions with the new "function" package.
*)

theory Functions
imports Main
begin

section \<open>Function Definitions for Dummies\<close>

text \<open>
  In most cases, defining a recursive function is just as simple as other definitions:
\<close>

fun fib :: "nat \<Rightarrow> nat"
where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text \<open>
  The syntax is rather self-explanatory: We introduce a function by
  giving its name, its type, 
  and a set of defining recursive equations.
  If we leave out the type, the most general type will be
  inferred, which can sometimes lead to surprises: Since both \<^term>\<open>1::nat\<close> and \<open>+\<close> are overloaded, we would end up
  with \<open>fib :: nat \<Rightarrow> 'a::{one,plus}\<close>.
\<close>

text \<open>
  The function always terminates, since its argument gets smaller in
  every recursive call. 
  Since HOL is a logic of total functions, termination is a
  fundamental requirement to prevent inconsistencies\footnote{From the
  \qt{definition} \<open>f(n) = f(n) + 1\<close> we could prove 
  \<open>0 = 1\<close> by subtracting \<open>f(n)\<close> on both sides.}.
  Isabelle tries to prove termination automatically when a definition
  is made. In \S\ref{termination}, we will look at cases where this
  fails and see what to do then.
\<close>

subsection \<open>Pattern matching\<close>

text \<open>\label{patmatch}
  Like in functional programming, we can use pattern matching to
  define functions. At the moment we will only consider \emph{constructor
  patterns}, which only consist of datatype constructors and
  variables. Furthermore, patterns must be linear, i.e.\ all variables
  on the left hand side of an equation must be distinct. In
  \S\ref{genpats} we discuss more general pattern matching.

  If patterns overlap, the order of the equations is taken into
  account. The following function inserts a fixed element between any
  two elements of a list:
\<close>

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "sep a (x#y#xs) = x # a # sep a (y # xs)"
| "sep a xs       = xs"

text \<open>
  Overlapping patterns are interpreted as \qt{increments} to what is
  already there: The second equation is only meant for the cases where
  the first one does not match. Consequently, Isabelle replaces it
  internally by the remaining cases, making the patterns disjoint:
\<close>

thm sep.simps

text \<open>@{thm [display] sep.simps[no_vars]}\<close>

text \<open>
  \noindent The equations from function definitions are automatically used in
  simplification:
\<close>

lemma "sep 0 [1, 2, 3] = [1, 0, 2, 0, 3]"
by simp

subsection \<open>Induction\<close>

text \<open>

  Isabelle provides customized induction rules for recursive
  functions. These rules follow the recursive structure of the
  definition. Here is the rule @{thm [source] sep.induct} arising from the
  above definition of \<^const>\<open>sep\<close>:

  @{thm [display] sep.induct}
  
  We have a step case for list with at least two elements, and two
  base cases for the zero- and the one-element list. Here is a simple
  proof about \<^const>\<open>sep\<close> and \<^const>\<open>map\<close>
\<close>

lemma "map f (sep x ys) = sep (f x) (map f ys)"
apply (induct x ys rule: sep.induct)

text \<open>
  We get three cases, like in the definition.

  @{subgoals [display]}
\<close>

apply auto 
done
text \<open>

  With the \cmd{fun} command, you can define about 80\% of the
  functions that occur in practice. The rest of this tutorial explains
  the remaining 20\%.
\<close>


section \<open>fun vs.\ function\<close>

text \<open>
  The \cmd{fun} command provides a
  convenient shorthand notation for simple function definitions. In
  this mode, Isabelle tries to solve all the necessary proof obligations
  automatically. If any proof fails, the definition is
  rejected. This can either mean that the definition is indeed faulty,
  or that the default proof procedures are just not smart enough (or
  rather: not designed) to handle the definition.

  By expanding the abbreviation to the more verbose \cmd{function} command, these proof obligations become visible and can be analyzed or
  solved manually. The expansion from \cmd{fun} to \cmd{function} is as follows:

\end{isamarkuptext}


\[\left[\;\begin{minipage}{0.25\textwidth}\vspace{6pt}
\cmd{fun} \<open>f :: \<tau>\<close>\\%
\cmd{where}\\%
\hspace*{2ex}{\it equations}\\%
\hspace*{2ex}\vdots\vspace*{6pt}
\end{minipage}\right]
\quad\equiv\quad
\left[\;\begin{minipage}{0.48\textwidth}\vspace{6pt}
\cmd{function} \<open>(\<close>\cmd{sequential}\<open>) f :: \<tau>\<close>\\%
\cmd{where}\\%
\hspace*{2ex}{\it equations}\\%
\hspace*{2ex}\vdots\\%
\cmd{by} \<open>pat_completeness auto\<close>\\%
\cmd{termination by} \<open>lexicographic_order\<close>\vspace{6pt}
\end{minipage}
\right]\]

\begin{isamarkuptext}
  \vspace*{1em}
  \noindent Some details have now become explicit:

  \begin{enumerate}
  \item The \cmd{sequential} option enables the preprocessing of
  pattern overlaps which we already saw. Without this option, the equations
  must already be disjoint and complete. The automatic completion only
  works with constructor patterns.

  \item A function definition produces a proof obligation which
  expresses completeness and compatibility of patterns (we talk about
  this later). The combination of the methods \<open>pat_completeness\<close> and
  \<open>auto\<close> is used to solve this proof obligation.

  \item A termination proof follows the definition, started by the
  \cmd{termination} command. This will be explained in \S\ref{termination}.
 \end{enumerate}
  Whenever a \cmd{fun} command fails, it is usually a good idea to
  expand the syntax to the more verbose \cmd{function} form, to see
  what is actually going on.
\<close>


section \<open>Termination\<close>

text \<open>\label{termination}
  The method \<open>lexicographic_order\<close> is the default method for
  termination proofs. It can prove termination of a
  certain class of functions by searching for a suitable lexicographic
  combination of size measures. Of course, not all functions have such
  a simple termination argument. For them, we can specify the termination
  relation manually.
\<close>

subsection \<open>The {\tt relation} method\<close>
text\<open>
  Consider the following function, which sums up natural numbers up to
  \<open>N\<close>, using a counter \<open>i\<close>:
\<close>

function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "sum i N = (if i > N then 0 else i + sum (Suc i) N)"
by pat_completeness auto

text \<open>
  \noindent The \<open>lexicographic_order\<close> method fails on this example, because none of the
  arguments decreases in the recursive call, with respect to the standard size ordering.
  To prove termination manually, we must provide a custom wellfounded relation.

  The termination argument for \<open>sum\<close> is based on the fact that
  the \emph{difference} between \<open>i\<close> and \<open>N\<close> gets
  smaller in every step, and that the recursion stops when \<open>i\<close>
  is greater than \<open>N\<close>. Phrased differently, the expression 
  \<open>N + 1 - i\<close> always decreases.

  We can use this expression as a measure function suitable to prove termination.
\<close>

termination sum
apply (relation "measure (\<lambda>(i,N). N + 1 - i)")

text \<open>
  The \cmd{termination} command sets up the termination goal for the
  specified function \<open>sum\<close>. If the function name is omitted, it
  implicitly refers to the last function definition.

  The \<open>relation\<close> method takes a relation of
  type \<^typ>\<open>('a \<times> 'a) set\<close>, where \<^typ>\<open>'a\<close> is the argument type of
  the function. If the function has multiple curried arguments, then
  these are packed together into a tuple, as it happened in the above
  example.

  The predefined function @{term[source] "measure :: ('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"} constructs a
  wellfounded relation from a mapping into the natural numbers (a
  \emph{measure function}). 

  After the invocation of \<open>relation\<close>, we must prove that (a)
  the relation we supplied is wellfounded, and (b) that the arguments
  of recursive calls indeed decrease with respect to the
  relation:

  @{subgoals[display,indent=0]}

  These goals are all solved by \<open>auto\<close>:
\<close>

apply auto
done

text \<open>
  Let us complicate the function a little, by adding some more
  recursive calls: 
\<close>

function foo :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "foo i N = (if i > N 
              then (if N = 0 then 0 else foo 0 (N - 1))
              else i + foo (Suc i) N)"
by pat_completeness auto

text \<open>
  When \<open>i\<close> has reached \<open>N\<close>, it starts at zero again
  and \<open>N\<close> is decremented.
  This corresponds to a nested
  loop where one index counts up and the other down. Termination can
  be proved using a lexicographic combination of two measures, namely
  the value of \<open>N\<close> and the above difference. The \<^const>\<open>measures\<close> combinator generalizes \<open>measure\<close> by taking a
  list of measure functions.  
\<close>

termination 
by (relation "measures [\<lambda>(i, N). N, \<lambda>(i,N). N + 1 - i]") auto

subsection \<open>How \<open>lexicographic_order\<close> works\<close>

(*fun fails :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
where
  "fails a [] = a"
| "fails a (x#xs) = fails (x + a) (x # xs)"
*)

text \<open>
  To see how the automatic termination proofs work, let's look at an
  example where it fails\footnote{For a detailed discussion of the
  termination prover, see @{cite bulwahnKN07}}:

\end{isamarkuptext}  
\cmd{fun} \<open>fails :: "nat \<Rightarrow> nat list \<Rightarrow> nat"\<close>\\%
\cmd{where}\\%
\hspace*{2ex}\<open>"fails a [] = a"\<close>\\%
|\hspace*{1.5ex}\<open>"fails a (x#xs) = fails (x + a) (x#xs)"\<close>\\
\begin{isamarkuptext}

\noindent Isabelle responds with the following error:

\begin{isabelle}
*** Unfinished subgoals:\newline
*** (a, 1, <):\newline
*** \ 1.~\<open>\<And>x. x = 0\<close>\newline
*** (a, 1, <=):\newline
*** \ 1.~False\newline
*** (a, 2, <):\newline
*** \ 1.~False\newline
*** Calls:\newline
*** a) \<open>(a, x # xs) -->> (x + a, x # xs)\<close>\newline
*** Measures:\newline
*** 1) \<open>\<lambda>x. size (fst x)\<close>\newline
*** 2) \<open>\<lambda>x. size (snd x)\<close>\newline
*** Result matrix:\newline
*** \ \ \ \ 1\ \ 2  \newline
*** a:  ?   <= \newline
*** Could not find lexicographic termination order.\newline
*** At command "fun".\newline
\end{isabelle}
\<close>
text \<open>
  The key to this error message is the matrix at the bottom. The rows
  of that matrix correspond to the different recursive calls (In our
  case, there is just one). The columns are the function's arguments 
  (expressed through different measure functions, which map the
  argument tuple to a natural number). 

  The contents of the matrix summarize what is known about argument
  descents: The second argument has a weak descent (\<open><=\<close>) at the
  recursive call, and for the first argument nothing could be proved,
  which is expressed by \<open>?\<close>. In general, there are the values
  \<open><\<close>, \<open><=\<close> and \<open>?\<close>.

  For the failed proof attempts, the unfinished subgoals are also
  printed. Looking at these will often point to a missing lemma.
\<close>

subsection \<open>The \<open>size_change\<close> method\<close>

text \<open>
  Some termination goals that are beyond the powers of
  \<open>lexicographic_order\<close> can be solved automatically by the
  more powerful \<open>size_change\<close> method, which uses a variant of
  the size-change principle, together with some other
  techniques. While the details are discussed
  elsewhere @{cite krauss_phd},
  here are a few typical situations where
  \<open>lexicographic_order\<close> has difficulties and \<open>size_change\<close>
  may be worth a try:
  \begin{itemize}
  \item Arguments are permuted in a recursive call.
  \item Several mutually recursive functions with multiple arguments.
  \item Unusual control flow (e.g., when some recursive calls cannot
  occur in sequence).
  \end{itemize}

  Loading the theory \<open>Multiset\<close> makes the \<open>size_change\<close>
  method a bit stronger: it can then use multiset orders internally.
\<close>

subsection \<open>Configuring simplification rules for termination proofs\<close>

text \<open>
  Since both \<open>lexicographic_order\<close> and \<open>size_change\<close> rely on the simplifier internally,
  there can sometimes be the need for adding additional simp rules to them.
  This can be done either as arguments to the methods themselves, or globally via the
  theorem attribute \<open>termination_simp\<close>, which is useful in rare cases.
\<close>

section \<open>Mutual Recursion\<close>

text \<open>
  If two or more functions call one another mutually, they have to be defined
  in one step. Here are \<open>even\<close> and \<open>odd\<close>:
\<close>

function even :: "nat \<Rightarrow> bool"
    and odd  :: "nat \<Rightarrow> bool"
where
  "even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"
by pat_completeness auto

text \<open>
  To eliminate the mutual dependencies, Isabelle internally
  creates a single function operating on the sum
  type \<^typ>\<open>nat + nat\<close>. Then, \<^const>\<open>even\<close> and \<^const>\<open>odd\<close> are
  defined as projections. Consequently, termination has to be proved
  simultaneously for both functions, by specifying a measure on the
  sum type: 
\<close>

termination 
by (relation "measure (\<lambda>x. case x of Inl n \<Rightarrow> n | Inr n \<Rightarrow> n)") auto

text \<open>
  We could also have used \<open>lexicographic_order\<close>, which
  supports mutual recursive termination proofs to a certain extent.
\<close>

subsection \<open>Induction for mutual recursion\<close>

text \<open>

  When functions are mutually recursive, proving properties about them
  generally requires simultaneous induction. The induction rule @{thm [source] "even_odd.induct"}
  generated from the above definition reflects this.

  Let us prove something about \<^const>\<open>even\<close> and \<^const>\<open>odd\<close>:
\<close>

lemma even_odd_mod2:
  "even n = (n mod 2 = 0)"
  "odd n = (n mod 2 = 1)"

text \<open>
  We apply simultaneous induction, specifying the induction variable
  for both goals, separated by \cmd{and}:\<close>

apply (induct n and n rule: even_odd.induct)

text \<open>
  We get four subgoals, which correspond to the clauses in the
  definition of \<^const>\<open>even\<close> and \<^const>\<open>odd\<close>:
  @{subgoals[display,indent=0]}
  Simplification solves the first two goals, leaving us with two
  statements about the \<open>mod\<close> operation to prove:
\<close>

apply simp_all

text \<open>
  @{subgoals[display,indent=0]} 

  \noindent These can be handled by Isabelle's arithmetic decision procedures.
  
\<close>

apply arith
apply arith
done

text \<open>
  In proofs like this, the simultaneous induction is really essential:
  Even if we are just interested in one of the results, the other
  one is necessary to strengthen the induction hypothesis. If we leave
  out the statement about \<^const>\<open>odd\<close> and just write \<^term>\<open>True\<close> instead,
  the same proof fails:
\<close>

lemma failed_attempt:
  "even n = (n mod 2 = 0)"
  "True"
apply (induct n rule: even_odd.induct)

text \<open>
  \noindent Now the third subgoal is a dead end, since we have no
  useful induction hypothesis available:

  @{subgoals[display,indent=0]} 
\<close>

oops

section \<open>Elimination\<close>

text \<open>
  A definition of function \<open>f\<close> gives rise to two kinds of elimination rules. Rule \<open>f.cases\<close>
  simply describes case analysis according to the patterns used in the definition:
\<close>

fun list_to_option :: "'a list \<Rightarrow> 'a option"
where
  "list_to_option [x] = Some x"
| "list_to_option _ = None"

thm list_to_option.cases
text \<open>
  @{thm[display] list_to_option.cases}

  Note that this rule does not mention the function at all, but only describes the cases used for
  defining it. In contrast, the rule @{thm[source] list_to_option.elims} also tell us what the function
  value will be in each case:
\<close>
thm list_to_option.elims
text \<open>
  @{thm[display] list_to_option.elims}

  \noindent
  This lets us eliminate an assumption of the form \<^prop>\<open>list_to_option xs = y\<close> and replace it
  with the two cases, e.g.:
\<close>

lemma "list_to_option xs = y \<Longrightarrow> P"
proof (erule list_to_option.elims)
  fix x assume "xs = [x]" "y = Some x" thus P sorry
next
  assume "xs = []" "y = None" thus P sorry
next
  fix a b xs' assume "xs = a # b # xs'" "y = None" thus P sorry
qed


text \<open>
  Sometimes it is convenient to derive specialized versions of the \<open>elim\<close> rules above and
  keep them around as facts explicitly. For example, it is natural to show that if 
  \<^prop>\<open>list_to_option xs = Some y\<close>, then \<^term>\<open>xs\<close> must be a singleton. The command 
  \cmd{fun\_cases} derives such facts automatically, by instantiating and simplifying the general 
  elimination rules given some pattern:
\<close>

fun_cases list_to_option_SomeE[elim]: "list_to_option xs = Some y"

thm list_to_option_SomeE
text \<open>
  @{thm[display] list_to_option_SomeE}
\<close>


section \<open>General pattern matching\<close>
text\<open>\label{genpats}\<close>

subsection \<open>Avoiding automatic pattern splitting\<close>

text \<open>

  Up to now, we used pattern matching only on datatypes, and the
  patterns were always disjoint and complete, and if they weren't,
  they were made disjoint automatically like in the definition of
  \<^const>\<open>sep\<close> in \S\ref{patmatch}.

  This automatic splitting can significantly increase the number of
  equations involved, and this is not always desirable. The following
  example shows the problem:
  
  Suppose we are modeling incomplete knowledge about the world by a
  three-valued datatype, which has values \<^term>\<open>T\<close>, \<^term>\<open>F\<close>
  and \<^term>\<open>X\<close> for true, false and uncertain propositions, respectively. 
\<close>

datatype P3 = T | F | X

text \<open>\noindent Then the conjunction of such values can be defined as follows:\<close>

fun And :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And T p = p"
| "And p T = p"
| "And p F = F"
| "And F p = F"
| "And X X = X"


text \<open>
  This definition is useful, because the equations can directly be used
  as simplification rules. But the patterns overlap: For example,
  the expression \<^term>\<open>And T T\<close> is matched by both the first and
  the second equation. By default, Isabelle makes the patterns disjoint by
  splitting them up, producing instances:
\<close>

thm And.simps

text \<open>
  @{thm[indent=4] And.simps}
  
  \vspace*{1em}
  \noindent There are several problems with this:

  \begin{enumerate}
  \item If the datatype has many constructors, there can be an
  explosion of equations. For \<^const>\<open>And\<close>, we get seven instead of
  five equations, which can be tolerated, but this is just a small
  example.

  \item Since splitting makes the equations \qt{less general}, they
  do not always match in rewriting. While the term \<^term>\<open>And x F\<close>
  can be simplified to \<^term>\<open>F\<close> with the original equations, a
  (manual) case split on \<^term>\<open>x\<close> is now necessary.

  \item The splitting also concerns the induction rule @{thm [source]
  "And.induct"}. Instead of five premises it now has seven, which
  means that our induction proofs will have more cases.

  \item In general, it increases clarity if we get the same definition
  back which we put in.
  \end{enumerate}

  If we do not want the automatic splitting, we can switch it off by
  leaving out the \cmd{sequential} option. However, we will have to
  prove that our pattern matching is consistent\footnote{This prevents
  us from defining something like \<^term>\<open>f x = True\<close> and \<^term>\<open>f x
  = False\<close> simultaneously.}:
\<close>

function And2 :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And2 T p = p"
| "And2 p T = p"
| "And2 p F = F"
| "And2 F p = F"
| "And2 X X = X"

text \<open>
  \noindent Now let's look at the proof obligations generated by a
  function definition. In this case, they are:

  @{subgoals[display,indent=0]}\vspace{-1.2em}\hspace{3cm}\vdots\vspace{1.2em}

  The first subgoal expresses the completeness of the patterns. It has
  the form of an elimination rule and states that every \<^term>\<open>x\<close> of
  the function's input type must match at least one of the patterns\footnote{Completeness could
  be equivalently stated as a disjunction of existential statements: 
\<^term>\<open>(\<exists>p. x = (T, p)) \<or> (\<exists>p. x = (p, T)) \<or> (\<exists>p. x = (p, F)) \<or>
  (\<exists>p. x = (F, p)) \<or> (x = (X, X))\<close>, and you can use the method \<open>atomize_elim\<close> to get that form instead.}. If the patterns just involve
  datatypes, we can solve it with the \<open>pat_completeness\<close>
  method:
\<close>

apply pat_completeness

text \<open>
  The remaining subgoals express \emph{pattern compatibility}. We do
  allow that an input value matches multiple patterns, but in this
  case, the result (i.e.~the right hand sides of the equations) must
  also be equal. For each pair of two patterns, there is one such
  subgoal. Usually this needs injectivity of the constructors, which
  is used automatically by \<open>auto\<close>.
\<close>

by auto
termination by (relation "{}") simp


subsection \<open>Non-constructor patterns\<close>

text \<open>
  Most of Isabelle's basic types take the form of inductive datatypes,
  and usually pattern matching works on the constructors of such types. 
  However, this need not be always the case, and the \cmd{function}
  command handles other kind of patterns, too.

  One well-known instance of non-constructor patterns are
  so-called \emph{$n+k$-patterns}, which are a little controversial in
  the functional programming world. Here is the initial fibonacci
  example with $n+k$-patterns:
\<close>

function fib2 :: "nat \<Rightarrow> nat"
where
  "fib2 0 = 1"
| "fib2 1 = 1"
| "fib2 (n + 2) = fib2 n + fib2 (Suc n)"

text \<open>
  This kind of matching is again justified by the proof of pattern
  completeness and compatibility. 
  The proof obligation for pattern completeness states that every natural number is
  either \<^term>\<open>0::nat\<close>, \<^term>\<open>1::nat\<close> or \<^term>\<open>n +
  (2::nat)\<close>:

  @{subgoals[display,indent=0,goals_limit=1]}

  This is an arithmetic triviality, but unfortunately the
  \<open>arith\<close> method cannot handle this specific form of an
  elimination rule. However, we can use the method \<open>atomize_elim\<close> to do an ad-hoc conversion to a disjunction of
  existentials, which can then be solved by the arithmetic decision procedure.
  Pattern compatibility and termination are automatic as usual.
\<close>
apply atomize_elim
apply arith
apply auto
done
termination by lexicographic_order
text \<open>
  We can stretch the notion of pattern matching even more. The
  following function is not a sensible functional program, but a
  perfectly valid mathematical definition:
\<close>

function ev :: "nat \<Rightarrow> bool"
where
  "ev (2 * n) = True"
| "ev (2 * n + 1) = False"
apply atomize_elim
by arith+
termination by (relation "{}") simp

text \<open>
  This general notion of pattern matching gives you a certain freedom
  in writing down specifications. However, as always, such freedom should
  be used with care:

  If we leave the area of constructor
  patterns, we have effectively departed from the world of functional
  programming. This means that it is no longer possible to use the
  code generator, and expect it to generate ML code for our
  definitions. Also, such a specification might not work very well together with
  simplification. Your mileage may vary.
\<close>


subsection \<open>Conditional equations\<close>

text \<open>
  The function package also supports conditional equations, which are
  similar to guards in a language like Haskell. Here is Euclid's
  algorithm written with conditional patterns\footnote{Note that the
  patterns are also overlapping in the base case}:
\<close>

function gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd x 0 = x"
| "gcd 0 y = y"
| "x < y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (Suc x) (y - x)"
| "\<not> x < y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (x - y) (Suc y)"
by (atomize_elim, auto, arith)
termination by lexicographic_order

text \<open>
  By now, you can probably guess what the proof obligations for the
  pattern completeness and compatibility look like. 

  Again, functions with conditional patterns are not supported by the
  code generator.
\<close>


subsection \<open>Pattern matching on strings\<close>

text \<open>
  As strings (as lists of characters) are normal datatypes, pattern
  matching on them is possible, but somewhat problematic. Consider the
  following definition:

\end{isamarkuptext}
\noindent\cmd{fun} \<open>check :: "string \<Rightarrow> bool"\<close>\\%
\cmd{where}\\%
\hspace*{2ex}\<open>"check (''good'') = True"\<close>\\%
\<open>| "check s = False"\<close>
\begin{isamarkuptext}

  \noindent An invocation of the above \cmd{fun} command does not
  terminate. What is the problem? Strings are lists of characters, and
  characters are a datatype with a lot of constructors. Splitting the
  catch-all pattern thus leads to an explosion of cases, which cannot
  be handled by Isabelle.

  There are two things we can do here. Either we write an explicit
  \<open>if\<close> on the right hand side, or we can use conditional patterns:
\<close>

function check :: "string \<Rightarrow> bool"
where
  "check (''good'') = True"
| "s \<noteq> ''good'' \<Longrightarrow> check s = False"
by auto
termination by (relation "{}") simp


section \<open>Partiality\<close>

text \<open>
  In HOL, all functions are total. A function \<^term>\<open>f\<close> applied to
  \<^term>\<open>x\<close> always has the value \<^term>\<open>f x\<close>, and there is no notion
  of undefinedness. 
  This is why we have to do termination
  proofs when defining functions: The proof justifies that the
  function can be defined by wellfounded recursion.

  However, the \cmd{function} package does support partiality to a
  certain extent. Let's look at the following function which looks
  for a zero of a given function f. 
\<close>

function (*<*)(domintros)(*>*)findzero :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "findzero f n = (if f n = 0 then n else findzero f (Suc n))"
by pat_completeness auto

text \<open>
  \noindent Clearly, any attempt of a termination proof must fail. And without
  that, we do not get the usual rules \<open>findzero.simps\<close> and 
  \<open>findzero.induct\<close>. So what was the definition good for at all?
\<close>

subsection \<open>Domain predicates\<close>

text \<open>
  The trick is that Isabelle has not only defined the function \<^const>\<open>findzero\<close>, but also
  a predicate \<^term>\<open>findzero_dom\<close> that characterizes the values where the function
  terminates: the \emph{domain} of the function. If we treat a
  partial function just as a total function with an additional domain
  predicate, we can derive simplification and
  induction rules as we do for total functions. They are guarded
  by domain conditions and are called \<open>psimps\<close> and \<open>pinduct\<close>: 
\<close>

text \<open>
  \noindent\begin{minipage}{0.79\textwidth}@{thm[display,margin=85] findzero.psimps}\end{minipage}
  \hfill(@{thm [source] "findzero.psimps"})
  \vspace{1em}

  \noindent\begin{minipage}{0.79\textwidth}@{thm[display,margin=85] findzero.pinduct}\end{minipage}
  \hfill(@{thm [source] "findzero.pinduct"})
\<close>

text \<open>
  Remember that all we
  are doing here is use some tricks to make a total function appear
  as if it was partial. We can still write the term \<^term>\<open>findzero
  (\<lambda>x. 1) 0\<close> and like any other term of type \<^typ>\<open>nat\<close> it is equal
  to some natural number, although we might not be able to find out
  which one. The function is \emph{underdefined}.

  But it is defined enough to prove something interesting about it. We
  can prove that if \<^term>\<open>findzero f n\<close>
  terminates, it indeed returns a zero of \<^term>\<open>f\<close>:
\<close>

lemma findzero_zero: "findzero_dom (f, n) \<Longrightarrow> f (findzero f n) = 0"

text \<open>\noindent We apply induction as usual, but using the partial induction
  rule:\<close>

apply (induct f n rule: findzero.pinduct)

text \<open>\noindent This gives the following subgoals:

  @{subgoals[display,indent=0]}

  \noindent The hypothesis in our lemma was used to satisfy the first premise in
  the induction rule. However, we also get \<^term>\<open>findzero_dom (f, n)\<close> as a local assumption in the induction step. This
  allows unfolding \<^term>\<open>findzero f n\<close> using the \<open>psimps\<close>
  rule, and the rest is trivial.
\<close>
apply (simp add: findzero.psimps)
done

text \<open>
  Proofs about partial functions are often not harder than for total
  functions. Fig.~\ref{findzero_isar} shows a slightly more
  complicated proof written in Isar. It is verbose enough to show how
  partiality comes into play: From the partial induction, we get an
  additional domain condition hypothesis. Observe how this condition
  is applied when calls to \<^term>\<open>findzero\<close> are unfolded.
\<close>

text_raw \<open>
\begin{figure}
\hrule\vspace{6pt}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
\<close>
lemma "\<lbrakk>findzero_dom (f, n); x \<in> {n ..< findzero f n}\<rbrakk> \<Longrightarrow> f x \<noteq> 0"
proof (induct rule: findzero.pinduct)
  fix f n assume dom: "findzero_dom (f, n)"
               and IH: "\<lbrakk>f n \<noteq> 0; x \<in> {Suc n ..< findzero f (Suc n)}\<rbrakk> \<Longrightarrow> f x \<noteq> 0"
               and x_range: "x \<in> {n ..< findzero f n}"
  have "f n \<noteq> 0"
  proof 
    assume "f n = 0"
    with dom have "findzero f n = n" by (simp add: findzero.psimps)
    with x_range show False by auto
  qed
  
  from x_range have "x = n \<or> x \<in> {Suc n ..< findzero f n}" by auto
  thus "f x \<noteq> 0"
  proof
    assume "x = n"
    with \<open>f n \<noteq> 0\<close> show ?thesis by simp
  next
    assume "x \<in> {Suc n ..< findzero f n}"
    with dom and \<open>f n \<noteq> 0\<close> have "x \<in> {Suc n ..< findzero f (Suc n)}" by (simp add: findzero.psimps)
    with IH and \<open>f n \<noteq> 0\<close>
    show ?thesis by simp
  qed
qed
text_raw \<open>
\isamarkupfalse\isabellestyle{tt}
\end{minipage}\vspace{6pt}\hrule
\caption{A proof about a partial function}\label{findzero_isar}
\end{figure}
\<close>

subsection \<open>Partial termination proofs\<close>

text \<open>
  Now that we have proved some interesting properties about our
  function, we should turn to the domain predicate and see if it is
  actually true for some values. Otherwise we would have just proved
  lemmas with \<^term>\<open>False\<close> as a premise.

  Essentially, we need some introduction rules for \<open>findzero_dom\<close>. The function package can prove such domain
  introduction rules automatically. But since they are not used very
  often (they are almost never needed if the function is total), this
  functionality is disabled by default for efficiency reasons. So we have to go
  back and ask for them explicitly by passing the \<open>(domintros)\<close> option to the function package:

\vspace{1ex}
\noindent\cmd{function} \<open>(domintros) findzero :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"\<close>\\%
\cmd{where}\isanewline%
\ \ \ldots\\

  \noindent Now the package has proved an introduction rule for \<open>findzero_dom\<close>:
\<close>

thm findzero.domintros

text \<open>
  @{thm[display] findzero.domintros}

  Domain introduction rules allow to show that a given value lies in the
  domain of a function, if the arguments of all recursive calls
  are in the domain as well. They allow to do a \qt{single step} in a
  termination proof. Usually, you want to combine them with a suitable
  induction principle.

  Since our function increases its argument at recursive calls, we
  need an induction principle which works \qt{backwards}. We will use
  @{thm [source] inc_induct}, which allows to do induction from a fixed number
  \qt{downwards}:

  \begin{center}@{thm inc_induct}\hfill(@{thm [source] "inc_induct"})\end{center}

  Figure \ref{findzero_term} gives a detailed Isar proof of the fact
  that \<open>findzero\<close> terminates if there is a zero which is greater
  or equal to \<^term>\<open>n\<close>. First we derive two useful rules which will
  solve the base case and the step case of the induction. The
  induction is then straightforward, except for the unusual induction
  principle.

\<close>

text_raw \<open>
\begin{figure}
\hrule\vspace{6pt}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
\<close>
lemma findzero_termination:
  assumes "x \<ge> n" and "f x = 0"
  shows "findzero_dom (f, n)"
proof - 
  have base: "findzero_dom (f, x)"
    by (rule findzero.domintros) (simp add:\<open>f x = 0\<close>)

  have step: "\<And>i. findzero_dom (f, Suc i) 
    \<Longrightarrow> findzero_dom (f, i)"
    by (rule findzero.domintros) simp

  from \<open>x \<ge> n\<close> show ?thesis
  proof (induct rule:inc_induct)
    show "findzero_dom (f, x)" by (rule base)
  next
    fix i assume "findzero_dom (f, Suc i)"
    thus "findzero_dom (f, i)" by (rule step)
  qed
qed      
text_raw \<open>
\isamarkupfalse\isabellestyle{tt}
\end{minipage}\vspace{6pt}\hrule
\caption{Termination proof for \<open>findzero\<close>}\label{findzero_term}
\end{figure}
\<close>
      
text \<open>
  Again, the proof given in Fig.~\ref{findzero_term} has a lot of
  detail in order to explain the principles. Using more automation, we
  can also have a short proof:
\<close>

lemma findzero_termination_short:
  assumes zero: "x >= n" 
  assumes [simp]: "f x = 0"
  shows "findzero_dom (f, n)"
using zero
by (induct rule:inc_induct) (auto intro: findzero.domintros)
    
text \<open>
  \noindent It is simple to combine the partial correctness result with the
  termination lemma:
\<close>

lemma findzero_total_correctness:
  "f x = 0 \<Longrightarrow> f (findzero f 0) = 0"
by (blast intro: findzero_zero findzero_termination)

subsection \<open>Definition of the domain predicate\<close>

text \<open>
  Sometimes it is useful to know what the definition of the domain
  predicate looks like. Actually, \<open>findzero_dom\<close> is just an
  abbreviation:

  @{abbrev[display] findzero_dom}

  The domain predicate is the \emph{accessible part} of a relation \<^const>\<open>findzero_rel\<close>, which was also created internally by the function
  package. \<^const>\<open>findzero_rel\<close> is just a normal
  inductive predicate, so we can inspect its definition by
  looking at the introduction rules @{thm [source] findzero_rel.intros}.
  In our case there is just a single rule:

  @{thm[display] findzero_rel.intros}

  The predicate \<^const>\<open>findzero_rel\<close>
  describes the \emph{recursion relation} of the function
  definition. The recursion relation is a binary relation on
  the arguments of the function that relates each argument to its
  recursive calls. In general, there is one introduction rule for each
  recursive call.

  The predicate \<^term>\<open>Wellfounded.accp findzero_rel\<close> is the accessible part of
  that relation. An argument belongs to the accessible part, if it can
  be reached in a finite number of steps (cf.~its definition in \<open>Wellfounded.thy\<close>).

  Since the domain predicate is just an abbreviation, you can use
  lemmas for \<^const>\<open>Wellfounded.accp\<close> and \<^const>\<open>findzero_rel\<close> directly. Some
  lemmas which are occasionally useful are @{thm [source] accpI}, @{thm [source]
  accp_downward}, and of course the introduction and elimination rules
  for the recursion relation @{thm [source] "findzero_rel.intros"} and @{thm
  [source] "findzero_rel.cases"}.
\<close>

section \<open>Nested recursion\<close>

text \<open>
  Recursive calls which are nested in one another frequently cause
  complications, since their termination proof can depend on a partial
  correctness property of the function itself. 

  As a small example, we define the \qt{nested zero} function:
\<close>

function nz :: "nat \<Rightarrow> nat"
where
  "nz 0 = 0"
| "nz (Suc n) = nz (nz n)"
by pat_completeness auto

text \<open>
  If we attempt to prove termination using the identity measure on
  naturals, this fails:
\<close>

termination
  apply (relation "measure (\<lambda>n. n)")
  apply auto

text \<open>
  We get stuck with the subgoal

  @{subgoals[display]}

  Of course this statement is true, since we know that \<^const>\<open>nz\<close> is
  the zero function. And in fact we have no problem proving this
  property by induction.
\<close>
(*<*)oops(*>*)
lemma nz_is_zero: "nz_dom n \<Longrightarrow> nz n = 0"
  by (induct rule:nz.pinduct) (auto simp: nz.psimps)

text \<open>
  We formulate this as a partial correctness lemma with the condition
  \<^term>\<open>nz_dom n\<close>. This allows us to prove it with the \<open>pinduct\<close> rule before we have proved termination. With this lemma,
  the termination proof works as expected:
\<close>

termination
  by (relation "measure (\<lambda>n. n)") (auto simp: nz_is_zero)

text \<open>
  As a general strategy, one should prove the statements needed for
  termination as a partial property first. Then they can be used to do
  the termination proof. This also works for less trivial
  examples. Figure \ref{f91} defines the 91-function, a well-known
  challenge problem due to John McCarthy, and proves its termination.
\<close>

text_raw \<open>
\begin{figure}
\hrule\vspace{6pt}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
\<close>

function f91 :: "nat \<Rightarrow> nat"
where
  "f91 n = (if 100 < n then n - 10 else f91 (f91 (n + 11)))"
by pat_completeness auto

lemma f91_estimate: 
  assumes trm: "f91_dom n" 
  shows "n < f91 n + 11"
using trm by induct (auto simp: f91.psimps)

termination
proof
  let ?R = "measure (\<lambda>x. 101 - x)"
  show "wf ?R" ..

  fix n :: nat assume "\<not> 100 < n" \<comment> \<open>Assumptions for both calls\<close>

  thus "(n + 11, n) \<in> ?R" by simp \<comment> \<open>Inner call\<close>

  assume inner_trm: "f91_dom (n + 11)" \<comment> \<open>Outer call\<close>
  with f91_estimate have "n + 11 < f91 (n + 11) + 11" .
  with \<open>\<not> 100 < n\<close> show "(f91 (n + 11), n) \<in> ?R" by simp
qed

text_raw \<open>
\isamarkupfalse\isabellestyle{tt}
\end{minipage}
\vspace{6pt}\hrule
\caption{McCarthy's 91-function}\label{f91}
\end{figure}
\<close>


section \<open>Higher-Order Recursion\<close>

text \<open>
  Higher-order recursion occurs when recursive calls
  are passed as arguments to higher-order combinators such as \<^const>\<open>map\<close>, \<^term>\<open>filter\<close> etc.
  As an example, imagine a datatype of n-ary trees:
\<close>

datatype 'a tree = 
  Leaf 'a 
| Branch "'a tree list"


text \<open>\noindent We can define a function which swaps the left and right subtrees recursively, using the 
  list functions \<^const>\<open>rev\<close> and \<^const>\<open>map\<close>:\<close>

fun mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "mirror (Leaf n) = Leaf n"
| "mirror (Branch l) = Branch (rev (map mirror l))"

text \<open>
  Although the definition is accepted without problems, let us look at the termination proof:
\<close>

termination proof
  text \<open>

  As usual, we have to give a wellfounded relation, such that the
  arguments of the recursive calls get smaller. But what exactly are
  the arguments of the recursive calls when mirror is given as an
  argument to \<^const>\<open>map\<close>? Isabelle gives us the
  subgoals

  @{subgoals[display,indent=0]} 

  So the system seems to know that \<^const>\<open>map\<close> only
  applies the recursive call \<^term>\<open>mirror\<close> to elements
  of \<^term>\<open>l\<close>, which is essential for the termination proof.

  This knowledge about \<^const>\<open>map\<close> is encoded in so-called congruence rules,
  which are special theorems known to the \cmd{function} command. The
  rule for \<^const>\<open>map\<close> is

  @{thm[display] map_cong}

  You can read this in the following way: Two applications of \<^const>\<open>map\<close> are equal, if the list arguments are equal and the functions
  coincide on the elements of the list. This means that for the value 
  \<^term>\<open>map f l\<close> we only have to know how \<^term>\<open>f\<close> behaves on
  the elements of \<^term>\<open>l\<close>.

  Usually, one such congruence rule is
  needed for each higher-order construct that is used when defining
  new functions. In fact, even basic functions like \<^const>\<open>If\<close> and \<^const>\<open>Let\<close> are handled by this mechanism. The congruence
  rule for \<^const>\<open>If\<close> states that the \<open>then\<close> branch is only
  relevant if the condition is true, and the \<open>else\<close> branch only if it
  is false:

  @{thm[display] if_cong}
  
  Congruence rules can be added to the
  function package by giving them the \<^term>\<open>fundef_cong\<close> attribute.

  The constructs that are predefined in Isabelle, usually
  come with the respective congruence rules.
  But if you define your own higher-order functions, you may have to
  state and prove the required congruence rules yourself, if you want to use your
  functions in recursive definitions. 
\<close>
(*<*)oops(*>*)

subsection \<open>Congruence Rules and Evaluation Order\<close>

text \<open>
  Higher order logic differs from functional programming languages in
  that it has no built-in notion of evaluation order. A program is
  just a set of equations, and it is not specified how they must be
  evaluated. 

  However for the purpose of function definition, we must talk about
  evaluation order implicitly, when we reason about termination.
  Congruence rules express that a certain evaluation order is
  consistent with the logical definition. 

  Consider the following function.
\<close>

function f :: "nat \<Rightarrow> bool"
where
  "f n = (n = 0 \<or> f (n - 1))"
(*<*)by pat_completeness auto(*>*)

text \<open>
  For this definition, the termination proof fails. The default configuration
  specifies no congruence rule for disjunction. We have to add a
  congruence rule that specifies left-to-right evaluation order:

  \vspace{1ex}
  \noindent @{thm disj_cong}\hfill(@{thm [source] "disj_cong"})
  \vspace{1ex}

  Now the definition works without problems. Note how the termination
  proof depends on the extra condition that we get from the congruence
  rule.

  However, as evaluation is not a hard-wired concept, we
  could just turn everything around by declaring a different
  congruence rule. Then we can make the reverse definition:
\<close>

lemma disj_cong2[fundef_cong]: 
  "(\<not> Q' \<Longrightarrow> P = P') \<Longrightarrow> (Q = Q') \<Longrightarrow> (P \<or> Q) = (P' \<or> Q')"
  by blast

fun f' :: "nat \<Rightarrow> bool"
where
  "f' n = (f' (n - 1) \<or> n = 0)"

text \<open>
  \noindent These examples show that, in general, there is no \qt{best} set of
  congruence rules.

  However, such tweaking should rarely be necessary in
  practice, as most of the time, the default set of congruence rules
  works well.
\<close>

end
