(*  Title:      doc-src/IsarAdvanced/Functions/Thy/Fundefs.thy
    Author:     Alexander Krauss, TU Muenchen

Tutorial for function definitions with the new "function" package.
*)

theory Functions
imports Main
begin

section {* Function Definitions for Dummies *}

text {*
  In most cases, defining a recursive function is just as simple as other definitions:
*}

fun fib :: "nat \<Rightarrow> nat"
where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text {*
  The syntax is rather self-explanatory: We introduce a function by
  giving its name, its type, 
  and a set of defining recursive equations.
  If we leave out the type, the most general type will be
  inferred, which can sometimes lead to surprises: Since both @{term
  "1::nat"} and @{text "+"} are overloaded, we would end up
  with @{text "fib :: nat \<Rightarrow> 'a::{one,plus}"}.
*}

text {*
  The function always terminates, since its argument gets smaller in
  every recursive call. 
  Since HOL is a logic of total functions, termination is a
  fundamental requirement to prevent inconsistencies\footnote{From the
  \qt{definition} @{text "f(n) = f(n) + 1"} we could prove 
  @{text "0 = 1"} by subtracting @{text "f(n)"} on both sides.}.
  Isabelle tries to prove termination automatically when a definition
  is made. In \S\ref{termination}, we will look at cases where this
  fails and see what to do then.
*}

subsection {* Pattern matching *}

text {* \label{patmatch}
  Like in functional programming, we can use pattern matching to
  define functions. At the moment we will only consider \emph{constructor
  patterns}, which only consist of datatype constructors and
  variables. Furthermore, patterns must be linear, i.e.\ all variables
  on the left hand side of an equation must be distinct. In
  \S\ref{genpats} we discuss more general pattern matching.

  If patterns overlap, the order of the equations is taken into
  account. The following function inserts a fixed element between any
  two elements of a list:
*}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "sep a (x#y#xs) = x # a # sep a (y # xs)"
| "sep a xs       = xs"

text {* 
  Overlapping patterns are interpreted as \qt{increments} to what is
  already there: The second equation is only meant for the cases where
  the first one does not match. Consequently, Isabelle replaces it
  internally by the remaining cases, making the patterns disjoint:
*}

thm sep.simps

text {* @{thm [display] sep.simps[no_vars]} *}

text {* 
  \noindent The equations from function definitions are automatically used in
  simplification:
*}

lemma "sep 0 [1, 2, 3] = [1, 0, 2, 0, 3]"
by simp

subsection {* Induction *}

text {*

  Isabelle provides customized induction rules for recursive
  functions. These rules follow the recursive structure of the
  definition. Here is the rule @{text sep.induct} arising from the
  above definition of @{const sep}:

  @{thm [display] sep.induct}
  
  We have a step case for list with at least two elements, and two
  base cases for the zero- and the one-element list. Here is a simple
  proof about @{const sep} and @{const map}
*}

lemma "map f (sep x ys) = sep (f x) (map f ys)"
apply (induct x ys rule: sep.induct)

txt {*
  We get three cases, like in the definition.

  @{subgoals [display]}
*}

apply auto 
done
text {*

  With the \cmd{fun} command, you can define about 80\% of the
  functions that occur in practice. The rest of this tutorial explains
  the remaining 20\%.
*}


section {* fun vs.\ function *}

text {* 
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
\cmd{fun} @{text "f :: \<tau>"}\\%
\cmd{where}\\%
\hspace*{2ex}{\it equations}\\%
\hspace*{2ex}\vdots\vspace*{6pt}
\end{minipage}\right]
\quad\equiv\quad
\left[\;\begin{minipage}{0.48\textwidth}\vspace{6pt}
\cmd{function} @{text "("}\cmd{sequential}@{text ") f :: \<tau>"}\\%
\cmd{where}\\%
\hspace*{2ex}{\it equations}\\%
\hspace*{2ex}\vdots\\%
\cmd{by} @{text "pat_completeness auto"}\\%
\cmd{termination by} @{text "lexicographic_order"}\vspace{6pt}
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
  this later). The combination of the methods @{text "pat_completeness"} and
  @{text "auto"} is used to solve this proof obligation.

  \item A termination proof follows the definition, started by the
  \cmd{termination} command. This will be explained in \S\ref{termination}.
 \end{enumerate}
  Whenever a \cmd{fun} command fails, it is usually a good idea to
  expand the syntax to the more verbose \cmd{function} form, to see
  what is actually going on.
 *}


section {* Termination *}

text {*\label{termination}
  The method @{text "lexicographic_order"} is the default method for
  termination proofs. It can prove termination of a
  certain class of functions by searching for a suitable lexicographic
  combination of size measures. Of course, not all functions have such
  a simple termination argument. For them, we can specify the termination
  relation manually.
*}

subsection {* The {\tt relation} method *}
text{*
  Consider the following function, which sums up natural numbers up to
  @{text "N"}, using a counter @{text "i"}:
*}

function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "sum i N = (if i > N then 0 else i + sum (Suc i) N)"
by pat_completeness auto

text {*
  \noindent The @{text "lexicographic_order"} method fails on this example, because none of the
  arguments decreases in the recursive call, with respect to the standard size ordering.
  To prove termination manually, we must provide a custom wellfounded relation.

  The termination argument for @{text "sum"} is based on the fact that
  the \emph{difference} between @{text "i"} and @{text "N"} gets
  smaller in every step, and that the recursion stops when @{text "i"}
  is greater than @{text "N"}. Phrased differently, the expression 
  @{text "N + 1 - i"} always decreases.

  We can use this expression as a measure function suitable to prove termination.
*}

termination sum
apply (relation "measure (\<lambda>(i,N). N + 1 - i)")

txt {*
  The \cmd{termination} command sets up the termination goal for the
  specified function @{text "sum"}. If the function name is omitted, it
  implicitly refers to the last function definition.

  The @{text relation} method takes a relation of
  type @{typ "('a \<times> 'a) set"}, where @{typ "'a"} is the argument type of
  the function. If the function has multiple curried arguments, then
  these are packed together into a tuple, as it happened in the above
  example.

  The predefined function @{term[source] "measure :: ('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"} constructs a
  wellfounded relation from a mapping into the natural numbers (a
  \emph{measure function}). 

  After the invocation of @{text "relation"}, we must prove that (a)
  the relation we supplied is wellfounded, and (b) that the arguments
  of recursive calls indeed decrease with respect to the
  relation:

  @{subgoals[display,indent=0]}

  These goals are all solved by @{text "auto"}:
*}

apply auto
done

text {*
  Let us complicate the function a little, by adding some more
  recursive calls: 
*}

function foo :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "foo i N = (if i > N 
              then (if N = 0 then 0 else foo 0 (N - 1))
              else i + foo (Suc i) N)"
by pat_completeness auto

text {*
  When @{text "i"} has reached @{text "N"}, it starts at zero again
  and @{text "N"} is decremented.
  This corresponds to a nested
  loop where one index counts up and the other down. Termination can
  be proved using a lexicographic combination of two measures, namely
  the value of @{text "N"} and the above difference. The @{const
  "measures"} combinator generalizes @{text "measure"} by taking a
  list of measure functions.  
*}

termination 
by (relation "measures [\<lambda>(i, N). N, \<lambda>(i,N). N + 1 - i]") auto

subsection {* How @{text "lexicographic_order"} works *}

(*fun fails :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
where
  "fails a [] = a"
| "fails a (x#xs) = fails (x + a) (x # xs)"
*)

text {*
  To see how the automatic termination proofs work, let's look at an
  example where it fails\footnote{For a detailed discussion of the
  termination prover, see \cite{bulwahnKN07}}:

\end{isamarkuptext}  
\cmd{fun} @{text "fails :: \"nat \<Rightarrow> nat list \<Rightarrow> nat\""}\\%
\cmd{where}\\%
\hspace*{2ex}@{text "\"fails a [] = a\""}\\%
|\hspace*{1.5ex}@{text "\"fails a (x#xs) = fails (x + a) (x#xs)\""}\\
\begin{isamarkuptext}

\noindent Isabelle responds with the following error:

\begin{isabelle}
*** Unfinished subgoals:\newline
*** (a, 1, <):\newline
*** \ 1.~@{text "\<And>x. x = 0"}\newline
*** (a, 1, <=):\newline
*** \ 1.~False\newline
*** (a, 2, <):\newline
*** \ 1.~False\newline
*** Calls:\newline
*** a) @{text "(a, x # xs) -->> (x + a, x # xs)"}\newline
*** Measures:\newline
*** 1) @{text "\<lambda>x. size (fst x)"}\newline
*** 2) @{text "\<lambda>x. size (snd x)"}\newline
*** Result matrix:\newline
*** \ \ \ \ 1\ \ 2  \newline
*** a:  ?   <= \newline
*** Could not find lexicographic termination order.\newline
*** At command "fun".\newline
\end{isabelle}
*}
text {*
  The key to this error message is the matrix at the bottom. The rows
  of that matrix correspond to the different recursive calls (In our
  case, there is just one). The columns are the function's arguments 
  (expressed through different measure functions, which map the
  argument tuple to a natural number). 

  The contents of the matrix summarize what is known about argument
  descents: The second argument has a weak descent (@{text "<="}) at the
  recursive call, and for the first argument nothing could be proved,
  which is expressed by @{text "?"}. In general, there are the values
  @{text "<"}, @{text "<="} and @{text "?"}.

  For the failed proof attempts, the unfinished subgoals are also
  printed. Looking at these will often point to a missing lemma.
*}

subsection {* The @{text size_change} method *}

text {*
  Some termination goals that are beyond the powers of
  @{text lexicographic_order} can be solved automatically by the
  more powerful @{text size_change} method, which uses a variant of
  the size-change principle, together with some other
  techniques. While the details are discussed
  elsewhere\cite{krauss_phd},
  here are a few typical situations where
  @{text lexicographic_order} has difficulties and @{text size_change}
  may be worth a try:
  \begin{itemize}
  \item Arguments are permuted in a recursive call.
  \item Several mutually recursive functions with multiple arguments.
  \item Unusual control flow (e.g., when some recursive calls cannot
  occur in sequence).
  \end{itemize}

  Loading the theory @{text Multiset} makes the @{text size_change}
  method a bit stronger: it can then use multiset orders internally.
*}

section {* Mutual Recursion *}

text {*
  If two or more functions call one another mutually, they have to be defined
  in one step. Here are @{text "even"} and @{text "odd"}:
*}

function even :: "nat \<Rightarrow> bool"
    and odd  :: "nat \<Rightarrow> bool"
where
  "even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"
by pat_completeness auto

text {*
  To eliminate the mutual dependencies, Isabelle internally
  creates a single function operating on the sum
  type @{typ "nat + nat"}. Then, @{const even} and @{const odd} are
  defined as projections. Consequently, termination has to be proved
  simultaneously for both functions, by specifying a measure on the
  sum type: 
*}

termination 
by (relation "measure (\<lambda>x. case x of Inl n \<Rightarrow> n | Inr n \<Rightarrow> n)") auto

text {* 
  We could also have used @{text lexicographic_order}, which
  supports mutual recursive termination proofs to a certain extent.
*}

subsection {* Induction for mutual recursion *}

text {*

  When functions are mutually recursive, proving properties about them
  generally requires simultaneous induction. The induction rule @{text "even_odd.induct"}
  generated from the above definition reflects this.

  Let us prove something about @{const even} and @{const odd}:
*}

lemma even_odd_mod2:
  "even n = (n mod 2 = 0)"
  "odd n = (n mod 2 = 1)"

txt {* 
  We apply simultaneous induction, specifying the induction variable
  for both goals, separated by \cmd{and}:  *}

apply (induct n and n rule: even_odd.induct)

txt {* 
  We get four subgoals, which correspond to the clauses in the
  definition of @{const even} and @{const odd}:
  @{subgoals[display,indent=0]}
  Simplification solves the first two goals, leaving us with two
  statements about the @{text "mod"} operation to prove:
*}

apply simp_all

txt {* 
  @{subgoals[display,indent=0]} 

  \noindent These can be handled by Isabelle's arithmetic decision procedures.
  
*}

apply arith
apply arith
done

text {*
  In proofs like this, the simultaneous induction is really essential:
  Even if we are just interested in one of the results, the other
  one is necessary to strengthen the induction hypothesis. If we leave
  out the statement about @{const odd} and just write @{term True} instead,
  the same proof fails:
*}

lemma failed_attempt:
  "even n = (n mod 2 = 0)"
  "True"
apply (induct n rule: even_odd.induct)

txt {*
  \noindent Now the third subgoal is a dead end, since we have no
  useful induction hypothesis available:

  @{subgoals[display,indent=0]} 
*}

oops

section {* General pattern matching *}
text{*\label{genpats} *}

subsection {* Avoiding automatic pattern splitting *}

text {*

  Up to now, we used pattern matching only on datatypes, and the
  patterns were always disjoint and complete, and if they weren't,
  they were made disjoint automatically like in the definition of
  @{const "sep"} in \S\ref{patmatch}.

  This automatic splitting can significantly increase the number of
  equations involved, and this is not always desirable. The following
  example shows the problem:
  
  Suppose we are modeling incomplete knowledge about the world by a
  three-valued datatype, which has values @{term "T"}, @{term "F"}
  and @{term "X"} for true, false and uncertain propositions, respectively. 
*}

datatype P3 = T | F | X

text {* \noindent Then the conjunction of such values can be defined as follows: *}

fun And :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And T p = p"
| "And p T = p"
| "And p F = F"
| "And F p = F"
| "And X X = X"


text {* 
  This definition is useful, because the equations can directly be used
  as simplification rules. But the patterns overlap: For example,
  the expression @{term "And T T"} is matched by both the first and
  the second equation. By default, Isabelle makes the patterns disjoint by
  splitting them up, producing instances:
*}

thm And.simps

text {*
  @{thm[indent=4] And.simps}
  
  \vspace*{1em}
  \noindent There are several problems with this:

  \begin{enumerate}
  \item If the datatype has many constructors, there can be an
  explosion of equations. For @{const "And"}, we get seven instead of
  five equations, which can be tolerated, but this is just a small
  example.

  \item Since splitting makes the equations \qt{less general}, they
  do not always match in rewriting. While the term @{term "And x F"}
  can be simplified to @{term "F"} with the original equations, a
  (manual) case split on @{term "x"} is now necessary.

  \item The splitting also concerns the induction rule @{text
  "And.induct"}. Instead of five premises it now has seven, which
  means that our induction proofs will have more cases.

  \item In general, it increases clarity if we get the same definition
  back which we put in.
  \end{enumerate}

  If we do not want the automatic splitting, we can switch it off by
  leaving out the \cmd{sequential} option. However, we will have to
  prove that our pattern matching is consistent\footnote{This prevents
  us from defining something like @{term "f x = True"} and @{term "f x
  = False"} simultaneously.}:
*}

function And2 :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And2 T p = p"
| "And2 p T = p"
| "And2 p F = F"
| "And2 F p = F"
| "And2 X X = X"

txt {*
  \noindent Now let's look at the proof obligations generated by a
  function definition. In this case, they are:

  @{subgoals[display,indent=0]}\vspace{-1.2em}\hspace{3cm}\vdots\vspace{1.2em}

  The first subgoal expresses the completeness of the patterns. It has
  the form of an elimination rule and states that every @{term x} of
  the function's input type must match at least one of the patterns\footnote{Completeness could
  be equivalently stated as a disjunction of existential statements: 
@{term "(\<exists>p. x = (T, p)) \<or> (\<exists>p. x = (p, T)) \<or> (\<exists>p. x = (p, F)) \<or>
  (\<exists>p. x = (F, p)) \<or> (x = (X, X))"}, and you can use the method @{text atomize_elim} to get that form instead.}. If the patterns just involve
  datatypes, we can solve it with the @{text "pat_completeness"}
  method:
*}

apply pat_completeness

txt {*
  The remaining subgoals express \emph{pattern compatibility}. We do
  allow that an input value matches multiple patterns, but in this
  case, the result (i.e.~the right hand sides of the equations) must
  also be equal. For each pair of two patterns, there is one such
  subgoal. Usually this needs injectivity of the constructors, which
  is used automatically by @{text "auto"}.
*}

by auto
termination by (relation "{}") simp


subsection {* Non-constructor patterns *}

text {*
  Most of Isabelle's basic types take the form of inductive datatypes,
  and usually pattern matching works on the constructors of such types. 
  However, this need not be always the case, and the \cmd{function}
  command handles other kind of patterns, too.

  One well-known instance of non-constructor patterns are
  so-called \emph{$n+k$-patterns}, which are a little controversial in
  the functional programming world. Here is the initial fibonacci
  example with $n+k$-patterns:
*}

function fib2 :: "nat \<Rightarrow> nat"
where
  "fib2 0 = 1"
| "fib2 1 = 1"
| "fib2 (n + 2) = fib2 n + fib2 (Suc n)"

txt {*
  This kind of matching is again justified by the proof of pattern
  completeness and compatibility. 
  The proof obligation for pattern completeness states that every natural number is
  either @{term "0::nat"}, @{term "1::nat"} or @{term "n +
  (2::nat)"}:

  @{subgoals[display,indent=0,goals_limit=1]}

  This is an arithmetic triviality, but unfortunately the
  @{text arith} method cannot handle this specific form of an
  elimination rule. However, we can use the method @{text
  "atomize_elim"} to do an ad-hoc conversion to a disjunction of
  existentials, which can then be solved by the arithmetic decision procedure.
  Pattern compatibility and termination are automatic as usual.
*}
apply atomize_elim
apply arith
apply auto
done
termination by lexicographic_order
text {*
  We can stretch the notion of pattern matching even more. The
  following function is not a sensible functional program, but a
  perfectly valid mathematical definition:
*}

function ev :: "nat \<Rightarrow> bool"
where
  "ev (2 * n) = True"
| "ev (2 * n + 1) = False"
apply atomize_elim
by arith+
termination by (relation "{}") simp

text {*
  This general notion of pattern matching gives you a certain freedom
  in writing down specifications. However, as always, such freedom should
  be used with care:

  If we leave the area of constructor
  patterns, we have effectively departed from the world of functional
  programming. This means that it is no longer possible to use the
  code generator, and expect it to generate ML code for our
  definitions. Also, such a specification might not work very well together with
  simplification. Your mileage may vary.
*}


subsection {* Conditional equations *}

text {* 
  The function package also supports conditional equations, which are
  similar to guards in a language like Haskell. Here is Euclid's
  algorithm written with conditional patterns\footnote{Note that the
  patterns are also overlapping in the base case}:
*}

function gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd x 0 = x"
| "gcd 0 y = y"
| "x < y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (Suc x) (y - x)"
| "\<not> x < y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (x - y) (Suc y)"
by (atomize_elim, auto, arith)
termination by lexicographic_order

text {*
  By now, you can probably guess what the proof obligations for the
  pattern completeness and compatibility look like. 

  Again, functions with conditional patterns are not supported by the
  code generator.
*}


subsection {* Pattern matching on strings *}

text {*
  As strings (as lists of characters) are normal datatypes, pattern
  matching on them is possible, but somewhat problematic. Consider the
  following definition:

\end{isamarkuptext}
\noindent\cmd{fun} @{text "check :: \"string \<Rightarrow> bool\""}\\%
\cmd{where}\\%
\hspace*{2ex}@{text "\"check (''good'') = True\""}\\%
@{text "| \"check s = False\""}
\begin{isamarkuptext}

  \noindent An invocation of the above \cmd{fun} command does not
  terminate. What is the problem? Strings are lists of characters, and
  characters are a datatype with a lot of constructors. Splitting the
  catch-all pattern thus leads to an explosion of cases, which cannot
  be handled by Isabelle.

  There are two things we can do here. Either we write an explicit
  @{text "if"} on the right hand side, or we can use conditional patterns:
*}

function check :: "string \<Rightarrow> bool"
where
  "check (''good'') = True"
| "s \<noteq> ''good'' \<Longrightarrow> check s = False"
by auto
termination by (relation "{}") simp


section {* Partiality *}

text {* 
  In HOL, all functions are total. A function @{term "f"} applied to
  @{term "x"} always has the value @{term "f x"}, and there is no notion
  of undefinedness. 
  This is why we have to do termination
  proofs when defining functions: The proof justifies that the
  function can be defined by wellfounded recursion.

  However, the \cmd{function} package does support partiality to a
  certain extent. Let's look at the following function which looks
  for a zero of a given function f. 
*}

function (*<*)(domintros)(*>*)findzero :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "findzero f n = (if f n = 0 then n else findzero f (Suc n))"
by pat_completeness auto

text {*
  \noindent Clearly, any attempt of a termination proof must fail. And without
  that, we do not get the usual rules @{text "findzero.simps"} and 
  @{text "findzero.induct"}. So what was the definition good for at all?
*}

subsection {* Domain predicates *}

text {*
  The trick is that Isabelle has not only defined the function @{const findzero}, but also
  a predicate @{term "findzero_dom"} that characterizes the values where the function
  terminates: the \emph{domain} of the function. If we treat a
  partial function just as a total function with an additional domain
  predicate, we can derive simplification and
  induction rules as we do for total functions. They are guarded
  by domain conditions and are called @{text psimps} and @{text
  pinduct}: 
*}

text {*
  \noindent\begin{minipage}{0.79\textwidth}@{thm[display,margin=85] findzero.psimps}\end{minipage}
  \hfill(@{text "findzero.psimps"})
  \vspace{1em}

  \noindent\begin{minipage}{0.79\textwidth}@{thm[display,margin=85] findzero.pinduct}\end{minipage}
  \hfill(@{text "findzero.pinduct"})
*}

text {*
  Remember that all we
  are doing here is use some tricks to make a total function appear
  as if it was partial. We can still write the term @{term "findzero
  (\<lambda>x. 1) 0"} and like any other term of type @{typ nat} it is equal
  to some natural number, although we might not be able to find out
  which one. The function is \emph{underdefined}.

  But it is defined enough to prove something interesting about it. We
  can prove that if @{term "findzero f n"}
  terminates, it indeed returns a zero of @{term f}:
*}

lemma findzero_zero: "findzero_dom (f, n) \<Longrightarrow> f (findzero f n) = 0"

txt {* \noindent We apply induction as usual, but using the partial induction
  rule: *}

apply (induct f n rule: findzero.pinduct)

txt {* \noindent This gives the following subgoals:

  @{subgoals[display,indent=0]}

  \noindent The hypothesis in our lemma was used to satisfy the first premise in
  the induction rule. However, we also get @{term
  "findzero_dom (f, n)"} as a local assumption in the induction step. This
  allows unfolding @{term "findzero f n"} using the @{text psimps}
  rule, and the rest is trivial.
 *}
apply (simp add: findzero.psimps)
done

text {*
  Proofs about partial functions are often not harder than for total
  functions. Fig.~\ref{findzero_isar} shows a slightly more
  complicated proof written in Isar. It is verbose enough to show how
  partiality comes into play: From the partial induction, we get an
  additional domain condition hypothesis. Observe how this condition
  is applied when calls to @{term findzero} are unfolded.
*}

text_raw {*
\begin{figure}
\hrule\vspace{6pt}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
*}
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
    with `f n \<noteq> 0` show ?thesis by simp
  next
    assume "x \<in> {Suc n ..< findzero f n}"
    with dom and `f n \<noteq> 0` have "x \<in> {Suc n ..< findzero f (Suc n)}" by (simp add: findzero.psimps)
    with IH and `f n \<noteq> 0`
    show ?thesis by simp
  qed
qed
text_raw {*
\isamarkupfalse\isabellestyle{tt}
\end{minipage}\vspace{6pt}\hrule
\caption{A proof about a partial function}\label{findzero_isar}
\end{figure}
*}

subsection {* Partial termination proofs *}

text {*
  Now that we have proved some interesting properties about our
  function, we should turn to the domain predicate and see if it is
  actually true for some values. Otherwise we would have just proved
  lemmas with @{term False} as a premise.

  Essentially, we need some introduction rules for @{text
  findzero_dom}. The function package can prove such domain
  introduction rules automatically. But since they are not used very
  often (they are almost never needed if the function is total), this
  functionality is disabled by default for efficiency reasons. So we have to go
  back and ask for them explicitly by passing the @{text
  "(domintros)"} option to the function package:

\vspace{1ex}
\noindent\cmd{function} @{text "(domintros) findzero :: \"(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\""}\\%
\cmd{where}\isanewline%
\ \ \ldots\\

  \noindent Now the package has proved an introduction rule for @{text findzero_dom}:
*}

thm findzero.domintros

text {*
  @{thm[display] findzero.domintros}

  Domain introduction rules allow to show that a given value lies in the
  domain of a function, if the arguments of all recursive calls
  are in the domain as well. They allow to do a \qt{single step} in a
  termination proof. Usually, you want to combine them with a suitable
  induction principle.

  Since our function increases its argument at recursive calls, we
  need an induction principle which works \qt{backwards}. We will use
  @{text inc_induct}, which allows to do induction from a fixed number
  \qt{downwards}:

  \begin{center}@{thm inc_induct}\hfill(@{text "inc_induct"})\end{center}

  Figure \ref{findzero_term} gives a detailed Isar proof of the fact
  that @{text findzero} terminates if there is a zero which is greater
  or equal to @{term n}. First we derive two useful rules which will
  solve the base case and the step case of the induction. The
  induction is then straightforward, except for the unusual induction
  principle.

*}

text_raw {*
\begin{figure}
\hrule\vspace{6pt}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
*}
lemma findzero_termination:
  assumes "x \<ge> n" and "f x = 0"
  shows "findzero_dom (f, n)"
proof - 
  have base: "findzero_dom (f, x)"
    by (rule findzero.domintros) (simp add:`f x = 0`)

  have step: "\<And>i. findzero_dom (f, Suc i) 
    \<Longrightarrow> findzero_dom (f, i)"
    by (rule findzero.domintros) simp

  from `x \<ge> n` show ?thesis
  proof (induct rule:inc_induct)
    show "findzero_dom (f, x)" by (rule base)
  next
    fix i assume "findzero_dom (f, Suc i)"
    thus "findzero_dom (f, i)" by (rule step)
  qed
qed      
text_raw {*
\isamarkupfalse\isabellestyle{tt}
\end{minipage}\vspace{6pt}\hrule
\caption{Termination proof for @{text findzero}}\label{findzero_term}
\end{figure}
*}
      
text {*
  Again, the proof given in Fig.~\ref{findzero_term} has a lot of
  detail in order to explain the principles. Using more automation, we
  can also have a short proof:
*}

lemma findzero_termination_short:
  assumes zero: "x >= n" 
  assumes [simp]: "f x = 0"
  shows "findzero_dom (f, n)"
using zero
by (induct rule:inc_induct) (auto intro: findzero.domintros)
    
text {*
  \noindent It is simple to combine the partial correctness result with the
  termination lemma:
*}

lemma findzero_total_correctness:
  "f x = 0 \<Longrightarrow> f (findzero f 0) = 0"
by (blast intro: findzero_zero findzero_termination)

subsection {* Definition of the domain predicate *}

text {*
  Sometimes it is useful to know what the definition of the domain
  predicate looks like. Actually, @{text findzero_dom} is just an
  abbreviation:

  @{abbrev[display] findzero_dom}

  The domain predicate is the \emph{accessible part} of a relation @{const
  findzero_rel}, which was also created internally by the function
  package. @{const findzero_rel} is just a normal
  inductive predicate, so we can inspect its definition by
  looking at the introduction rules @{text findzero_rel.intros}.
  In our case there is just a single rule:

  @{thm[display] findzero_rel.intros}

  The predicate @{const findzero_rel}
  describes the \emph{recursion relation} of the function
  definition. The recursion relation is a binary relation on
  the arguments of the function that relates each argument to its
  recursive calls. In general, there is one introduction rule for each
  recursive call.

  The predicate @{term "accp findzero_rel"} is the accessible part of
  that relation. An argument belongs to the accessible part, if it can
  be reached in a finite number of steps (cf.~its definition in @{text
  "Wellfounded.thy"}).

  Since the domain predicate is just an abbreviation, you can use
  lemmas for @{const accp} and @{const findzero_rel} directly. Some
  lemmas which are occasionally useful are @{text accpI}, @{text
  accp_downward}, and of course the introduction and elimination rules
  for the recursion relation @{text "findzero.intros"} and @{text "findzero.cases"}.
*}

section {* Nested recursion *}

text {*
  Recursive calls which are nested in one another frequently cause
  complications, since their termination proof can depend on a partial
  correctness property of the function itself. 

  As a small example, we define the \qt{nested zero} function:
*}

function nz :: "nat \<Rightarrow> nat"
where
  "nz 0 = 0"
| "nz (Suc n) = nz (nz n)"
by pat_completeness auto

text {*
  If we attempt to prove termination using the identity measure on
  naturals, this fails:
*}

termination
  apply (relation "measure (\<lambda>n. n)")
  apply auto

txt {*
  We get stuck with the subgoal

  @{subgoals[display]}

  Of course this statement is true, since we know that @{const nz} is
  the zero function. And in fact we have no problem proving this
  property by induction.
*}
(*<*)oops(*>*)
lemma nz_is_zero: "nz_dom n \<Longrightarrow> nz n = 0"
  by (induct rule:nz.pinduct) (auto simp: nz.psimps)

text {*
  We formulate this as a partial correctness lemma with the condition
  @{term "nz_dom n"}. This allows us to prove it with the @{text
  pinduct} rule before we have proved termination. With this lemma,
  the termination proof works as expected:
*}

termination
  by (relation "measure (\<lambda>n. n)") (auto simp: nz_is_zero)

text {*
  As a general strategy, one should prove the statements needed for
  termination as a partial property first. Then they can be used to do
  the termination proof. This also works for less trivial
  examples. Figure \ref{f91} defines the 91-function, a well-known
  challenge problem due to John McCarthy, and proves its termination.
*}

text_raw {*
\begin{figure}
\hrule\vspace{6pt}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
*}

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

  fix n :: nat assume "\<not> 100 < n" -- "Assumptions for both calls"

  thus "(n + 11, n) \<in> ?R" by simp -- "Inner call"

  assume inner_trm: "f91_dom (n + 11)" -- "Outer call"
  with f91_estimate have "n + 11 < f91 (n + 11) + 11" .
  with `\<not> 100 < n` show "(f91 (n + 11), n) \<in> ?R" by simp
qed

text_raw {*
\isamarkupfalse\isabellestyle{tt}
\end{minipage}
\vspace{6pt}\hrule
\caption{McCarthy's 91-function}\label{f91}
\end{figure}
*}


section {* Higher-Order Recursion *}

text {*
  Higher-order recursion occurs when recursive calls
  are passed as arguments to higher-order combinators such as @{const
  map}, @{term filter} etc.
  As an example, imagine a datatype of n-ary trees:
*}

datatype 'a tree = 
  Leaf 'a 
| Branch "'a tree list"


text {* \noindent We can define a function which swaps the left and right subtrees recursively, using the 
  list functions @{const rev} and @{const map}: *}

fun mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "mirror (Leaf n) = Leaf n"
| "mirror (Branch l) = Branch (rev (map mirror l))"

text {*
  Although the definition is accepted without problems, let us look at the termination proof:
*}

termination proof
  txt {*

  As usual, we have to give a wellfounded relation, such that the
  arguments of the recursive calls get smaller. But what exactly are
  the arguments of the recursive calls when mirror is given as an
  argument to @{const map}? Isabelle gives us the
  subgoals

  @{subgoals[display,indent=0]} 

  So the system seems to know that @{const map} only
  applies the recursive call @{term "mirror"} to elements
  of @{term "l"}, which is essential for the termination proof.

  This knowledge about @{const map} is encoded in so-called congruence rules,
  which are special theorems known to the \cmd{function} command. The
  rule for @{const map} is

  @{thm[display] map_cong}

  You can read this in the following way: Two applications of @{const
  map} are equal, if the list arguments are equal and the functions
  coincide on the elements of the list. This means that for the value 
  @{term "map f l"} we only have to know how @{term f} behaves on
  the elements of @{term l}.

  Usually, one such congruence rule is
  needed for each higher-order construct that is used when defining
  new functions. In fact, even basic functions like @{const
  If} and @{const Let} are handled by this mechanism. The congruence
  rule for @{const If} states that the @{text then} branch is only
  relevant if the condition is true, and the @{text else} branch only if it
  is false:

  @{thm[display] if_cong}
  
  Congruence rules can be added to the
  function package by giving them the @{term fundef_cong} attribute.

  The constructs that are predefined in Isabelle, usually
  come with the respective congruence rules.
  But if you define your own higher-order functions, you may have to
  state and prove the required congruence rules yourself, if you want to use your
  functions in recursive definitions. 
*}
(*<*)oops(*>*)

subsection {* Congruence Rules and Evaluation Order *}

text {* 
  Higher order logic differs from functional programming languages in
  that it has no built-in notion of evaluation order. A program is
  just a set of equations, and it is not specified how they must be
  evaluated. 

  However for the purpose of function definition, we must talk about
  evaluation order implicitly, when we reason about termination.
  Congruence rules express that a certain evaluation order is
  consistent with the logical definition. 

  Consider the following function.
*}

function f :: "nat \<Rightarrow> bool"
where
  "f n = (n = 0 \<or> f (n - 1))"
(*<*)by pat_completeness auto(*>*)

text {*
  For this definition, the termination proof fails. The default configuration
  specifies no congruence rule for disjunction. We have to add a
  congruence rule that specifies left-to-right evaluation order:

  \vspace{1ex}
  \noindent @{thm disj_cong}\hfill(@{text "disj_cong"})
  \vspace{1ex}

  Now the definition works without problems. Note how the termination
  proof depends on the extra condition that we get from the congruence
  rule.

  However, as evaluation is not a hard-wired concept, we
  could just turn everything around by declaring a different
  congruence rule. Then we can make the reverse definition:
*}

lemma disj_cong2[fundef_cong]: 
  "(\<not> Q' \<Longrightarrow> P = P') \<Longrightarrow> (Q = Q') \<Longrightarrow> (P \<or> Q) = (P' \<or> Q')"
  by blast

fun f' :: "nat \<Rightarrow> bool"
where
  "f' n = (f' (n - 1) \<or> n = 0)"

text {*
  \noindent These examples show that, in general, there is no \qt{best} set of
  congruence rules.

  However, such tweaking should rarely be necessary in
  practice, as most of the time, the default set of congruence rules
  works well.
*}

end
