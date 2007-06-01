(*  Title:      Doc/IsarAdvanced/Functions/Thy/Fundefs.thy
    ID:         $Id$
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
  giving its name, its type and a set of defining recursive
  equations. Note that the function is not primitive recursive.
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
  (linear occurrences of) variables.

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
  The equations from function definitions are automatically used in
  simplification:
*}

lemma "sep 0 [1, 2, 3] = [1, 0, 2, 0, 3]"
by simp

subsection {* Induction *}

text {*

  Isabelle provides customized induction rules for recursive functions.  
  See \cite[\S3.5.4]{isa-tutorial}. \fixme{Cases?}


  With the \cmd{fun} command, you can define about 80\% of the
  functions that occur in practice. The rest of this tutorial explains
  the remaining 20\%.
*}


section {* fun vs.\ function *}

text {* 
  The \cmd{fun} command provides a
  convenient shorthand notation for simple function definitions. In
  this mode, Isabelle tries to solve all the necessary proof obligations
  automatically. If a proof fails, the definition is
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
\left[\;\begin{minipage}{0.45\textwidth}\vspace{6pt}
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
  pattern overlaps we already saw. Without this option, the equations
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
  The @{text "lexicographic_order"} method can prove termination of a
  certain class of functions by searching for a suitable lexicographic
  combination of size measures. Of course, not all functions have such
  a simple termination argument.
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
  arguments decreases in the recursive call.
  % FIXME: simps and induct only appear after "termination"

  The easiest way of doing termination proofs is to supply a wellfounded
  relation on the argument type, and to show that the argument
  decreases in every recursive call. 

  The termination argument for @{text "sum"} is based on the fact that
  the \emph{difference} between @{text "i"} and @{text "N"} gets
  smaller in every step, and that the recursion stops when @{text "i"}
  is greater then @{text "n"}. Phrased differently, the expression 
  @{text "N + 1 - i"} decreases in every recursive call.

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

  The predefined function @{term_type "measure"} constructs a
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
*** Could not find lexicographic termination order:\newline
*** \ \ \ \ 1\ \ 2  \newline
*** a:  N   <= \newline
*** Calls:\newline
*** a) @{text "(a, x # xs) -->> (x + a, x # xs)"}\newline
*** Measures:\newline
*** 1) @{text "\<lambda>x. size (fst x)"}\newline
*** 2) @{text "\<lambda>x. size (snd x)"}\newline
*** Unfinished subgoals:\newline
*** @{text "\<And>a x xs."}\newline
*** \quad @{text "(x. size (fst x)) (x + a, x # xs)"}\newline
***  \quad @{text "\<le> (\<lambda>x. size (fst x)) (a, x # xs)"}\newline
***  @{text "1. \<And>x. x = 0"}\newline
*** At command "fun".\newline
\end{isabelle}
*}


text {*


  The the key to this error message is the matrix at the top. The rows
  of that matrix correspond to the different recursive calls (In our
  case, there is just one). The columns are the function's arguments 
  (expressed through different measure functions, which map the
  argument tuple to a natural number). 

  The contents of the matrix summarize what is known about argument
  descents: The second argument has a weak descent (@{text "<="}) at the
  recursive call, and for the first argument nothing could be proved,
  which is expressed by @{text N}. In general, there are the values
  @{text "<"}, @{text "<="} and @{text "N"}.

  For the failed proof attempts, the unfinished subgoals are also
  printed. Looking at these will often point us to a missing lemma.

%  As a more real example, here is quicksort:
*}
(*
function qs :: "nat list \<Rightarrow> nat list"
where
  "qs [] = []"
| "qs (x#xs) = qs [y\<in>xs. y < x] @ x # qs [y\<in>xs. y \<ge> x]"
by pat_completeness auto

termination apply lexicographic_order

text {* If we try @{text "lexicographic_order"} method, we get the
  following error *}
termination by (lexicographic_order simp:l2)

lemma l: "x \<le> y \<Longrightarrow> x < Suc y" by arith

function 

*)

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

  \noindent These can be handeled by the descision procedure for
  arithmethic.
  
*}

apply presburger -- {* \fixme{arith} *}
apply presburger
done

text {*
  In proofs like this, the simultaneous induction is really essential:
  Even if we are just interested in one of the results, the other
  one is necessary to strengthen the induction hypothesis. If we leave
  out the statement about @{const odd} (by substituting it with @{term
  "True"}), the same proof fails:
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

subsection {* Avoiding automatic pattern splitting *}

text {*

  Up to now, we used pattern matching only on datatypes, and the
  patterns were always disjoint and complete, and if they weren't,
  they were made disjoint automatically like in the definition of
  @{const "sep"} in \S\ref{patmatch}.

  This automatic splitting can significantly increase the number of
  equations involved, and this is not always desirable. The following
  example shows the problem:
  
  Suppose we are modelling incomplete knowledge about the world by a
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
  as simplifcation rules rules. But the patterns overlap: For example,
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
  (\<exists>p. x = (F, p)) \<or> (x = (X, X))"}.}. If the patterns just involve
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


subsection {* Non-constructor patterns *}

text {*
  Most of Isabelle's basic types take the form of inductive data types
  with constructors. However, this is not true for all of them. The
  integers, for instance, are defined using the usual algebraic
  quotient construction, thus they are not an \qt{official} datatype.

  Of course, we might want to do pattern matching there, too. So



*}

function Abs :: "int \<Rightarrow> nat"
where
  "Abs (int n) = n"
| "Abs (- int (Suc n)) = n"
by (erule int_cases) auto
termination by (relation "{}") simp

text {*
  This kind of matching is again justified by the proof of pattern
  completeness and compatibility. Here, the existing lemma @{text
  int_cases} is used:

  \begin{center}@{thm int_cases}\hfill(@{text "int_cases"})\end{center}
*}
text {*
  One well-known instance of non-constructor patterns are the
  so-called \emph{$n+k$-patterns}, which are a little controversial in
  the functional programming world. Here is the initial fibonacci
  example with $n+k$-patterns:
*}

function fib2 :: "nat \<Rightarrow> nat"
where
  "fib2 0 = 1"
| "fib2 1 = 1"
| "fib2 (n + 2) = fib2 n + fib2 (Suc n)"

(*<*)ML "goals_limit := 1"(*>*)
txt {*
  The proof obligation for pattern completeness states that every natural number is
  either @{term "0::nat"}, @{term "1::nat"} or @{term "n +
  (2::nat)"}:

  @{subgoals[display,indent=0]}

  This is an arithmetic triviality, but unfortunately the
  @{text arith} method cannot handle this specific form of an
  elimination rule. We have to do a case split on @{text P} first,
  which can be conveniently done using the @{text
  classical} rule. Pattern compatibility and termination are automatic as usual.
*}
(*<*)ML "goals_limit := 10"(*>*)

apply (rule classical, simp, arith)
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
by (rule classical, simp) arith+
termination by (relation "{}") simp

text {*
  This general notion of pattern matching gives you the full freedom
  of mathematical specifications. However, as always, freedom should
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
by (rule classical, auto, arith)
termination by lexicographic_order

text {*
  By now, you can probably guess what the proof obligations for the
  pattern completeness and compatibility look like. 

  Again, functions with conditional patterns are not supported by the
  code generator.
*}


subsection {* Pattern matching on strings *}

text {*
  As strings (as lists of characters) are normal data types, pattern
  matching on them is possible, but somewhat problematic. Consider the
  following definition:

\end{isamarkuptext}
\noindent\cmd{fun} @{text "check :: \"string \<Rightarrow> bool\""}\\%
\cmd{where}\\%
\hspace*{2ex}@{text "\"check (''good'') = True\""}\\%
@{text "| \"check s = False\""}
\begin{isamarkuptext}

  An invocation of the above \cmd{fun} command does not
  terminate. What is the problem? Strings are lists of characters, and
  characters are a data type with a lot of constructors. Splitting the
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

function (*<*)(domintros, tailrec)(*>*)findzero :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "findzero f n = (if f n = 0 then n else findzero f (Suc n))"
by pat_completeness auto
(*<*)declare findzero.simps[simp del](*>*)

text {*
  Clearly, any attempt of a termination proof must fail. And without
  that, we do not get the usual rules @{text "findzero.simp"} and 
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

thm findzero.psimps

text {*
  @{thm[display] findzero.psimps}
*}

thm findzero.pinduct

text {*
  @{thm[display] findzero.pinduct}
*}

text {*
  Remember that all we
  are doing here is use some tricks to make a total function appear
  as if it was partial. We can still write the term @{term "findzero
  (\<lambda>x. 1) 0"} and like any other term of type @{typ nat} it is equal
  to some natural number, although we might not be able to find out
  which one. The function is \emph{underdefined}.

  But it is enough defined to prove something interesting about it. We
  can prove that if @{term "findzero f n"}
  it terminates, it indeed returns a zero of @{term f}:
*}

lemma findzero_zero: "findzero_dom (f, n) \<Longrightarrow> f (findzero f n) = 0"

txt {* We apply induction as usual, but using the partial induction
  rule: *}

apply (induct f n rule: findzero.pinduct)

txt {* This gives the following subgoals:

  @{subgoals[display,indent=0]}

  The hypothesis in our lemma was used to satisfy the first premise in
  the induction rule. However, we also get @{term
  "findzero_dom (f, n)"} as a local assumption in the induction step. This
  allows to unfold @{term "findzero f n"} using the @{text psimps}
  rule, and the rest is trivial. Since the @{text psimps} rules carry the
  @{text "[simp]"} attribute by default, we just need a single step:
 *}
apply simp
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
    with dom have "findzero f n = n" by simp
    with x_range show False by auto
  qed
  
  from x_range have "x = n \<or> x \<in> {Suc n ..< findzero f n}" by auto
  thus "f x \<noteq> 0"
  proof
    assume "x = n"
    with `f n \<noteq> 0` show ?thesis by simp
  next
    assume "x \<in> {Suc n ..< findzero f n}"
    with dom and `f n \<noteq> 0` have "x \<in> {Suc n ..< findzero f (Suc n)}"
      by simp
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
  induction is then straightforward, except for the unusal induction
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
  predicate actually is. Actually, @{text findzero_dom} is just an
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

  The predicate @{term "acc findzero_rel"} is the accessible part of
  that relation. An argument belongs to the accessible part, if it can
  be reached in a finite number of steps (cf.~its definition in @{text
  "Accessible_Part.thy"}).

  Since the domain predicate is just an abbreviation, you can use
  lemmas for @{const acc} and @{const findzero_rel} directly. Some
  lemmas which are occasionally useful are @{text accI}, @{text
  acc_downward}, and of course the introduction and elimination rules
  for the recursion relation @{text "findzero.intros"} and @{text "findzero.cases"}.
*}

(*lemma findzero_nicer_domintros:
  "f x = 0 \<Longrightarrow> findzero_dom (f, x)"
  "findzero_dom (f, Suc x) \<Longrightarrow> findzero_dom (f, x)"
by (rule accI, erule findzero_rel.cases, auto)+
*)
  
subsection {* A Useful Special Case: Tail recursion *}

text {*
  The domain predicate is our trick that allows us to model partiality
  in a world of total functions. The downside of this is that we have
  to carry it around all the time. The termination proof above allowed
  us to replace the abstract @{term "findzero_dom (f, n)"} by the more
  concrete @{term "(x \<ge> n \<and> f x = (0::nat))"}, but the condition is still
  there and can only be discharged for special cases.
  In particular, the domain predicate guards the unfolding of our
  function, since it is there as a condition in the @{text psimp}
  rules. 

  Now there is an important special case: We can actually get rid
  of the condition in the simplification rules, \emph{if the function
  is tail-recursive}. The reason is that for all tail-recursive
  equations there is a total function satisfying them, even if they
  are non-terminating. 

%  A function is tail recursive, if each call to the function is either
%  equal
%
%  So the outer form of the 
%
%if it can be written in the following
%  form:
%  {term[display] "f x = (if COND x then BASE x else f (LOOP x))"}


  The function package internally does the right construction and can
  derive the unconditional simp rules, if we ask it to do so. Luckily,
  our @{const "findzero"} function is tail-recursive, so we can just go
  back and add another option to the \cmd{function} command:

\vspace{1ex}
\noindent\cmd{function} @{text "(domintros, tailrec) findzero :: \"(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\""}\\%
\cmd{where}\isanewline%
\ \ \ldots\\%

  
  \noindent Now, we actually get unconditional simplification rules, even
  though the function is partial:
*}

thm findzero.simps

text {*
  @{thm[display] findzero.simps}

  \noindent Of course these would make the simplifier loop, so we better remove
  them from the simpset:
*}

declare findzero.simps[simp del]

text {* 
  Getting rid of the domain conditions in the simplification rules is
  not only useful because it simplifies proofs. It is also required in
  order to use Isabelle's code generator to generate ML code
  from a function definition.
  Since the code generator only works with equations, it cannot be
  used with @{text "psimp"} rules. Thus, in order to generate code for
  partial functions, they must be defined as a tail recursion.
  Luckily, many functions have a relatively natural tail recursive
  definition.
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
oops

lemma nz_is_zero: "nz_dom n \<Longrightarrow> nz n = 0"
  by (induct rule:nz.pinduct) auto

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
using trm by induct auto

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
  are passed as arguments to higher-order combinators such as @{term
  map}, @{term filter} etc.
  As an example, imagine a data type of n-ary trees:
*}

datatype 'a tree = 
  Leaf 'a 
| Branch "'a tree list"


text {* \noindent We can define a map function for trees, using the predefined
  map function for lists. *}
  
function treemap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
  "treemap f (Leaf n) = Leaf (f n)"
| "treemap f (Branch l) = Branch (map (treemap f) l)"
by pat_completeness auto

text {*
  We do the termination proof manually, to point out what happens
  here: 
*}

termination proof
  txt {*

  As usual, we have to give a wellfounded relation, such that the
  arguments of the recursive calls get smaller. But what exactly are
  the arguments of the recursive calls? Isabelle gives us the
  subgoals

  @{subgoals[display,indent=0]} 

  So Isabelle seems to know that @{const map} behaves nicely and only
  applies the recursive call @{term "treemap f"} to elements
  of @{term "l"}. Before we discuss where this knowledge comes from,
  let us finish the termination proof:
  *}

  show "wf (measure (size o snd))" by simp
next
  fix f l and x :: "'a tree"
  assume "x \<in> set l"
  thus "((f, x), (f, Branch l)) \<in> measure (size o snd)"
    apply simp
    txt {*
      Simplification returns the following subgoal: 

      @{subgoals[display,indent=0]} 

      We are lacking a property about the function @{const
      tree_list_size}, which was generated automatically at the
      definition of the @{text tree} type. We should go back and prove
      it, by induction.
      *}
    oops

  lemma tree_list_size[simp]: "x \<in> set l \<Longrightarrow> size x < Suc (tree_list_size l)"
    by (induct l) auto

  text {* 
    Now the whole termination proof is automatic:
    *}

  termination 
    by lexicographic_order
  

subsection {* Congruence Rules *}

text {*
  Let's come back to the question how Isabelle knows about @{const
  map}.

  The knowledge about map is encoded in so-called congruence rules,
  which are special theorems known to the \cmd{function} command. The
  rule for map is

  @{thm[display] map_cong}

  You can read this in the following way: Two applications of @{const
  map} are equal, if the list arguments are equal and the functions
  coincide on the elements of the list. This means that for the value 
  @{term "map f l"} we only have to know how @{term f} behaves on
  @{term l}.

  Usually, one such congruence rule is
  needed for each higher-order construct that is used when defining
  new functions. In fact, even basic functions like @{const
  If} and @{const Let} are handeled by this mechanism. The congruence
  rule for @{const If} states that the @{text then} branch is only
  relevant if the condition is true, and the @{text else} branch only if it
  is false:

  @{thm[display] if_cong}
  
  Congruence rules can be added to the
  function package by giving them the @{term fundef_cong} attribute.

  Isabelle comes with predefined congruence rules for most of the
  definitions.
  But if you define your own higher-order constructs, you will have to
  come up with the congruence rules yourself, if you want to use your
  functions in recursive definitions. Since the structure of
  congruence rules is a little unintuitive, here are some exercises:
*}
(*<*)
fun mapeven :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "mapeven f [] = []"
| "mapeven f (x#xs) = (if x mod 2 = 0 then f x # mapeven f xs else x #
  mapeven f xs)"
(*>*)
text {*

  \begin{exercise}
    Find a suitable congruence rule for the following function which
  maps only over the even numbers in a list:

  @{thm[display] mapeven.simps}
  \end{exercise}
  
  \begin{exercise}
  Try what happens if the congruence rule for @{const If} is
  disabled by declaring @{text "if_cong[fundef_cong del]"}?
  \end{exercise}

  Note that in some cases there is no \qt{best} congruence rule.
  \fixme{}

*}

end
