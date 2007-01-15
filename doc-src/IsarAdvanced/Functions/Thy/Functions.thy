(*  Title:      Doc/IsarAdvanced/Functions/Thy/Fundefs.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

Tutorial for function definitions with the new "function" package.
*)

theory Functions
imports Main
begin

chapter {* Defining Recursive Functions in Isabelle/HOL *}

section {* Function Definition for Dummies *}

text {*
  In most cases, defining a recursive function is just as simple as other definitions:
  *}

fun fib :: "nat \<Rightarrow> nat"
where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text {*
  The function always terminates, since the argument of gets smaller in every
  recursive call. Termination is an
  important requirement, since it prevents inconsistencies: From
  the "definition" @{text "f(n) = f(n) + 1"} we could prove 
  @{text "0  = 1"} by subtracting @{text "f(n)"} on both sides.

  Isabelle tries to prove termination automatically when a function is
  defined. We will later look at cases where this fails and see what to
  do then.
*}

subsection {* Pattern matching *}

text {* \label{patmatch}
  Like in functional programming, functions can be defined by pattern
  matching. At the moment we will only consider \emph{datatype
  patterns}, which only consist of datatype constructors and
  variables.

  If patterns overlap, the order of the equations is taken into
  account. The following function inserts a fixed element between any
  two elements of a list:
*}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "sep a (x#y#xs) = x # a # sep a (y # xs)"
| "sep a xs       = xs"

text {* 
  Overlapping patterns are interpreted as "increments" to what is
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

lemma "sep (0::nat) [1, 2, 3] = [1, 0, 2, 0, 3]"
by simp

  

subsection {* Induction *}

text {*

  Isabelle provides customized induction rules for recursive functions.  
  See \cite[\S3.5.4]{isa-tutorial}.
*}


section {* Full form definitions *}

text {* 
  Up to now, we were using the \cmd{fun} command, which provides a
  convenient shorthand notation for simple function definitions. In
  this mode, Isabelle tries to solve all the necessary proof obligations
  automatically. If a proof does not go through, the definition is
  rejected. This can either mean that the definition is indeed faulty,
  or that the default proof procedures are just not smart enough (or
  rather: not designed) to handle the definition.

  By expanding the abbreviated \cmd{fun} to the full \cmd{function}
  command, the proof obligations become visible and can be analyzed or
  solved manually.

\end{isamarkuptext}


\fbox{\parbox{\textwidth}{
\noindent\cmd{fun} @{text "f :: \<tau>"}\\%
\cmd{where}\isanewline%
\ \ {\it equations}\isanewline%
\ \ \quad\vdots
}}

\begin{isamarkuptext}
\vspace*{1em}
\noindent abbreviates
\end{isamarkuptext}

\fbox{\parbox{\textwidth}{
\noindent\cmd{function} @{text "("}\cmd{sequential}@{text ") f :: \<tau>"}\\%
\cmd{where}\isanewline%
\ \ {\it equations}\isanewline%
\ \ \quad\vdots\\%
\cmd{by} @{text "pat_completeness auto"}\\%
\cmd{termination by} @{text "lexicographic_order"}
}}

\begin{isamarkuptext}
  \vspace*{1em}
  \noindent Some declarations and proofs have now become explicit:

  \begin{enumerate}
  \item The \cmd{sequential} option enables the preprocessing of
  pattern overlaps we already saw. Without this option, the equations
  must already be disjoint and complete. The automatic completion only
  works with datatype patterns.

  \item A function definition now produces a proof obligation which
  expresses completeness and compatibility of patterns (We talk about
  this later). The combination of the methods @{text "pat_completeness"} and
  @{text "auto"} is used to solve this proof obligation.

  \item A termination proof follows the definition, started by the
  \cmd{termination} command, which sets up the goal. The @{text
  "lexicographic_order"} method can prove termination of a certain
  class of functions by searching for a suitable lexicographic
  combination of size measures.
 \end{enumerate}
  Whenever a \cmd{fun} command fails, it is usually a good idea to
  expand the syntax to the more verbose \cmd{function} form, to see
  what is actually going on.
 *}


section {* Proving termination *}

text {*
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

  A more general method for termination proofs is to supply a wellfounded
  relation on the argument type, and to show that the argument
  decreases in every recursive call. 

  The termination argument for @{text "sum"} is based on the fact that
  the \emph{difference} between @{text "i"} and @{text "N"} gets
  smaller in every step, and that the recursion stops when @{text "i"}
  is greater then @{text "n"}. Phrased differently, the expression 
  @{text "N + 1 - i"} decreases in every recursive call.

  We can use this expression as a measure function suitable to prove termination.
*}

termination 
by (relation "measure (\<lambda>(i,N). N + 1 - i)") auto

text {*
  The @{text relation} method takes a relation of
  type @{typ "('a \<times> 'a) set"}, where @{typ "'a"} is the argument type of
  the function. If the function has multiple curried arguments, then
  these are packed together into a tuple, as it happened in the above
  example.

  The predefined function @{term_type "measure"} is a very common way of
  specifying termination relations in terms of a mapping into the
  natural numbers.

  After the invocation of @{text "relation"}, we must prove that (a)
  the relation we supplied is wellfounded, and (b) that the arguments
  of recursive calls indeed decrease with respect to the
  relation. These goals are all solved by the subsequent call to
  @{text "auto"}.

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


section {* Mutual Recursion *}

text {*
  If two or more functions call one another mutually, they have to be defined
  in one step. The simplest example are probably @{text "even"} and @{text "odd"}:
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
  To solve the problem of mutual dependencies, Isabelle internally
  creates a single function operating on the sum
  type. Then the original functions are defined as
  projections. Consequently, termination has to be proved
  simultaneously for both functions, by specifying a measure on the
  sum type: 
*}

termination 
by (relation "measure (\<lambda>x. case x of Inl n \<Rightarrow> n | Inr n \<Rightarrow> n)") 
   auto

subsection {* Induction for mutual recursion *}

text {*

  When functions are mutually recursive, proving properties about them
  generally requires simultaneous induction. The induction rules
  generated from the definitions reflect this.

  Let us prove something about @{const even} and @{const odd}:
*}

lemma 
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
  presburger arithmethic.
  
*}

apply presburger
apply presburger
done

text {*
  Even if we were just interested in one of the statements proved by
  simultaneous induction, the other ones may be necessary to
  strengthen the induction hypothesis. If we had left out the statement
  about @{const odd} (by substituting it with @{term "True"}, our
  proof would have failed:
*}

lemma 
  "even n = (n mod 2 = 0)"
  "True"
apply (induct n rule: even_odd.induct)

txt {*
  \noindent Now the third subgoal is a dead end, since we have no
  useful induction hypothesis:

  @{subgoals[display,indent=0]} 
*}

oops

section {* More general patterns *}

subsection {* Avoiding pattern splitting *}

text {*

  Up to now, we used pattern matching only on datatypes, and the
  patterns were always disjoint and complete, and if they weren't,
  they were made disjoint automatically like in the definition of
  @{const "sep"} in \S\ref{patmatch}.

  This splitting can significantly increase the number of equations
  involved, and is not always necessary. The following simple example
  shows the problem:
  
  Suppose we are modelling incomplete knowledge about the world by a
  three-valued datatype, which has values for @{term "T"}, @{term "F"}
  and @{term "X"} for true, false and uncertain propositions. 
*}

datatype P3 = T | F | X

text {* Then the conjunction of such values can be defined as follows: *}

fun And :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And T p = p"
  "And p T = p"
  "And p F = F"
  "And F p = F"
  "And X X = X"


text {* 
  This definition is useful, because the equations can directly be used
  as rules to simplify expressions. But the patterns overlap, e.g.~the
  expression @{term "And T T"} is matched by the first two
  equations. By default, Isabelle makes the patterns disjoint by
  splitting them up, producing instances:
*}

thm And.simps

text {*
  @{thm[indent=4] And.simps}
  
  \vspace*{1em}
  \noindent There are several problems with this approach:

  \begin{enumerate}
  \item When datatypes have many constructors, there can be an
  explosion of equations. For @{const "And"}, we get seven instead of
  five equation, which can be tolerated, but this is just a small
  example.

  \item Since splitting makes the equations "more special", they
  do not always match in rewriting. While the term @{term "And x F"}
  can be simplified to @{term "F"} by the original specification, a
  (manual) case split on @{term "x"} is now necessary.

  \item The splitting also concerns the induction rule @{text
  "And.induct"}. Instead of five premises it now has seven, which
  means that our induction proofs will have more cases.

  \item In general, it increases clarity if we get the same definition
  back which we put in.
  \end{enumerate}

  On the other hand, a definition needs to be consistent and defining
  both @{term "f x = True"} and @{term "f x = False"} is a bad
  idea. So if we don't want Isabelle to mangle our definitions, we
  will have to prove that this is not necessary. By using the full
  definition form withour the \cmd{sequential} option, we get this
  behaviour: 
*}

function And2 :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And2 T p = p"
  "And2 p T = p"
  "And2 p F = F"
  "And2 F p = F"
  "And2 X X = X"

txt {*
  Now it is also time to look at the subgoals generated by a
  function definition. In this case, they are:

  @{subgoals[display,indent=0]} 

  The first subgoal expresses the completeness of the patterns. It has
  the form of an elimination rule and states that every @{term x} of
  the function's input type must match one of the patterns. It could
  be equivalently stated as a disjunction of existential statements: 
@{term "(\<exists>p. x = (T, p)) \<or> (\<exists>p. x = (p, T)) \<or> (\<exists>p. x = (p, F)) \<or>
  (\<exists>p. x = (F, p)) \<or> (x = (X, X))"} If the patterns just involve
  datatypes, we can solve it with the @{text "pat_completeness"} method:
*}

apply pat_completeness

txt {*
  The remaining subgoals express \emph{pattern compatibility}. We do
  allow that a value is matched by more than one patterns, but in this
  case, the result (i.e.~the right hand sides of the equations) must
  also be equal. For each pair of two patterns, there is one such
  subgoal. Usually this needs injectivity of the constructors, which
  is used automatically by @{text "auto"}.
*}

by auto


subsection {* Non-constructor patterns *}

text {* FIXME *}


subsection {* Non-constructor patterns *}

text {* FIXME *}






section {* Partiality *}

text {* 
  In HOL, all functions are total. A function @{term "f"} applied to
  @{term "x"} always has a value @{term "f x"}, and there is no notion
  of undefinedness. 

  FIXME
*}



  
section {* Nested recursion *}

text {*
  





 FIXME *}






end
