(*  Title:      Doc/IsarAdvanced/Functions/Thy/Fundefs.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

Tutorial for function definitions with the new "function" package.
*)

theory Functions
imports Main
begin

chapter {* Defining Recursive Functions in Isabelle/HOL *}
text {* \cite{isa-tutorial} *}

section {* Function Definition for Dummies *}

text {*
  In most cases, defining a recursive function is just as simple as other definitions:
  *}

fun fib :: "nat \<Rightarrow> nat"
where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

(*<*)termination by lexicographic_order(*>*)

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

text {* 
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
(*<*)termination by lexicographic_order(*>*)

text {* 
  Overlapping patterns are interpreted as "increments" to what is
  already there: The second equation is only meant for the cases where
  the first one does not match. Consequently, Isabelle replaces it
  internally by the remaining cases, making the patterns disjoint.
  This results in the equations @{thm [display] sep.simps[no_vars]}
*}







text {* 
  The equations from function definitions are automatically used in
  simplification:
*}

lemma "fib (Suc (Suc 0)) = (Suc (Suc 0))"
by simp


  

subsection {* Induction *}

text {* FIXME *}


section {* If it does not work *}

text {* 
  Up to now, we were using the \cmd{fun} command, which provides a
  convenient shorthand notation for simple function definitions. In
  this mode, Isabelle tries to solve all the necessary proof obligations
  automatically. If a proof does not go through, the definition is
  rejected. This can mean that the definition is indeed faulty, like,
  or that the default proof procedures are not smart enough (or
  rather: not designed) to handle the specific definition.
.
  By expanding the abbreviation to the full \cmd{function} command, the
  proof obligations become visible and can be analyzed and solved manually.
*}

(*<*)types "\<tau>" = "nat \<Rightarrow> nat"
(*>*)
fun f :: "\<tau>"
where
  (*<*)"f x = x" (*>*)text {* \vspace{-0.8cm}\emph{equations} *}

text {* \noindent abbreviates *}

function (sequential) fo :: "\<tau>"
where
  (*<*)"fo x = x" (*>*)txt {* \vspace{-0.8cm}\emph{equations} *}
by pat_completeness auto 
termination by lexicographic_order

text {* 
  Some declarations and proofs have now become explicit:

  \begin{enumerate}
  \item The "sequential" option enables the preprocessing of
  pattern overlaps we already saw. Without this option, the equations
  must already be disjoint and complete. The automatic completion only
  works with datatype patterns.

  \item A function definition now produces a proof obligation which
  expresses completeness and compatibility of patterns (We talk about
  this later). The combination of the methods {\tt pat\_completeness} and
  {\tt auto} is used to solve this proof obligation.

  \item A termination proof follows the definition, started by the
  \cmd{termination} command. The {\tt lexicographic\_order} method can prove termination of a
  certain class of functions by searching for a suitable lexicographic combination of size
  measures.
  \end{enumerate}
 *}


section {* Proving termination *}

text {*
  Consider the following function, which sums up natural numbers up to
  @{text "N"}, using a counter @{text "i"}
*}

function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "sum i N = (if i > N then 0 else i + sum (Suc i) N)"
  by pat_completeness auto

text {*
  The {\tt lexicographic\_order} method fails on this example, because none of the
  arguments decreases in the recursive call.

  A more general method for termination proofs is to supply a wellfounded
  relation on the argument type, and to show that the argument
  decreases in every recursive call. 

  The termination argument for @{text "sum"} is based on the fact that
  the \emph{difference} between @{text "i"} and @{text "N"} gets
  smaller in every step, and that the recursion stops when @{text "i"}
  is greater then @{text "n"}. Phrased differently, the expression 
  @{text "N + 1 - i"} decreases in every recursive call.

  We can use this expression as a measure function to construct a
  wellfounded relation, which is a proof of termination:
*}

termination 
  by (auto_term "measure (\<lambda>(i,N). N + 1 - i)")

text {*
  Note that the two (curried) function arguments appear as a pair in
  the measure function. The \cmd{function} command packs together curried
  arguments into a tuple to simplify its internal operation. Hence,
  measure functions and termination relations always work on the
  tupled type.

  Let us complicate the function a little, by adding some more recursive calls:
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
  the value of @{text "N"} and the above difference. The @{text "measures"}
  combinator generalizes @{text "measure"} by taking a list of measure functions.
*}

termination 
  by (auto_term "measures [\<lambda>(i, N). N, \<lambda>(i,N). N + 1 - i]")


section {* Mutual Recursion *}

text {*
  If two or more functions call one another mutually, they have to be defined
  in one step. The simplest example are probably @{text "even"} and @{text "odd"}:
*}
(*<*)hide const even odd(*>*)

function even odd :: "nat \<Rightarrow> bool"
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
  by (auto_term "measure (sum_case (%n. n) (%n. n))")



(* FIXME: Mutual induction *)



section {* Nested recursion *}

text {* FIXME *}

section {* More general patterns *}

text {* FIXME *}




end
