(*  Title:      Doc/IsarAdvanced/Functions/Thy/Fundefs.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

Tutorial for function definitions with the new "function" package.
*)

theory Functions
imports Main
begin

section {* Function Definition for Dummies *}

text {*
  In most cases, defining a recursive function is just as simple as other definitions:

  Like in functional programming, a function definition consists of a 

*}

fun fib :: "nat \<Rightarrow> nat"
where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text {*
  The syntax is rather self-explanatory: We introduce a function by
  giving its name, its type and a set of defining recursive
  equations. 
*}





text {*
  The function always terminates, since its argument gets smaller in
  every recursive call. Termination is an important requirement, since
  it prevents inconsistencies: From the "definition" @{text "f(n) =
  f(n) + 1"} we could prove @{text "0 = 1"} by subtracting @{text
  "f(n)"} on both sides.

  Isabelle tries to prove termination automatically when a function is
  defined. We will later look at cases where this fails and see what to
  do then.
*}

subsection {* Pattern matching *}

text {* \label{patmatch}
  Like in functional programming, we can use pattern matching to
  define functions. At the moment we will only consider \emph{constructor
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

termination sum
by (relation "measure (\<lambda>(i,N). N + 1 - i)") auto

text {*
  The \cmd{termination} command sets up the termination goal for the
  specified function @{text "sum"}. If the function name is omitted it
  implicitly refers to the last function definition.

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

subsection {* Manual Termination Proofs *}

text {*
  The @{text relation} method is often useful, but not
  necessary. Since termination proofs are just normal Isabelle proofs,
  they can also be carried out manually: 
*}

function id :: "nat \<Rightarrow> nat"
where
  "id 0 = 0"
| "id (Suc n) = Suc (id n)"
by pat_completeness auto

termination
proof 
  show "wf less_than" ..
next
  fix n show "(n, Suc n) \<in> less_than" by simp
qed

text {*
  Of course this is just a trivial example, but manual proofs can
  sometimes be the only choice if faced with very hard termination problems.
*}


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
  three-valued datatype, which has values @{term "T"}, @{term "F"}
  and @{term "X"} for true, false and uncertain propositions, respectively. 
*}

datatype P3 = T | F | X

text {* Then the conjunction of such values can be defined as follows: *}

fun And :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And T p = p"
| "And p T = p"
| "And p F = F"
| "And F p = F"
| "And X X = X"


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
  \noindent There are several problems with this:

  \begin{enumerate}
  \item When datatypes have many constructors, there can be an
  explosion of equations. For @{const "And"}, we get seven instead of
  five equations, which can be tolerated, but this is just a small
  example.

  \item Since splitting makes the equations "less general", they
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
  definition form without the \cmd{sequential} option, we get this
  behaviour: 
*}

function And2 :: "P3 \<Rightarrow> P3 \<Rightarrow> P3"
where
  "And2 T p = p"
| "And2 p T = p"
| "And2 p F = F"
| "And2 F p = F"
| "And2 X X = X"

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




section {* Partiality *}

text {* 
  In HOL, all functions are total. A function @{term "f"} applied to
  @{term "x"} always has a value @{term "f x"}, and there is no notion
  of undefinedness. 
  
  This property of HOL is the reason why we have to do termination
  proofs when defining functions: The termination proof justifies the
  definition of the function by wellfounded recursion.

  However, the \cmd{function} package still supports partiality. Let's
  look at the following function which searches for a zero in the
  function f. 
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
  terminates: the \emph{domain} of the function. In Isabelle/HOL, a
  partial function is just a total function with an additional domain
  predicate. Like with total functions, we get simplification and
  induction rules, but they are guarded by the domain conditions and
  called @{text psimps} and @{text pinduct}:
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
  As already mentioned, HOL does not support true partiality. All we
  are doing here is using some tricks to make a total function appear
  as if it was partial. We can still write the term @{term "findzero
  (\<lambda>x. 1) 0"} and like any other term of type @{typ nat} it is equal
  to some natural number, although we might not be able to find out
  which one (we will discuss this further in \S\ref{default}). The
  function is \emph{underdefined}.

  But it is enough defined to prove something about it. We can prove
  that if @{term "findzero f n"}
  it terminates, it indeed returns a zero of @{term f}:
*}

lemma findzero_zero: "findzero_dom (f, n) \<Longrightarrow> f (findzero f n) = 0"

txt {* We apply induction as usual, but using the partial induction
  rule: *}

apply (induct f n rule: findzero.pinduct)

txt {* This gives the following subgoals:

  @{subgoals[display,indent=0]}

  The premise in our lemma was used to satisfy the first premise in
  the induction rule. However, now we can also use @{term
  "findzero_dom (f, n)"} as an assumption in the induction step. This
  allows to unfold @{term "findzero f n"} using the @{text psimps}
  rule, and the rest is trivial. Since @{text psimps} rules carry the
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
\begin{center}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
*}
lemma "\<lbrakk>findzero_dom (f, n); x \<in> {n ..< findzero f n}\<rbrakk> \<Longrightarrow> f x \<noteq> 0"
proof (induct rule: findzero.pinduct)
  fix f n assume dom: "findzero_dom (f, n)"
    and IH: "\<lbrakk>f n \<noteq> 0; x \<in> {Suc n..<findzero f (Suc n)}\<rbrakk>
             \<Longrightarrow> f x \<noteq> 0"
    and x_range: "x \<in> {n..<findzero f n}"
  
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
    assume "x \<in> {Suc n..<findzero f n}"
    with dom and `f n \<noteq> 0` have "x \<in> {Suc n ..< findzero f (Suc n)}"
      by simp
    with IH and `f n \<noteq> 0`
    show ?thesis by simp
  qed
qed
text_raw {*
\isamarkupfalse\isabellestyle{tt}
\end{minipage}\end{center}
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
  often (they are almost never needed if the function is total), they
  are disabled by default for efficiency reasons. So we have to go
  back and ask for them explicitly by passing the @{text
  "(domintros)"} option to the function package:

\noindent\cmd{function} @{text "(domintros) findzero :: \"(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\""}\\%
\cmd{where}\isanewline%
\ \ \ldots\\
\cmd{by} @{text "pat_completeness auto"}\\%


  Now the package has proved an introduction rule for @{text findzero_dom}:
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

  @{thm[display] inc_induct}

  Fig.~\ref{findzero_term} gives a detailed Isar proof of the fact
  that @{text findzero} terminates if there is a zero which is greater
  or equal to @{term n}. First we derive two useful rules which will
  solve the base case and the step case of the induction. The
  induction is then straightforward, except for the unusal induction
  principle.

*}

text_raw {*
\begin{figure}
\begin{center}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
*}
lemma findzero_termination:
  assumes "x >= n" 
  assumes "f x = 0"
  shows "findzero_dom (f, n)"
proof - 
  have base: "findzero_dom (f, x)"
    by (rule findzero.domintros) (simp add:`f x = 0`)

  have step: "\<And>i. findzero_dom (f, Suc i) 
    \<Longrightarrow> findzero_dom (f, i)"
    by (rule findzero.domintros) simp

  from `x \<ge> n`
  show ?thesis
  proof (induct rule:inc_induct)
    show "findzero_dom (f, x)"
      by (rule base)
  next
    fix i assume "findzero_dom (f, Suc i)"
    thus "findzero_dom (f, i)"
      by (rule step)
  qed
qed      
text_raw {*
\isamarkupfalse\isabellestyle{tt}
\end{minipage}\end{center}
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
  It is simple to combine the partial correctness result with the
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

  The domain predicate is the accessible part of a relation @{const
  findzero_rel}, which was also created internally by the function
  package. @{const findzero_rel} is just a normal
  inductively defined predicate, so we can inspect its definition by
  looking at the introduction rules @{text findzero_rel.intros}.
  In our case there is just a single rule:

  @{thm[display] findzero_rel.intros}

  The relation @{const findzero_rel}, expressed as a binary predicate,
  describes the \emph{recursion relation} of the function
  definition. The recursion relation is a binary relation on
  the arguments of the function that relates each argument to its
  recursive calls. In general, there is one introduction rule for each
  recursive call.

  The predicate @{term "acc findzero_rel"} is the \emph{accessible part} of
  that relation. An argument belongs to the accessible part, if it can
  be reached in a finite number of steps. 

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
  concrete @{term "(x \<ge> n \<and> f x = 0)"}, but the condition is still
  there and it won't go away soon. 

  In particular, the domain predicate guard the unfolding of our
  function, since it is there as a condition in the @{text psimp}
  rules. 

  On the other hand, we must be happy about the domain predicate,
  since it guarantees that all this is at all possible without losing
  consistency. 

  Now there is an important special case: We can actually get rid
  of the condition in the simplification rules, \emph{if the function
  is tail-recursive}. The reason is that for all tail-recursive
  equations there is a total function satisfying them, even if they
  are non-terminating. 

  The function package internally does the right construction and can
  derive the unconditional simp rules, if we ask it to do so. Luckily,
  our @{const "findzero"} function is tail-recursive, so we can just go
  back and add another option to the \cmd{function} command:

\noindent\cmd{function} @{text "(domintros, tailrec) findzero :: \"(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\""}\\%
\cmd{where}\isanewline%
\ \ \ldots\\%

  
  Now, we actually get the unconditional simplification rules, even
  though the function is partial:
*}

thm findzero.simps

text {*
  @{thm[display] findzero.simps}

  Of course these would make the simplifier loop, so we better remove
  them from the simpset:
*}

declare findzero.simps[simp del]


text {* \fixme{Code generation ???} *}

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
  examples. Figure \ref{f91} defines the well-known 91-function by
  McCarthy \cite{?} and proves its termination.
*}

text_raw {*
\begin{figure}
\begin{center}
\begin{minipage}{0.8\textwidth}
\isabellestyle{it}
\isastyle\isamarkuptrue
*}

function f91 :: "nat => nat"
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
\end{minipage}\end{center}
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
  What happens if the congruence rule for @{const If} is
  disabled by declaring @{text "if_cong[fundef_cong del]"}?
  \end{exercise}

  Note that in some cases there is no \qt{best} congruence rule.
  \fixme

*}







section {* Appendix: Predefined Congruence Rules *}

(*<*)
syntax (Rule output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{\mbox{>_\<^raw:}}>\<^raw:{\mbox{>_\<^raw:}}>")

  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^raw:\mbox{}\inferrule{>_\<^raw:}>\<^raw:{\mbox{>_\<^raw:}}>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("\<^raw:\mbox{>_\<^raw:}\\>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^raw:\mbox{>_\<^raw:}>")

definition 
FixImp :: "prop \<Rightarrow> prop \<Rightarrow> prop" 
where
  "FixImp (PROP A) (PROP B) \<equiv> (PROP A \<Longrightarrow> PROP B)"
notation (output)
  FixImp (infixr "\<Longrightarrow>" 1)

setup {*
let
  val fix_imps = map_aterms (fn Const ("==>", T) => Const ("Functions.FixImp", T) | t => t)
  fun transform t = Logic.list_implies (map fix_imps (Logic.strip_imp_prems t), Logic.strip_imp_concl t)
in
  TermStyle.add_style "topl" (K transform)
end
*}
(*>*)

subsection {* Basic Control Structures *}

text {*

@{thm_style[mode=Rule] topl if_cong}

@{thm_style [mode=Rule] topl let_cong}

*}

subsection {* Data Types *}

text {*

For each \cmd{datatype} definition, a congruence rule for the case
  combinator is registeres automatically. Here are the rules for
  @{text "nat"} and @{text "list"}:

\begin{center}@{thm_style[mode=Rule] topl nat.case_cong}\end{center}

\begin{center}@{thm_style[mode=Rule] topl list.case_cong}\end{center}

*}

subsection {* List combinators *}


text {*

@{thm_style[mode=Rule] topl map_cong}

@{thm_style[mode=Rule] topl filter_cong}

@{thm_style[mode=Rule] topl foldr_cong}

@{thm_style[mode=Rule] topl foldl_cong}

Similar: takewhile, dropwhile

*}

subsection {* Sets *}


text {*

@{thm_style[mode=Rule] topl ball_cong}

@{thm_style[mode=Rule] topl bex_cong}

@{thm_style[mode=Rule] topl UN_cong}

@{thm_style[mode=Rule] topl INT_cong}

@{thm_style[mode=Rule] topl image_cong}


*}






end
