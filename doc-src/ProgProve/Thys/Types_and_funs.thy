(*<*)
theory Types_and_funs
imports Main
begin
(*>*)
text{*
\vspace{-5ex}
\section{Type and function definitions}

Type synonyms are abbreviations for existing types, for example
*}

type_synonym string = "char list"

text{*
Type synonyms are expanded after parsing and are not present in internal representation and output. They are mere conveniences for the reader.

\subsection{Datatypes}

The general form of a datatype definition looks like this:
\begin{quote}
\begin{tabular}{@ {}rclcll}
\isacom{datatype} @{text "('a\<^isub>1,\<dots>,'a\<^isub>n)t"}
     & = & $C_1 \ @{text"\""}\tau_{1,1}@{text"\""} \dots @{text"\""}\tau_{1,n_1}@{text"\""}$ \\
     & $|$ & \dots \\
     & $|$ & $C_k \ @{text"\""}\tau_{k,1}@{text"\""} \dots @{text"\""}\tau_{k,n_k}@{text"\""}$
\end{tabular}
\end{quote}
It introduces the constructors \
$C_i :: \tau_{i,1}\Rightarrow \cdots \Rightarrow \tau_{i,n_i} \Rightarrow$~@{text "('a\<^isub>1,\<dots>,'a\<^isub>n)t"} \ and expresses that any value of this type is built from these constructors in a unique manner. Uniqueness is implied by the following
properties of the constructors:
\begin{itemize}
\item \emph{Distinctness:} $C_i\ \ldots \neq C_j\ \dots$ \quad if $i \neq j$
\item \emph{Injectivity:}
\begin{tabular}[t]{l}
 $(C_i \ x_1 \dots x_{n_i} = C_i \ y_1 \dots y_{n_i}) =$\\
 $(x_1 = y_1 \land \dots \land x_{n_i} = y_{n_i})$
\end{tabular}
\end{itemize}
The fact that any value of the datatype is built from the constructors implies
the structural induction rule: to show
$P~x$ for all $x$ of type @{text "('a\<^isub>1,\<dots>,'a\<^isub>n)t"},
one needs to show $P(C_i\ x_1 \dots x_{n_i})$ (for each $i$) assuming
$P(x_j)$ for all $j$ where $\tau_{i,j} =$~@{text "('a\<^isub>1,\<dots>,'a\<^isub>n)t"}.
Distinctness and injectivity are applied automatically by @{text auto}
and other proof methods. Induction must be applied explicitly.

Datatype values can be taken apart with case-expressions, for example
\begin{quote}
\noquotes{@{term[source] "(case xs of [] \<Rightarrow> 0 | x # _ \<Rightarrow> Suc x)"}}
\end{quote}
just like in functional programming languages. Case expressions
must be enclosed in parentheses.

As an example, consider binary trees:
*}

datatype 'a tree = Tip | Node "('a tree)" 'a "('a tree)"

text{* with a mirror function: *}

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

text{* The following lemma illustrates induction: *}

lemma "mirror(mirror t) = t"
apply(induction t)

txt{* yields
@{subgoals[display]}
The induction step contains two induction hypotheses, one for each subtree.
An application of @{text auto} finishes the proof.

A very simple but also very useful datatype is the predefined
@{datatype[display] option}
Its sole purpose is to add a new element @{const None} to an existing
type @{typ 'a}. To make sure that @{const None} is distinct from all the
elements of @{typ 'a}, you wrap them up in @{const Some} and call
the new type @{typ"'a option"}. A typical application is a lookup function
on a list of key-value pairs, often called an association list:
*}
(*<*)
apply auto
done
(*>*)
fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x' = None" |
"lookup ((x,y) # ps) x' = (if x = x' then Some y else lookup ps x')"

text{*
Note that @{text"\<tau>\<^isub>1 * \<tau>\<^isub>2"} is the type of pairs, also written @{text"\<tau>\<^isub>1 \<times> \<tau>\<^isub>2"}.

\subsection{Definitions}

Non recursive functions can be defined as in the following example:
*}

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

text{* Such definitions do not allow pattern matching but only
@{text"f x\<^isub>1 \<dots> x\<^isub>n = t"}, where @{text f} does not occur in @{text t}.

\subsection{Abbreviations}

Abbreviations are similar to definitions:
*}

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n == n * n"

text{* The key difference is that @{const sq'} is only syntactic sugar:
@{term"sq' t"} is replaced by \mbox{@{term"t*t"}} after parsing, and every
occurrence of a term @{term"u*u"} is replaced by \mbox{@{term"sq' u"}} before
printing.  Internally, @{const sq'} does not exist.  This is also the
advantage of abbreviations over definitions: definitions need to be expanded
explicitly (see \autoref{sec:rewr-defs}) whereas abbreviations are already
expanded upon parsing. However, abbreviations should be introduced sparingly:
if abused, they can lead to a confusing discrepancy between the internal and
external view of a term.

\subsection{Recursive functions}
\label{sec:recursive-funs}

Recursive functions are defined with \isacom{fun} by pattern matching
over datatype constructors. The order of equations matters. Just as in
functional programming languages. However, all HOL functions must be
total. This simplifies the logic---terms are always defined---but means
that recursive functions must terminate. Otherwise one could define a
function @{prop"f n = f n + (1::nat)"} and conclude \mbox{@{prop"(0::nat) = 1"}} by
subtracting @{term"f n"} on both sides.

Isabelle automatic termination checker requires that the arguments of
recursive calls on the right-hand side must be strictly smaller than the
arguments on the left-hand side. In the simplest case, this means that one
fixed argument position decreases in size with each recursive call. The size
is measured as the number of constructors (excluding 0-ary ones, e.g.\ @{text
Nil}). Lexicographic combinations are also recognised. In more complicated
situations, the user may have to prove termination by hand. For details
see~\cite{Krauss}.

Functions defined with \isacom{fun} come with their own induction schema
that mirrors the recursion schema and is derived from the termination
order. For example,
*}

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = Suc 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

text{* does not just define @{const div2} but also proves a
customised induction rule:
\[
\inferrule{
\mbox{@{thm (prem 1) div2.induct}}\\
\mbox{@{thm (prem 2) div2.induct}}\\
\mbox{@{thm (prem 3) div2.induct}}}
{\mbox{@{thm (concl) div2.induct[of _ "m"]}}}
\]
This customised induction rule can simplify inductive proofs. For example,
*}

lemma "div2(n+n) = n"
apply(induction n rule: div2.induct)

txt{* yields the 3 subgoals
@{subgoals[display,margin=65]}
An application of @{text auto} finishes the proof.
Had we used ordinary structural induction on @{text n},
the proof would have needed an additional
case distinction in the induction step.

The general case is often called \concept{computation induction},
because the induction follows the (terminating!) computation.
For every defining equation
\begin{quote}
@{text "f(e) = \<dots> f(r\<^isub>1) \<dots> f(r\<^isub>k) \<dots>"}
\end{quote}
where @{text"f(r\<^isub>i)"}, @{text"i=1\<dots>k"}, are all the recursive calls,
the induction rule @{text"f.induct"} contains one premise of the form
\begin{quote}
@{text"P(r\<^isub>1) \<Longrightarrow> \<dots> \<Longrightarrow> P(r\<^isub>k) \<Longrightarrow> P(e)"}
\end{quote}
If @{text "f :: \<tau>\<^isub>1 \<Rightarrow> \<dots> \<Rightarrow> \<tau>\<^isub>n \<Rightarrow> \<tau>"} then @{text"f.induct"} is applied like this:
\begin{quote}
\isacom{apply}@{text"(induction x\<^isub>1 \<dots> x\<^isub>n rule: f.induct)"}
\end{quote}
where typically there is a call @{text"f x\<^isub>1 \<dots> x\<^isub>n"} in the goal.
But note that the induction rule does not mention @{text f} at all,
except in its name, and is applicable independently of @{text f}.

\section{Induction heuristics}

We have already noted that theorems about recursive functions are proved by
induction. In case the function has more than one argument, we have followed
the following heuristic in the proofs about the append function:
\begin{quote}
\emph{Perform induction on argument number $i$\\
 if the function is defined by recursion on argument number $i$.}
\end{quote}
The key heuristic, and the main point of this section, is to
\emph{generalise the goal before induction}.
The reason is simple: if the goal is
too specific, the induction hypothesis is too weak to allow the induction
step to go through. Let us illustrate the idea with an example.

Function @{const rev} has quadratic worst-case running time
because it calls append for each element of the list and
append is linear in its first argument.  A linear time version of
@{const rev} requires an extra argument where the result is accumulated
gradually, using only~@{text"#"}:
*}
(*<*)
apply auto
done
(*>*)
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev []     ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

text{* The behaviour of @{const itrev} is simple: it reverses
its first argument by stacking its elements onto the second argument,
and returning that second argument when the first one becomes
empty. Note that @{const itrev} is tail-recursive: it can be
compiled into a loop, no stack is necessary for executing it.

Naturally, we would like to show that @{const itrev} does indeed reverse
its first argument provided the second one is empty:
*}

lemma "itrev xs [] = rev xs"

txt{* There is no choice as to the induction variable:
*}

apply(induction xs)
apply(auto)

txt{*
Unfortunately, this attempt does not prove
the induction step:
@{subgoals[display,margin=70]}
The induction hypothesis is too weak.  The fixed
argument,~@{term"[]"}, prevents it from rewriting the conclusion.  
This example suggests a heuristic:
\begin{quote}
\emph{Generalise goals for induction by replacing constants by variables.}
\end{quote}
Of course one cannot do this na\"{\i}vely: @{prop"itrev xs ys = rev xs"} is
just not true.  The correct generalisation is
*};
(*<*)oops;(*>*)
lemma "itrev xs ys = rev xs @ ys"
(*<*)apply(induction xs, auto)(*>*)
txt{*
If @{text ys} is replaced by @{term"[]"}, the right-hand side simplifies to
@{term"rev xs"}, as required.
In this instance it was easy to guess the right generalisation.
Other situations can require a good deal of creativity.  

Although we now have two variables, only @{text xs} is suitable for
induction, and we repeat our proof attempt. Unfortunately, we are still
not there:
@{subgoals[display,margin=65]}
The induction hypothesis is still too weak, but this time it takes no
intuition to generalise: the problem is that the @{text ys}
in the induction hypothesis is fixed,
but the induction hypothesis needs to be applied with
@{term"a # ys"} instead of @{text ys}. Hence we prove the theorem
for all @{text ys} instead of a fixed one. We can instruct induction
to perform this generalisation for us by adding @{text "arbitrary: ys"}.
*}
(*<*)oops
lemma "itrev xs ys = rev xs @ ys"
(*>*)
apply(induction xs arbitrary: ys)

txt{* The induction hypothesis in the induction step is now universally quantified over @{text ys}:
@{subgoals[display,margin=65]}
Thus the proof succeeds:
*}

apply auto
done

text{*
This leads to another heuristic for generalisation:
\begin{quote}
\emph{Generalise induction by generalising all free
variables\\ {\em(except the induction variable itself)}.}
\end{quote}
Generalisation is best performed with @{text"arbitrary: y\<^isub>1 \<dots> y\<^isub>k"}. 
This heuristic prevents trivial failures like the one above.
However, it should not be applied blindly.
It is not always required, and the additional quantifiers can complicate
matters in some cases. The variables that need to be quantified are typically
those that change in recursive calls.

\section{Simplification}

So far we have talked a lot about simplifying terms without explaining the concept. \concept{Simplification} means
\begin{itemize}
\item using equations $l = r$ from left to right (only),
\item as long as possible.
\end{itemize}
To emphasise the directionality, equations that have been given the
@{text"simp"} attribute are called \concept{simplification}
rules. Logically, they are still symmetric, but proofs by
simplification use them only in the left-to-right direction.  The proof tool
that performs simplifications is called the \concept{simplifier}. It is the
basis of @{text auto} and other related proof methods.

The idea of simplification is best explained by an example. Given the
simplification rules
\[
\begin{array}{rcl@ {\quad}l}
@{term"0 + n::nat"} &@{text"="}& @{text n} & (1) \\
@{term"(Suc m) + n"} &@{text"="}& @{term"Suc (m + n)"} & (2) \\
@{text"(Suc m \<le> Suc n)"} &@{text"="}& @{text"(m \<le> n)"} & (3)\\
@{text"(0 \<le> m)"} &@{text"="}& @{const True} & (4)
\end{array}
\]
the formula @{prop"0 + Suc 0 \<le> Suc 0 + x"} is simplified to @{const True}
as follows:
\[
\begin{array}{r@ {}c@ {}l@ {\quad}l}
@{text"(0 + Suc 0"} & \leq & @{text"Suc 0 + x)"}  & \stackrel{(1)}{=} \\
@{text"(Suc 0"}     & \leq & @{text"Suc 0 + x)"}  & \stackrel{(2)}{=} \\
@{text"(Suc 0"}     & \leq & @{text"Suc (0 + x)"} & \stackrel{(3)}{=} \\
@{text"(0"}         & \leq & @{text"0 + x)"}      & \stackrel{(4)}{=} \\[1ex]
 & @{const True}
\end{array}
\]
Simplification is often also called \concept{rewriting}
and simplification rules \concept{rewrite rules}.

\subsection{Simplification rules}

The attribute @{text"simp"} declares theorems to be simplification rules,
which the simplifier will use automatically. In addition,
\isacom{datatype} and \isacom{fun} commands implicitly declare some
simplification rules: \isacom{datatype} the distinctness and injectivity
rules, \isacom{fun} the defining equations. Definitions are not declared
as simplification rules automatically! Nearly any theorem can become a
simplification rule. The simplifier will try to transform it into an
equation. For example, the theorem @{prop"\<not> P"} is turned into @{prop"P = False"}.

Only equations that really simplify, like @{prop"rev (rev xs) = xs"} and
@{prop"xs @ [] = xs"}, should be declared as simplification
rules. Equations that may be counterproductive as simplification rules
should only be used in specific proof steps (see \S\ref{sec:simp} below).
Distributivity laws, for example, alter the structure of terms
and can produce an exponential blow-up.

\subsection{Conditional simplification rules}

Simplification rules can be conditional.  Before applying such a rule, the
simplifier will first try to prove the preconditions, again by
simplification. For example, given the simplification rules
\begin{quote}
@{prop"p(0::nat) = True"}\\
@{prop"p(x) \<Longrightarrow> f(x) = g(x)"},
\end{quote}
the term @{term"f(0::nat)"} simplifies to @{term"g(0::nat)"}
but @{term"f(1::nat)"} does not simplify because @{prop"p(1::nat)"}
is not provable.

\subsection{Termination}

Simplification can run forever, for example if both @{prop"f x = g x"} and
@{prop"g(x) = f(x)"} are simplification rules. It is the user's
responsibility not to include simplification rules that can lead to
nontermination, either on their own or in combination with other
simplification rules. The right-hand side of a simplification rule should
always be ``simpler'' than the left-hand side---in some sense. But since
termination is undecidable, such a check cannot be automated completely
and Isabelle makes little attempt to detect nontermination.

When conditional simplification rules are applied, their preconditions are
proved first. Hence all preconditions need to be
simpler than the left-hand side of the conclusion. For example
\begin{quote}
@{prop "n < m \<Longrightarrow> (n < Suc m) = True"}
\end{quote}
is suitable as a simplification rule: both @{prop"n<m"} and @{const True}
are simpler than \mbox{@{prop"n < Suc m"}}. But
\begin{quote}
@{prop "Suc n < m \<Longrightarrow> (n < m) = True"}
\end{quote}
leads to nontermination: when trying to rewrite @{prop"n<m"} to @{const True}
one first has to prove \mbox{@{prop"Suc n < m"}}, which can be rewritten to @{const True} provided @{prop"Suc(Suc n) < m"}, \emph{ad infinitum}.

\subsection{The @{text simp} proof method}
\label{sec:simp}

So far we have only used the proof method @{text auto}.  Method @{text simp}
is the key component of @{text auto}, but @{text auto} can do much more. In
some cases, @{text auto} is overeager and modifies the proof state too much.
In such cases the more predictable @{text simp} method should be used.
Given a goal
\begin{quote}
@{text"1. \<lbrakk> P\<^isub>1; \<dots>; P\<^isub>m \<rbrakk> \<Longrightarrow> C"}
\end{quote}
the command
\begin{quote}
\isacom{apply}@{text"(simp add: th\<^isub>1 \<dots> th\<^isub>n)"}
\end{quote}
simplifies the assumptions @{text "P\<^isub>i"} and the conclusion @{text C} using
\begin{itemize}
\item all simplification rules, including the ones coming from \isacom{datatype} and \isacom{fun},
\item the additional lemmas @{text"th\<^isub>1 \<dots> th\<^isub>n"}, and
\item the assumptions.
\end{itemize}
In addition to or instead of @{text add} there is also @{text del} for removing
simplification rules temporarily. Both are optional. Method @{text auto}
can be modified similarly:
\begin{quote}
\isacom{apply}@{text"(auto simp add: \<dots> simp del: \<dots>)"}
\end{quote}
Here the modifiers are @{text"simp add"} and @{text"simp del"}
instead of just @{text add} and @{text del} because @{text auto}
does not just perform simplification.

Note that @{text simp} acts only on subgoal 1, @{text auto} acts on all
subgoals. There is also @{text simp_all}, which applies @{text simp} to
all subgoals.

\subsection{Rewriting with definitions}
\label{sec:rewr-defs}

Definitions introduced by the command \isacom{definition}
can also be used as simplification rules,
but by default they are not: the simplifier does not expand them
automatically. Definitions are intended for introducing abstract concepts and
not merely as abbreviations. Of course, we need to expand the definition
initially, but once we have proved enough abstract properties of the new
constant, we can forget its original definition. This style makes proofs more
robust: if the definition has to be changed, only the proofs of the abstract
properties will be affected.

The definition of a function @{text f} is a theorem named @{text f_def}
and can be added to a call of @{text simp} just like any other theorem:
\begin{quote}
\isacom{apply}@{text"(simp add: f_def)"}
\end{quote}
In particular, let-expressions can be unfolded by
making @{thm[source] Let_def} a simplification rule.

\subsection{Case splitting with @{text simp}}

Goals containing if-expressions are automatically split into two cases by
@{text simp} using the rule
\begin{quote}
@{prop"P(if A then s else t) = ((A \<longrightarrow> P(s)) \<and> (~A \<longrightarrow> P(t)))"}
\end{quote}
For example, @{text simp} can prove
\begin{quote}
@{prop"(A \<and> B) = (if A then B else False)"}
\end{quote}
because both @{prop"A \<longrightarrow> (A & B) = B"} and @{prop"~A \<longrightarrow> (A & B) = False"}
simplify to @{const True}.

We can split case-expressions similarly. For @{text nat} the rule looks like this:
@{prop[display,margin=65,indent=4]"P(case e of 0 \<Rightarrow> a | Suc n \<Rightarrow> b n) = ((e = 0 \<longrightarrow> P a) & (ALL n. e = Suc n \<longrightarrow> P(b n)))"}
Case expressions are not split automatically by @{text simp}, but @{text simp}
can be instructed to do so:
\begin{quote}
\isacom{apply}@{text"(simp split: nat.split)"}
\end{quote}
splits all case-expressions over natural numbers. For an arbitrary
datatype @{text t} it is @{text "t.split"} instead of @{thm[source] nat.split}.
Method @{text auto} can be modified in exactly the same way.
*}
(*<*)
end
(*>*)
