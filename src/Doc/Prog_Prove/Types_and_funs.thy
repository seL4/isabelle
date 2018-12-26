(*<*)
theory Types_and_funs
imports Main
begin
(*>*)
text\<open>
\vspace{-5ex}
\section{Type and Function Definitions}

Type synonyms are abbreviations for existing types, for example
\index{string@\<open>string\<close>}\<close>

type_synonym string = "char list"

text\<open>
Type synonyms are expanded after parsing and are not present in internal representation and output. They are mere conveniences for the reader.

\subsection{Datatypes}
\label{sec:datatypes}

The general form of a datatype definition looks like this:
\begin{quote}
\begin{tabular}{@ {}rclcll}
\indexed{\isacom{datatype}}{datatype} \<open>('a\<^sub>1,\<dots>,'a\<^sub>n)t\<close>
     & = & $C_1 \ \<open>"\<close>\tau_{1,1}\<open>"\<close> \dots \<open>"\<close>\tau_{1,n_1}\<open>"\<close>$ \\
     & $|$ & \dots \\
     & $|$ & $C_k \ \<open>"\<close>\tau_{k,1}\<open>"\<close> \dots \<open>"\<close>\tau_{k,n_k}\<open>"\<close>$
\end{tabular}
\end{quote}
It introduces the constructors \
$C_i :: \tau_{i,1}\Rightarrow \cdots \Rightarrow \tau_{i,n_i} \Rightarrow$~\<open>('a\<^sub>1,\<dots>,'a\<^sub>n)t\<close> \ and expresses that any value of this type is built from these constructors in a unique manner. Uniqueness is implied by the following
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
the \concept{structural induction}\index{induction} rule: to show
$P~x$ for all $x$ of type \<open>('a\<^sub>1,\<dots>,'a\<^sub>n)t\<close>,
one needs to show $P(C_i\ x_1 \dots x_{n_i})$ (for each $i$) assuming
$P(x_j)$ for all $j$ where $\tau_{i,j} =$~\<open>('a\<^sub>1,\<dots>,'a\<^sub>n)t\<close>.
Distinctness and injectivity are applied automatically by \<open>auto\<close>
and other proof methods. Induction must be applied explicitly.

Like in functional programming languages, datatype values can be taken apart
with case expressions\index{case expression}\index{case expression@\<open>case ... of\<close>}, for example
\begin{quote}
\noquotes{@{term[source] "(case xs of [] \<Rightarrow> 0 | x # _ \<Rightarrow> Suc x)"}}
\end{quote}
Case expressions must be enclosed in parentheses.

As an example of a datatype beyond @{typ nat} and \<open>list\<close>, consider binary trees:
\<close>

datatype 'a tree = Tip | Node  "'a tree"  'a  "'a tree"

text\<open>with a mirror function:\<close>

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

text\<open>The following lemma illustrates induction:\<close>

lemma "mirror(mirror t) = t"
apply(induction t)

txt\<open>yields
@{subgoals[display]}
The induction step contains two induction hypotheses, one for each subtree.
An application of \<open>auto\<close> finishes the proof.

A very simple but also very useful datatype is the predefined
@{datatype[display] option}\index{option@\<open>option\<close>}\index{None@@{const None}}\index{Some@@{const Some}}
Its sole purpose is to add a new element @{const None} to an existing
type @{typ 'a}. To make sure that @{const None} is distinct from all the
elements of @{typ 'a}, you wrap them up in @{const Some} and call
the new type @{typ"'a option"}. A typical application is a lookup function
on a list of key-value pairs, often called an association list:
\<close>
(*<*)
apply auto
done
(*>*)
fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a,b) # ps) x = (if a = x then Some b else lookup ps x)"

text\<open>
Note that \<open>\<tau>\<^sub>1 * \<tau>\<^sub>2\<close> is the type of pairs, also written \<open>\<tau>\<^sub>1 \<times> \<tau>\<^sub>2\<close>.
Pairs can be taken apart either by pattern matching (as above) or with the
projection functions @{const fst} and @{const snd}: @{thm fst_conv[of x y]} and @{thm snd_conv[of x y]}.
Tuples are simulated by pairs nested to the right: @{term"(a,b,c)"}
is short for \<open>(a, (b, c))\<close> and \<open>\<tau>\<^sub>1 \<times> \<tau>\<^sub>2 \<times> \<tau>\<^sub>3\<close> is short for
\<open>\<tau>\<^sub>1 \<times> (\<tau>\<^sub>2 \<times> \<tau>\<^sub>3)\<close>.

\subsection{Definitions}

Non-recursive functions can be defined as in the following example:
\index{definition@\isacom{definition}}\<close>

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

text\<open>Such definitions do not allow pattern matching but only
\<open>f x\<^sub>1 \<dots> x\<^sub>n = t\<close>, where \<open>f\<close> does not occur in \<open>t\<close>.

\subsection{Abbreviations}

Abbreviations are similar to definitions:
\index{abbreviation@\isacom{abbreviation}}\<close>

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"

text\<open>The key difference is that @{const sq'} is only syntactic sugar:
after parsing, @{term"sq' t"} is replaced by \mbox{@{term"t*t"}};
before printing, every occurrence of @{term"u*u"} is replaced by
\mbox{@{term"sq' u"}}.  Internally, @{const sq'} does not exist.
This is the
advantage of abbreviations over definitions: definitions need to be expanded
explicitly (\autoref{sec:rewr-defs}) whereas abbreviations are already
expanded upon parsing. However, abbreviations should be introduced sparingly:
if abused, they can lead to a confusing discrepancy between the internal and
external view of a term.

The ASCII representation of \<open>\<equiv>\<close> is \texttt{==} or \xsymbol{equiv}.

\subsection{Recursive Functions}
\label{sec:recursive-funs}

Recursive functions are defined with \indexed{\isacom{fun}}{fun} by pattern matching
over datatype constructors. The order of equations matters, as in
functional programming languages. However, all HOL functions must be
total. This simplifies the logic --- terms are always defined --- but means
that recursive functions must terminate. Otherwise one could define a
function @{prop"f n = f n + (1::nat)"} and conclude \mbox{@{prop"(0::nat) = 1"}} by
subtracting @{term"f n"} on both sides.

Isabelle's automatic termination checker requires that the arguments of
recursive calls on the right-hand side must be strictly smaller than the
arguments on the left-hand side. In the simplest case, this means that one
fixed argument position decreases in size with each recursive call. The size
is measured as the number of constructors (excluding 0-ary ones, e.g., \<open>Nil\<close>). Lexicographic combinations are also recognized. In more complicated
situations, the user may have to prove termination by hand. For details
see~@{cite Krauss}.

Functions defined with \isacom{fun} come with their own induction schema
that mirrors the recursion schema and is derived from the termination
order. For example,
\<close>

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

text\<open>does not just define @{const div2} but also proves a
customized induction rule:
\[
\inferrule{
\mbox{@{thm (prem 1) div2.induct}}\\
\mbox{@{thm (prem 2) div2.induct}}\\
\mbox{@{thm (prem 3) div2.induct}}}
{\mbox{@{thm (concl) div2.induct[of _ "m"]}}}
\]
This customized induction rule can simplify inductive proofs. For example,
\<close>

lemma "div2(n) = n div 2"
apply(induction n rule: div2.induct)

txt\<open>(where the infix \<open>div\<close> is the predefined division operation)
yields the subgoals
@{subgoals[display,margin=65]}
An application of \<open>auto\<close> finishes the proof.
Had we used ordinary structural induction on \<open>n\<close>,
the proof would have needed an additional
case analysis in the induction step.

This example leads to the following induction heuristic:
\begin{quote}
\emph{Let \<open>f\<close> be a recursive function.
If the definition of \<open>f\<close> is more complicated
than having one equation for each constructor of some datatype,
then properties of \<open>f\<close> are best proved via \<open>f.induct\<close>.\index{inductionrule@\<open>.induct\<close>}}
\end{quote}

The general case is often called \concept{computation induction},
because the induction follows the (terminating!) computation.
For every defining equation
\begin{quote}
\<open>f(e) = \<dots> f(r\<^sub>1) \<dots> f(r\<^sub>k) \<dots>\<close>
\end{quote}
where \<open>f(r\<^sub>i)\<close>, \<open>i=1\<dots>k\<close>, are all the recursive calls,
the induction rule \<open>f.induct\<close> contains one premise of the form
\begin{quote}
\<open>P(r\<^sub>1) \<Longrightarrow> \<dots> \<Longrightarrow> P(r\<^sub>k) \<Longrightarrow> P(e)\<close>
\end{quote}
If \<open>f :: \<tau>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<tau>\<^sub>n \<Rightarrow> \<tau>\<close> then \<open>f.induct\<close> is applied like this:
\begin{quote}
\isacom{apply}\<open>(induction x\<^sub>1 \<dots> x\<^sub>n rule: f.induct)\<close>\index{inductionrule@\<open>induction ... rule:\<close>}
\end{quote}
where typically there is a call \<open>f x\<^sub>1 \<dots> x\<^sub>n\<close> in the goal.
But note that the induction rule does not mention \<open>f\<close> at all,
except in its name, and is applicable independently of \<open>f\<close>.


\subsection*{Exercises}

\begin{exercise}
Starting from the type \<open>'a tree\<close> defined in the text, define
a function \<open>contents ::\<close> @{typ "'a tree \<Rightarrow> 'a list"}
that collects all values in a tree in a list, in any order,
without removing duplicates.
Then define a function \<open>sum_tree ::\<close> @{typ "nat tree \<Rightarrow> nat"}
that sums up all values in a tree of natural numbers
and prove @{prop "sum_tree t = sum_list(contents t)"}
(where @{const sum_list} is predefined).
\end{exercise}

\begin{exercise}
Define a new type \<open>'a tree2\<close> of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{const mirror} function accordingly. Define two functions
\<open>pre_order\<close> and \<open>post_order\<close> of type \<open>'a tree2 \<Rightarrow> 'a list\<close>
that traverse a tree and collect all stored values in the respective order in
a list. Prove @{prop "pre_order (mirror t) = rev (post_order t)"}.
\end{exercise}

\begin{exercise}
Define a function \<open>intersperse ::\<close> @{typ "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"}
such that \<open>intersperse a [x\<^sub>1, ..., x\<^sub>n] = [x\<^sub>1, a, x\<^sub>2, a, ..., a, x\<^sub>n]\<close>.
Now prove that @{prop "map f (intersperse a xs) = intersperse (f a) (map f xs)"}.
\end{exercise}


\section{Induction Heuristics}\index{induction heuristics}

We have already noted that theorems about recursive functions are proved by
induction. In case the function has more than one argument, we have followed
the following heuristic in the proofs about the append function:
\begin{quote}
\emph{Perform induction on argument number $i$\\
 if the function is defined by recursion on argument number $i$.}
\end{quote}
The key heuristic, and the main point of this section, is to
\emph{generalize the goal before induction}.
The reason is simple: if the goal is
too specific, the induction hypothesis is too weak to allow the induction
step to go through. Let us illustrate the idea with an example.

Function @{const rev} has quadratic worst-case running time
because it calls append for each element of the list and
append is linear in its first argument.  A linear time version of
@{const rev} requires an extra argument where the result is accumulated
gradually, using only~\<open>#\<close>:
\<close>
(*<*)
apply auto
done
(*>*)
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev []        ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

text\<open>The behaviour of @{const itrev} is simple: it reverses
its first argument by stacking its elements onto the second argument,
and it returns that second argument when the first one becomes
empty. Note that @{const itrev} is tail-recursive: it can be
compiled into a loop; no stack is necessary for executing it.

Naturally, we would like to show that @{const itrev} does indeed reverse
its first argument provided the second one is empty:
\<close>

lemma "itrev xs [] = rev xs"

txt\<open>There is no choice as to the induction variable:
\<close>

apply(induction xs)
apply(auto)

txt\<open>
Unfortunately, this attempt does not prove
the induction step:
@{subgoals[display,margin=70]}
The induction hypothesis is too weak.  The fixed
argument,~@{term"[]"}, prevents it from rewriting the conclusion.  
This example suggests a heuristic:
\begin{quote}
\emph{Generalize goals for induction by replacing constants by variables.}
\end{quote}
Of course one cannot do this naively: @{prop"itrev xs ys = rev xs"} is
just not true.  The correct generalization is
\<close>
(*<*)oops(*>*)
lemma "itrev xs ys = rev xs @ ys"
(*<*)apply(induction xs, auto)(*>*)
txt\<open>
If \<open>ys\<close> is replaced by @{term"[]"}, the right-hand side simplifies to
@{term"rev xs"}, as required.
In this instance it was easy to guess the right generalization.
Other situations can require a good deal of creativity.  

Although we now have two variables, only \<open>xs\<close> is suitable for
induction, and we repeat our proof attempt. Unfortunately, we are still
not there:
@{subgoals[display,margin=65]}
The induction hypothesis is still too weak, but this time it takes no
intuition to generalize: the problem is that the \<open>ys\<close>
in the induction hypothesis is fixed,
but the induction hypothesis needs to be applied with
@{term"a # ys"} instead of \<open>ys\<close>. Hence we prove the theorem
for all \<open>ys\<close> instead of a fixed one. We can instruct induction
to perform this generalization for us by adding \<open>arbitrary: ys\<close>\index{arbitrary@\<open>arbitrary:\<close>}.
\<close>
(*<*)oops
lemma "itrev xs ys = rev xs @ ys"
(*>*)
apply(induction xs arbitrary: ys)

txt\<open>The induction hypothesis in the induction step is now universally quantified over \<open>ys\<close>:
@{subgoals[display,margin=65]}
Thus the proof succeeds:
\<close>

apply auto
done

text\<open>
This leads to another heuristic for generalization:
\begin{quote}
\emph{Generalize induction by generalizing all free
variables\\ {\em(except the induction variable itself)}.}
\end{quote}
Generalization is best performed with \<open>arbitrary: y\<^sub>1 \<dots> y\<^sub>k\<close>. 
This heuristic prevents trivial failures like the one above.
However, it should not be applied blindly.
It is not always required, and the additional quantifiers can complicate
matters in some cases. The variables that need to be quantified are typically
those that change in recursive calls.


\subsection*{Exercises}

\begin{exercise}
Write a tail-recursive variant of the \<open>add\<close> function on @{typ nat}:
@{term "itadd :: nat \<Rightarrow> nat \<Rightarrow> nat"}.
Tail-recursive means that in the recursive case, \<open>itadd\<close> needs to call
itself directly: \mbox{@{term"itadd (Suc m) n"}} \<open>= itadd \<dots>\<close>.
Prove @{prop "itadd m n = add m n"}.
\end{exercise}


\section{Simplification}

So far we have talked a lot about simplifying terms without explaining the concept.
\conceptidx{Simplification}{simplification} means
\begin{itemize}
\item using equations $l = r$ from left to right (only),
\item as long as possible.
\end{itemize}
To emphasize the directionality, equations that have been given the
\<open>simp\<close> attribute are called \conceptidx{simplification rules}{simplification rule}.
Logically, they are still symmetric, but proofs by
simplification use them only in the left-to-right direction.  The proof tool
that performs simplifications is called the \concept{simplifier}. It is the
basis of \<open>auto\<close> and other related proof methods.

The idea of simplification is best explained by an example. Given the
simplification rules
\[
\begin{array}{rcl@ {\quad}l}
@{term"0 + n::nat"} &\<open>=\<close>& \<open>n\<close> & (1) \\
@{term"(Suc m) + n"} &\<open>=\<close>& @{term"Suc (m + n)"} & (2) \\
\<open>(Suc m \<le> Suc n)\<close> &\<open>=\<close>& \<open>(m \<le> n)\<close> & (3)\\
\<open>(0 \<le> m)\<close> &\<open>=\<close>& @{const True} & (4)
\end{array}
\]
the formula @{prop"0 + Suc 0 \<le> Suc 0 + x"} is simplified to @{const True}
as follows:
\[
\begin{array}{r@ {}c@ {}l@ {\quad}l}
\<open>(0 + Suc 0\<close> & \leq & \<open>Suc 0 + x)\<close>  & \stackrel{(1)}{=} \\
\<open>(Suc 0\<close>     & \leq & \<open>Suc 0 + x)\<close>  & \stackrel{(2)}{=} \\
\<open>(Suc 0\<close>     & \leq & \<open>Suc (0 + x))\<close> & \stackrel{(3)}{=} \\
\<open>(0\<close>         & \leq & \<open>0 + x)\<close>      & \stackrel{(4)}{=} \\[1ex]
 & @{const True}
\end{array}
\]
Simplification is often also called \concept{rewriting}
and simplification rules \conceptidx{rewrite rules}{rewrite rule}.

\subsection{Simplification Rules}

The attribute \<open>simp\<close> declares theorems to be simplification rules,
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
should only be used in specific proof steps (see \autoref{sec:simp} below).
Distributivity laws, for example, alter the structure of terms
and can produce an exponential blow-up.

\subsection{Conditional Simplification Rules}

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
always be ``simpler'' than the left-hand side --- in some sense. But since
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

\subsection{The \indexed{\<open>simp\<close>}{simp} Proof Method}
\label{sec:simp}

So far we have only used the proof method \<open>auto\<close>.  Method \<open>simp\<close>
is the key component of \<open>auto\<close>, but \<open>auto\<close> can do much more. In
some cases, \<open>auto\<close> is overeager and modifies the proof state too much.
In such cases the more predictable \<open>simp\<close> method should be used.
Given a goal
\begin{quote}
\<open>1. \<lbrakk> P\<^sub>1; \<dots>; P\<^sub>m \<rbrakk> \<Longrightarrow> C\<close>
\end{quote}
the command
\begin{quote}
\isacom{apply}\<open>(simp add: th\<^sub>1 \<dots> th\<^sub>n)\<close>
\end{quote}
simplifies the assumptions \<open>P\<^sub>i\<close> and the conclusion \<open>C\<close> using
\begin{itemize}
\item all simplification rules, including the ones coming from \isacom{datatype} and \isacom{fun},
\item the additional lemmas \<open>th\<^sub>1 \<dots> th\<^sub>n\<close>, and
\item the assumptions.
\end{itemize}
In addition to or instead of \<open>add\<close> there is also \<open>del\<close> for removing
simplification rules temporarily. Both are optional. Method \<open>auto\<close>
can be modified similarly:
\begin{quote}
\isacom{apply}\<open>(auto simp add: \<dots> simp del: \<dots>)\<close>
\end{quote}
Here the modifiers are \<open>simp add\<close> and \<open>simp del\<close>
instead of just \<open>add\<close> and \<open>del\<close> because \<open>auto\<close>
does not just perform simplification.

Note that \<open>simp\<close> acts only on subgoal 1, \<open>auto\<close> acts on all
subgoals. There is also \<open>simp_all\<close>, which applies \<open>simp\<close> to
all subgoals.

\subsection{Rewriting with Definitions}
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

The definition of a function \<open>f\<close> is a theorem named \<open>f_def\<close>
and can be added to a call of \<open>simp\<close> like any other theorem:
\begin{quote}
\isacom{apply}\<open>(simp add: f_def)\<close>
\end{quote}
In particular, let-expressions can be unfolded by
making @{thm[source] Let_def} a simplification rule.

\subsection{Case Splitting With \<open>simp\<close>}

Goals containing if-expressions are automatically split into two cases by
\<open>simp\<close> using the rule
\begin{quote}
@{prop"P(if A then s else t) = ((A \<longrightarrow> P(s)) \<and> (~A \<longrightarrow> P(t)))"}
\end{quote}
For example, \<open>simp\<close> can prove
\begin{quote}
@{prop"(A \<and> B) = (if A then B else False)"}
\end{quote}
because both @{prop"A \<longrightarrow> (A & B) = B"} and @{prop"~A \<longrightarrow> (A & B) = False"}
simplify to @{const True}.

We can split case-expressions similarly. For \<open>nat\<close> the rule looks like this:
@{prop[display,margin=65,indent=4]"P(case e of 0 \<Rightarrow> a | Suc n \<Rightarrow> b n) = ((e = 0 \<longrightarrow> P a) \<and> (\<forall>n. e = Suc n \<longrightarrow> P(b n)))"}
Case expressions are not split automatically by \<open>simp\<close>, but \<open>simp\<close>
can be instructed to do so:
\begin{quote}
\isacom{apply}\<open>(simp split: nat.split)\<close>
\end{quote}
splits all case-expressions over natural numbers. For an arbitrary
datatype \<open>t\<close> it is \<open>t.split\<close>\index{split@\<open>.split\<close>} instead of @{thm[source] nat.split}.
Method \<open>auto\<close> can be modified in exactly the same way.
The modifier \indexed{\<open>split:\<close>}{split} can be followed by multiple names.
Splitting if or case-expressions in the assumptions requires 
\<open>split: if_splits\<close> or \<open>split: t.splits\<close>.

\ifsem\else
\subsection{Rewriting \<open>let\<close> and Numerals}

Let-expressions (@{term "let x = s in t"}) can be expanded explicitly with the simplification rule
@{thm[source] Let_def}. The simplifier will not expand \<open>let\<close>s automatically in many cases.

Numerals of type @{typ nat} can be converted to @{const Suc} terms with the simplification rule
@{thm[source] numeral_eq_Suc}. This is required, for example, when a function that is defined
by pattern matching with @{const Suc} is applied to a numeral: if \<open>f\<close> is defined by
\<open>f 0 = ...\<close> and  \<open>f (Suc n) = ...\<close>, the simplifier cannot simplify \<open>f 2\<close> unless
\<open>2\<close> is converted to @{term "Suc(Suc 0)"} (via @{thm[source] numeral_eq_Suc}).
\fi

\subsection*{Exercises}

\exercise\label{exe:tree0}
Define a datatype \<open>tree0\<close> of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function \<open>nodes :: tree0 \<Rightarrow> nat\<close> that counts the number of
all nodes (inner nodes and leaves) in such a tree.
Consider the following recursive function:
\<close>
(*<*)
datatype tree0 = Tip | Node tree0 tree0
(*>*)
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

text \<open>
Find an equation expressing the size of a tree after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and \<open>n\<close>. Prove your equation.
You may use the usual arithmetic operators, including the exponentiation
operator ``\<open>^\<close>''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
\<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text\<open>
Define a function \noquotes{@{term [source]"eval :: exp \<Rightarrow> int \<Rightarrow> int"}}
such that @{term"eval e x"} evaluates \<open>e\<close> at the value
\<open>x\<close>.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function \noquotes{@{term [source] "evalp :: int list \<Rightarrow> int \<Rightarrow> int"}}
that evaluates a polynomial at the given value.
Define a function \noquotes{@{term[source] "coeffs :: exp \<Rightarrow> int list"}}
that transforms an expression into a polynomial. This may require auxiliary
functions. Prove that \<open>coeffs\<close> preserves the value of the expression:
\mbox{@{prop"evalp (coeffs e) x = eval e x"}.}
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
\<close>
(*<*)
end
(*>*)
