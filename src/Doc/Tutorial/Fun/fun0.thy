(*<*)
theory fun0 imports Main begin
(*>*)

text\<open>
\subsection{Definition}
\label{sec:fun-examples}

Here is a simple example, the \rmindex{Fibonacci function}:
\<close>

fun fib :: "nat \<Rightarrow> nat" where
"fib 0 = 0" |
"fib (Suc 0) = 1" |
"fib (Suc(Suc x)) = fib x + fib (Suc x)"

text\<open>\noindent
This resembles ordinary functional programming languages. Note the obligatory
\isacommand{where} and \isa{|}. Command \isacommand{fun} declares and
defines the function in one go. Isabelle establishes termination automatically
because \<^const>\<open>fib\<close>'s argument decreases in every recursive call.

Slightly more interesting is the insertion of a fixed element
between any two elements of a list:
\<close>

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a []     = []" |
"sep a [x]    = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

text\<open>\noindent
This time the length of the list decreases with the
recursive call; the first argument is irrelevant for termination.

Pattern matching\index{pattern matching!and \isacommand{fun}}
need not be exhaustive and may employ wildcards:
\<close>

fun last :: "'a list \<Rightarrow> 'a" where
"last [x]      = x" |
"last (_#y#zs) = last (y#zs)"

text\<open>
Overlapping patterns are disambiguated by taking the order of equations into
account, just as in functional programming:
\<close>

fun sep1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep1 a (x#y#zs) = x # a # sep1 a (y#zs)" |
"sep1 _ xs       = xs"

text\<open>\noindent
To guarantee that the second equation can only be applied if the first
one does not match, Isabelle internally replaces the second equation
by the two possibilities that are left: \<^prop>\<open>sep1 a [] = []\<close> and
\<^prop>\<open>sep1 a [x] = [x]\<close>.  Thus the functions \<^const>\<open>sep\<close> and
\<^const>\<open>sep1\<close> are identical.

Because of its pattern matching syntax, \isacommand{fun} is also useful
for the definition of non-recursive functions:
\<close>

fun swap12 :: "'a list \<Rightarrow> 'a list" where
"swap12 (x#y#zs) = y#x#zs" |
"swap12 zs       = zs"

text\<open>
After a function~$f$ has been defined via \isacommand{fun},
its defining equations (or variants derived from them) are available
under the name $f$\<open>.simps\<close> as theorems.
For example, look (via \isacommand{thm}) at
@{thm[source]sep.simps} and @{thm[source]sep1.simps} to see that they define
the same function. What is more, those equations are automatically declared as
simplification rules.

\subsection{Termination}

Isabelle's automatic termination prover for \isacommand{fun} has a
fixed notion of the \emph{size} (of type \<^typ>\<open>nat\<close>) of an
argument. The size of a natural number is the number itself. The size
of a list is its length. For the general case see \S\ref{sec:general-datatype}.
A recursive function is accepted if \isacommand{fun} can
show that the size of one fixed argument becomes smaller with each
recursive call.

More generally, \isacommand{fun} allows any \emph{lexicographic
combination} of size measures in case there are multiple
arguments. For example, the following version of \rmindex{Ackermann's
function} is accepted:\<close>

fun ack2 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"ack2 n 0 = Suc n" |
"ack2 0 (Suc m) = ack2 (Suc 0) m" |
"ack2 (Suc n) (Suc m) = ack2 (ack2 n (Suc m)) m"

text\<open>The order of arguments has no influence on whether
\isacommand{fun} can prove termination of a function. For more details
see elsewhere~@{cite bulwahnKN07}.

\subsection{Simplification}
\label{sec:fun-simplification}

Upon a successful termination proof, the recursion equations become
simplification rules, just as with \isacommand{primrec}.
In most cases this works fine, but there is a subtle
problem that must be mentioned: simplification may not
terminate because of automatic splitting of \<open>if\<close>.
\index{*if expressions!splitting of}
Let us look at an example:
\<close>

fun gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"gcd m n = (if n=0 then m else gcd n (m mod n))"

text\<open>\noindent
The second argument decreases with each recursive call.
The termination condition
@{prop[display]"n ~= (0::nat) ==> m mod n < n"}
is proved automatically because it is already present as a lemma in
HOL\@.  Thus the recursion equation becomes a simplification
rule. Of course the equation is nonterminating if we are allowed to unfold
the recursive call inside the \<open>else\<close> branch, which is why programming
languages and our simplifier don't do that. Unfortunately the simplifier does
something else that leads to the same problem: it splits 
each \<open>if\<close>-expression unless its
condition simplifies to \<^term>\<open>True\<close> or \<^term>\<open>False\<close>.  For
example, simplification reduces
@{prop[display]"gcd m n = k"}
in one step to
@{prop[display]"(if n=0 then m else gcd n (m mod n)) = k"}
where the condition cannot be reduced further, and splitting leads to
@{prop[display]"(n=0 --> m=k) & (n ~= 0 --> gcd n (m mod n)=k)"}
Since the recursive call \<^term>\<open>gcd n (m mod n)\<close> is no longer protected by
an \<open>if\<close>, it is unfolded again, which leads to an infinite chain of
simplification steps. Fortunately, this problem can be avoided in many
different ways.

The most radical solution is to disable the offending theorem
@{thm[source]if_split},
as shown in \S\ref{sec:AutoCaseSplits}.  However, we do not recommend this
approach: you will often have to invoke the rule explicitly when
\<open>if\<close> is involved.

If possible, the definition should be given by pattern matching on the left
rather than \<open>if\<close> on the right. In the case of \<^term>\<open>gcd\<close> the
following alternative definition suggests itself:
\<close>

fun gcd1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"gcd1 m 0 = m" |
"gcd1 m n = gcd1 n (m mod n)"

text\<open>\noindent
The order of equations is important: it hides the side condition
\<^prop>\<open>n ~= (0::nat)\<close>.  Unfortunately, not all conditionals can be
expressed by pattern matching.

A simple alternative is to replace \<open>if\<close> by \<open>case\<close>, 
which is also available for \<^typ>\<open>bool\<close> and is not split automatically:
\<close>

fun gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"gcd2 m n = (case n=0 of True \<Rightarrow> m | False \<Rightarrow> gcd2 n (m mod n))"

text\<open>\noindent
This is probably the neatest solution next to pattern matching, and it is
always available.

A final alternative is to replace the offending simplification rules by
derived conditional ones. For \<^term>\<open>gcd\<close> it means we have to prove
these lemmas:
\<close>

lemma [simp]: "gcd m 0 = m"
apply(simp)
done

lemma [simp]: "n \<noteq> 0 \<Longrightarrow> gcd m n = gcd n (m mod n)"
apply(simp)
done

text\<open>\noindent
Simplification terminates for these proofs because the condition of the \<open>if\<close> simplifies to \<^term>\<open>True\<close> or \<^term>\<open>False\<close>.
Now we can disable the original simplification rule:
\<close>

declare gcd.simps [simp del]

text\<open>
\index{induction!recursion|(}
\index{recursion induction|(}

\subsection{Induction}
\label{sec:fun-induction}

Having defined a function we might like to prove something about it.
Since the function is recursive, the natural proof principle is
again induction. But this time the structural form of induction that comes
with datatypes is unlikely to work well --- otherwise we could have defined the
function by \isacommand{primrec}. Therefore \isacommand{fun} automatically
proves a suitable induction rule $f$\<open>.induct\<close> that follows the
recursion pattern of the particular function $f$. We call this
\textbf{recursion induction}. Roughly speaking, it
requires you to prove for each \isacommand{fun} equation that the property
you are trying to establish holds for the left-hand side provided it holds
for all recursive calls on the right-hand side. Here is a simple example
involving the predefined \<^term>\<open>map\<close> functional on lists:
\<close>

lemma "map f (sep x xs) = sep (f x) (map f xs)"

txt\<open>\noindent
Note that \<^term>\<open>map f xs\<close>
is the result of applying \<^term>\<open>f\<close> to all elements of \<^term>\<open>xs\<close>. We prove
this lemma by recursion induction over \<^term>\<open>sep\<close>:
\<close>

apply(induct_tac x xs rule: sep.induct)

txt\<open>\noindent
The resulting proof state has three subgoals corresponding to the three
clauses for \<^term>\<open>sep\<close>:
@{subgoals[display,indent=0]}
The rest is pure simplification:
\<close>

apply simp_all
done

text\<open>\noindent The proof goes smoothly because the induction rule
follows the recursion of \<^const>\<open>sep\<close>.  Try proving the above lemma by
structural induction, and you find that you need an additional case
distinction.

In general, the format of invoking recursion induction is
\begin{quote}
\isacommand{apply}\<open>(induct_tac\<close> $x@1 \dots x@n$ \<open>rule:\<close> $f$\<open>.induct)\<close>
\end{quote}\index{*induct_tac (method)}%
where $x@1~\dots~x@n$ is a list of free variables in the subgoal and $f$ the
name of a function that takes $n$ arguments. Usually the subgoal will
contain the term $f x@1 \dots x@n$ but this need not be the case. The
induction rules do not mention $f$ at all. Here is @{thm[source]sep.induct}:
\begin{isabelle}
{\isasymlbrakk}~{\isasymAnd}a.~P~a~[];\isanewline
~~{\isasymAnd}a~x.~P~a~[x];\isanewline
~~{\isasymAnd}a~x~y~zs.~P~a~(y~\#~zs)~{\isasymLongrightarrow}~P~a~(x~\#~y~\#~zs){\isasymrbrakk}\isanewline
{\isasymLongrightarrow}~P~u~v%
\end{isabelle}
It merely says that in order to prove a property \<^term>\<open>P\<close> of \<^term>\<open>u\<close> and
\<^term>\<open>v\<close> you need to prove it for the three cases where \<^term>\<open>v\<close> is the
empty list, the singleton list, and the list with at least two elements.
The final case has an induction hypothesis:  you may assume that \<^term>\<open>P\<close>
holds for the tail of that list.
\index{induction!recursion|)}
\index{recursion induction|)}
\<close>
(*<*)
end
(*>*)
