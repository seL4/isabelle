(*<*)
theory examples = Main:;
(*>*)

text{*
Here is a simple example, the Fibonacci function:
*}

consts fib :: "nat \<Rightarrow> nat";
recdef fib "measure(\<lambda>n. n)"
  "fib 0 = 0"
  "fib 1 = 1"
  "fib (Suc(Suc x)) = fib x + fib (Suc x)";

text{*\noindent
The definition of @{term"fib"} is accompanied by a \bfindex{measure function}
@{term"%n. n"} which maps the argument of @{term"fib"} to a
natural number. The requirement is that in each equation the measure of the
argument on the left-hand side is strictly greater than the measure of the
argument of each recursive call. In the case of @{term"fib"} this is
obviously true because the measure function is the identity and
@{term"Suc(Suc x)"} is strictly greater than both @{term"x"} and
@{term"Suc x"}.

Slightly more interesting is the insertion of a fixed element
between any two elements of a list:
*}

consts sep :: "'a \<times> 'a list \<Rightarrow> 'a list";
recdef sep "measure (\<lambda>(a,xs). length xs)"
  "sep(a, [])     = []"
  "sep(a, [x])    = [x]"
  "sep(a, x#y#zs) = x # a # sep(a,y#zs)";

text{*\noindent
This time the measure is the length of the list, which decreases with the
recursive call; the first component of the argument tuple is irrelevant.
The details of tupled $\lambda$-abstractions @{text"\<lambda>(x\<^sub>1,\<dots>,x\<^sub>n)"} are
explained in \S\ref{sec:products}, but for now your intuition is all you need.

Pattern matching need not be exhaustive:
*}

consts last :: "'a list \<Rightarrow> 'a";
recdef last "measure (\<lambda>xs. length xs)"
  "last [x]      = x"
  "last (x#y#zs) = last (y#zs)";

text{*
Overlapping patterns are disambiguated by taking the order of equations into
account, just as in functional programming:
*}

consts sep1 :: "'a \<times> 'a list \<Rightarrow> 'a list";
recdef sep1 "measure (\<lambda>(a,xs). length xs)"
  "sep1(a, x#y#zs) = x # a # sep1(a,y#zs)"
  "sep1(a, xs)     = xs";

text{*\noindent
To guarantee that the second equation can only be applied if the first
one does not match, Isabelle internally replaces the second equation
by the two possibilities that are left: @{prop"sep1(a,[]) = []"} and
@{prop"sep1(a, [x]) = [x]"}.  Thus the functions @{term sep} and
@{term sep1} are identical.

\begin{warn}
  \isacommand{recdef} only takes the first argument of a (curried)
  recursive function into account. This means both the termination measure
  and pattern matching can only use that first argument. In general, you will
  therefore have to combine several arguments into a tuple. In case only one
  argument is relevant for termination, you can also rearrange the order of
  arguments as in the following definition:
\end{warn}
*}
consts sep2 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list";
recdef sep2 "measure length"
  "sep2 (x#y#zs) = (\<lambda>a. x # a # sep2 (y#zs) a)"
  "sep2 xs       = (\<lambda>a. xs)";

text{*
Because of its pattern-matching syntax, \isacommand{recdef} is also useful
for the definition of non-recursive functions:
*}

consts swap12 :: "'a list \<Rightarrow> 'a list";
recdef swap12 "{}"
  "swap12 (x#y#zs) = y#x#zs"
  "swap12 zs       = zs";

text{*\noindent
For non-recursive functions the termination measure degenerates to the empty
set @{term"{}"}.
*}

(*<*)
end
(*>*)
