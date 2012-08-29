(*<*)theory Typedefs imports Main begin(*>*)

section{*Introducing New Types*}

text{*\label{sec:adv-typedef}
For most applications, a combination of predefined types like @{typ bool} and
@{text"\<Rightarrow>"} with recursive datatypes and records is quite sufficient. Very
occasionally you may feel the need for a more advanced type.  If you
are certain that your type is not definable by any of the
standard means, then read on.
\begin{warn}
  Types in HOL must be non-empty; otherwise the quantifier rules would be
  unsound, because $\exists x.\ x=x$ is a theorem.
\end{warn}
*}

subsection{*Declaring New Types*}

text{*\label{sec:typedecl}
\index{types!declaring|(}%
\index{typedecl@\isacommand {typedecl} (command)}%
The most trivial way of introducing a new type is by a \textbf{type
declaration}: *}

typedecl my_new_type

text{*\noindent
This does not define @{typ my_new_type} at all but merely introduces its
name. Thus we know nothing about this type, except that it is
non-empty. Such declarations without definitions are
useful if that type can be viewed as a parameter of the theory.
A typical example is given in \S\ref{sec:VMC}, where we define a transition
relation over an arbitrary type of states.

In principle we can always get rid of such type declarations by making those
types parameters of every other type, thus keeping the theory generic. In
practice, however, the resulting clutter can make types hard to read.

If you are looking for a quick and dirty way of introducing a new type
together with its properties: declare the type and state its properties as
axioms. Example:
*}

axiomatization where
just_one: "\<exists>x::my_new_type. \<forall>y. x = y"

text{*\noindent
However, we strongly discourage this approach, except at explorative stages
of your development. It is extremely easy to write down contradictory sets of
axioms, in which case you will be able to prove everything but it will mean
nothing.  In the example above, the axiomatic approach is
unnecessary: a one-element type called @{typ unit} is already defined in HOL.
\index{types!declaring|)}
*}

subsection{*Defining New Types*}

text{*\label{sec:typedef}
\index{types!defining|(}%
\index{typedecl@\isacommand {typedef} (command)|(}%
Now we come to the most general means of safely introducing a new type, the
\textbf{type definition}. All other means, for example
\isacommand{datatype}, are based on it. The principle is extremely simple:
any non-empty subset of an existing type can be turned into a new type.
More precisely, the new type is specified to be isomorphic to some
non-empty subset of an existing type.

Let us work a simple example, the definition of a three-element type.
It is easily represented by the first three natural numbers:
*}

typedef three = "{0::nat, 1, 2}"

txt{*\noindent
In order to enforce that the representing set on the right-hand side is
non-empty, this definition actually starts a proof to that effect:
@{subgoals[display,indent=0]}
Fortunately, this is easy enough to show, even \isa{auto} could do it.
In general, one has to provide a witness, in our case 0:
*}

apply(rule_tac x = 0 in exI)
by simp

text{*
This type definition introduces the new type @{typ three} and asserts
that it is a copy of the set @{term"{0::nat,1,2}"}. This assertion
is expressed via a bijection between the \emph{type} @{typ three} and the
\emph{set} @{term"{0::nat,1,2}"}. To this end, the command declares the following
constants behind the scenes:
\begin{center}
\begin{tabular}{rcl}
@{term three} &::& @{typ"nat set"} \\
@{term Rep_three} &::& @{typ"three \<Rightarrow> nat"}\\
@{term Abs_three} &::& @{typ"nat \<Rightarrow> three"}
\end{tabular}
\end{center}
where constant @{term three} is explicitly defined as the representing set:
\begin{center}
@{thm three_def}\hfill(@{thm[source]three_def})
\end{center}
The situation is best summarized with the help of the following diagram,
where squares denote types and the irregular region denotes a set:
\begin{center}
\includegraphics[scale=.8]{typedef}
\end{center}
Finally, \isacommand{typedef} asserts that @{term Rep_three} is
surjective on the subset @{term three} and @{term Abs_three} and @{term
Rep_three} are inverses of each other:
\begin{center}
\begin{tabular}{@ {}r@ {\qquad\qquad}l@ {}}
@{thm Rep_three[no_vars]} & (@{thm[source]Rep_three}) \\
@{thm Rep_three_inverse[no_vars]} & (@{thm[source]Rep_three_inverse}) \\
@{thm Abs_three_inverse[no_vars]} & (@{thm[source]Abs_three_inverse})
\end{tabular}
\end{center}
%
From this example it should be clear what \isacommand{typedef} does
in general given a name (here @{text three}) and a set
(here @{term"{0::nat,1,2}"}).

Our next step is to define the basic functions expected on the new type.
Although this depends on the type at hand, the following strategy works well:
\begin{itemize}
\item define a small kernel of basic functions that can express all other
functions you anticipate.
\item define the kernel in terms of corresponding functions on the
representing type using @{term Abs} and @{term Rep} to convert between the
two levels.
\end{itemize}
In our example it suffices to give the three elements of type @{typ three}
names:
*}

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

text{*
So far, everything was easy. But it is clear that reasoning about @{typ
three} will be hell if we have to go back to @{typ nat} every time. Thus our
aim must be to raise our level of abstraction by deriving enough theorems
about type @{typ three} to characterize it completely. And those theorems
should be phrased in terms of @{term A}, @{term B} and @{term C}, not @{term
Abs_three} and @{term Rep_three}. Because of the simplicity of the example,
we merely need to prove that @{term A}, @{term B} and @{term C} are distinct
and that they exhaust the type.

In processing our \isacommand{typedef} declaration, 
Isabelle proves several helpful lemmas. The first two
express injectivity of @{term Rep_three} and @{term Abs_three}:
\begin{center}
\begin{tabular}{@ {}r@ {\qquad}l@ {}}
@{thm Rep_three_inject[no_vars]} & (@{thm[source]Rep_three_inject}) \\
\begin{tabular}{@ {}l@ {}}
@{text"\<lbrakk>x \<in> three; y \<in> three \<rbrakk>"} \\
@{text"\<Longrightarrow> (Abs_three x = Abs_three y) = (x = y)"}
\end{tabular} & (@{thm[source]Abs_three_inject}) \\
\end{tabular}
\end{center}
The following ones allow to replace some @{text"x::three"} by
@{text"Abs_three(y::nat)"}, and conversely @{term y} by @{term"Rep_three x"}:
\begin{center}
\begin{tabular}{@ {}r@ {\qquad}l@ {}}
@{thm Rep_three_cases[no_vars]} & (@{thm[source]Rep_three_cases}) \\
@{thm Abs_three_cases[no_vars]} & (@{thm[source]Abs_three_cases}) \\
@{thm Rep_three_induct[no_vars]} & (@{thm[source]Rep_three_induct}) \\
@{thm Abs_three_induct[no_vars]} & (@{thm[source]Abs_three_induct}) \\
\end{tabular}
\end{center}
These theorems are proved for any type definition, with @{term three}
replaced by the name of the type in question.

Distinctness of @{term A}, @{term B} and @{term C} follows immediately
if we expand their definitions and rewrite with the injectivity
of @{term Abs_three}:
*}

lemma "A \<noteq> B \<and> B \<noteq> A \<and> A \<noteq> C \<and> C \<noteq> A \<and> B \<noteq> C \<and> C \<noteq> B"
by(simp add: Abs_three_inject A_def B_def C_def three_def)

text{*\noindent
Of course we rely on the simplifier to solve goals like @{prop"(0::nat) \<noteq> 1"}.

The fact that @{term A}, @{term B} and @{term C} exhaust type @{typ three} is
best phrased as a case distinction theorem: if you want to prove @{prop"P x"}
(where @{term x} is of type @{typ three}) it suffices to prove @{prop"P A"},
@{prop"P B"} and @{prop"P C"}: *}

lemma three_cases: "\<lbrakk> P A; P B; P C \<rbrakk> \<Longrightarrow> P x"

txt{*\noindent Again this follows easily using the induction principle stemming from the type definition:*}

apply(induct_tac x)

txt{*
@{subgoals[display,indent=0]}
Simplification with @{thm[source]three_def} leads to the disjunction @{prop"y
= 0 \<or> y = 1 \<or> y = (2::nat)"} which \isa{auto} separates into three
subgoals, each of which is easily solved by simplification: *}

apply(auto simp add: three_def A_def B_def C_def)
done

text{*\noindent
This concludes the derivation of the characteristic theorems for
type @{typ three}.

The attentive reader has realized long ago that the
above lengthy definition can be collapsed into one line:
*}

datatype better_three = A | B | C

text{*\noindent
In fact, the \isacommand{datatype} command performs internally more or less
the same derivations as we did, which gives you some idea what life would be
like without \isacommand{datatype}.

Although @{typ three} could be defined in one line, we have chosen this
example to demonstrate \isacommand{typedef} because its simplicity makes the
key concepts particularly easy to grasp. If you would like to see a
non-trivial example that cannot be defined more directly, we recommend the
definition of \emph{finite multisets} in the Library~\cite{HOL-Library}.

Let us conclude by summarizing the above procedure for defining a new type.
Given some abstract axiomatic description $P$ of a type $ty$ in terms of a
set of functions $F$, this involves three steps:
\begin{enumerate}
\item Find an appropriate type $\tau$ and subset $A$ which has the desired
  properties $P$, and make a type definition based on this representation.
\item Define the required functions $F$ on $ty$ by lifting
analogous functions on the representation via $Abs_ty$ and $Rep_ty$.
\item Prove that $P$ holds for $ty$ by lifting $P$ from the representation.
\end{enumerate}
You can now forget about the representation and work solely in terms of the
abstract functions $F$ and properties $P$.%
\index{typedecl@\isacommand {typedef} (command)|)}%
\index{types!defining|)}
*}

(*<*)end(*>*)
