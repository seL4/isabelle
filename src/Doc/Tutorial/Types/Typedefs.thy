(*<*)theory Typedefs imports Main begin(*>*)

section\<open>Introducing New Types\<close>

text\<open>\label{sec:adv-typedef}
For most applications, a combination of predefined types like \<^typ>\<open>bool\<close> and
\<open>\<Rightarrow>\<close> with recursive datatypes and records is quite sufficient. Very
occasionally you may feel the need for a more advanced type.  If you
are certain that your type is not definable by any of the
standard means, then read on.
\begin{warn}
  Types in HOL must be non-empty; otherwise the quantifier rules would be
  unsound, because $\exists x.\ x=x$ is a theorem.
\end{warn}
\<close>

subsection\<open>Declaring New Types\<close>

text\<open>\label{sec:typedecl}
\index{types!declaring|(}%
\index{typedecl@\isacommand {typedecl} (command)}%
The most trivial way of introducing a new type is by a \textbf{type
declaration}:\<close>

typedecl my_new_type

text\<open>\noindent
This does not define \<^typ>\<open>my_new_type\<close> at all but merely introduces its
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
\<close>

axiomatization where
just_one: "\<exists>x::my_new_type. \<forall>y. x = y"

text\<open>\noindent
However, we strongly discourage this approach, except at explorative stages
of your development. It is extremely easy to write down contradictory sets of
axioms, in which case you will be able to prove everything but it will mean
nothing.  In the example above, the axiomatic approach is
unnecessary: a one-element type called \<^typ>\<open>unit\<close> is already defined in HOL.
\index{types!declaring|)}
\<close>

subsection\<open>Defining New Types\<close>

text\<open>\label{sec:typedef}
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
\<close>

typedef three = "{0::nat, 1, 2}"

txt\<open>\noindent
In order to enforce that the representing set on the right-hand side is
non-empty, this definition actually starts a proof to that effect:
@{subgoals[display,indent=0]}
Fortunately, this is easy enough to show, even \isa{auto} could do it.
In general, one has to provide a witness, in our case 0:
\<close>

apply(rule_tac x = 0 in exI)
by simp

text\<open>
This type definition introduces the new type \<^typ>\<open>three\<close> and asserts
that it is a copy of the set \<^term>\<open>{0::nat,1,2}\<close>. This assertion
is expressed via a bijection between the \emph{type} \<^typ>\<open>three\<close> and the
\emph{set} \<^term>\<open>{0::nat,1,2}\<close>. To this end, the command declares the following
constants behind the scenes:
\begin{center}
\begin{tabular}{rcl}
\<^term>\<open>Rep_three\<close> &::& \<^typ>\<open>three \<Rightarrow> nat\<close>\\
\<^term>\<open>Abs_three\<close> &::& \<^typ>\<open>nat \<Rightarrow> three\<close>
\end{tabular}
\end{center}
The situation is best summarized with the help of the following diagram,
where squares denote types and the irregular region denotes a set:
\begin{center}
\includegraphics[scale=.8]{typedef}
\end{center}
Finally, \isacommand{typedef} asserts that \<^term>\<open>Rep_three\<close> is
surjective on the subset and \<^term>\<open>Abs_three\<close> and \<^term>\<open>Rep_three\<close> are inverses of each other:
\begin{center}
\begin{tabular}{@ {}r@ {\qquad\qquad}l@ {}}
@{thm Rep_three[no_vars]} & (@{thm[source]Rep_three}) \\
@{thm Rep_three_inverse[no_vars]} & (@{thm[source]Rep_three_inverse}) \\
@{thm Abs_three_inverse[no_vars]} & (@{thm[source]Abs_three_inverse})
\end{tabular}
\end{center}
%
From this example it should be clear what \isacommand{typedef} does
in general given a name (here \<open>three\<close>) and a set
(here \<^term>\<open>{0::nat,1,2}\<close>).

Our next step is to define the basic functions expected on the new type.
Although this depends on the type at hand, the following strategy works well:
\begin{itemize}
\item define a small kernel of basic functions that can express all other
functions you anticipate.
\item define the kernel in terms of corresponding functions on the
representing type using \<^term>\<open>Abs\<close> and \<^term>\<open>Rep\<close> to convert between the
two levels.
\end{itemize}
In our example it suffices to give the three elements of type \<^typ>\<open>three\<close>
names:
\<close>

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

text\<open>
So far, everything was easy. But it is clear that reasoning about \<^typ>\<open>three\<close> will be hell if we have to go back to \<^typ>\<open>nat\<close> every time. Thus our
aim must be to raise our level of abstraction by deriving enough theorems
about type \<^typ>\<open>three\<close> to characterize it completely. And those theorems
should be phrased in terms of \<^term>\<open>A\<close>, \<^term>\<open>B\<close> and \<^term>\<open>C\<close>, not \<^term>\<open>Abs_three\<close> and \<^term>\<open>Rep_three\<close>. Because of the simplicity of the example,
we merely need to prove that \<^term>\<open>A\<close>, \<^term>\<open>B\<close> and \<^term>\<open>C\<close> are distinct
and that they exhaust the type.

In processing our \isacommand{typedef} declaration, 
Isabelle proves several helpful lemmas. The first two
express injectivity of \<^term>\<open>Rep_three\<close> and \<^term>\<open>Abs_three\<close>:
\begin{center}
\begin{tabular}{@ {}r@ {\qquad}l@ {}}
@{thm Rep_three_inject[no_vars]} & (@{thm[source]Rep_three_inject}) \\
\begin{tabular}{@ {}l@ {}}
\<open>\<lbrakk>x \<in> {0, 1, 2}; y \<in> {0, 1, 2} \<rbrakk>\<close> \\
\<open>\<Longrightarrow> (Abs_three x = Abs_three y) = (x = y)\<close>
\end{tabular} & (@{thm[source]Abs_three_inject}) \\
\end{tabular}
\end{center}
The following ones allow to replace some \<open>x::three\<close> by
\<open>Abs_three(y::nat)\<close>, and conversely \<^term>\<open>y\<close> by \<^term>\<open>Rep_three x\<close>:
\begin{center}
\begin{tabular}{@ {}r@ {\qquad}l@ {}}
@{thm Rep_three_cases[no_vars]} & (@{thm[source]Rep_three_cases}) \\
@{thm Abs_three_cases[no_vars]} & (@{thm[source]Abs_three_cases}) \\
@{thm Rep_three_induct[no_vars]} & (@{thm[source]Rep_three_induct}) \\
@{thm Abs_three_induct[no_vars]} & (@{thm[source]Abs_three_induct}) \\
\end{tabular}
\end{center}
These theorems are proved for any type definition, with \<open>three\<close>
replaced by the name of the type in question.

Distinctness of \<^term>\<open>A\<close>, \<^term>\<open>B\<close> and \<^term>\<open>C\<close> follows immediately
if we expand their definitions and rewrite with the injectivity
of \<^term>\<open>Abs_three\<close>:
\<close>

lemma "A \<noteq> B \<and> B \<noteq> A \<and> A \<noteq> C \<and> C \<noteq> A \<and> B \<noteq> C \<and> C \<noteq> B"
by(simp add: Abs_three_inject A_def B_def C_def)

text\<open>\noindent
Of course we rely on the simplifier to solve goals like \<^prop>\<open>(0::nat) \<noteq> 1\<close>.

The fact that \<^term>\<open>A\<close>, \<^term>\<open>B\<close> and \<^term>\<open>C\<close> exhaust type \<^typ>\<open>three\<close> is
best phrased as a case distinction theorem: if you want to prove \<^prop>\<open>P x\<close>
(where \<^term>\<open>x\<close> is of type \<^typ>\<open>three\<close>) it suffices to prove \<^prop>\<open>P A\<close>,
\<^prop>\<open>P B\<close> and \<^prop>\<open>P C\<close>:\<close>

lemma three_cases: "\<lbrakk> P A; P B; P C \<rbrakk> \<Longrightarrow> P x"

txt\<open>\noindent Again this follows easily using the induction principle stemming from the type definition:\<close>

apply(induct_tac x)

txt\<open>
@{subgoals[display,indent=0]}
Simplification leads to the disjunction \<^prop>\<open>y
= 0 \<or> y = 1 \<or> y = (2::nat)\<close> which \isa{auto} separates into three
subgoals, each of which is easily solved by simplification:\<close>

apply(auto simp add: A_def B_def C_def)
done

text\<open>\noindent
This concludes the derivation of the characteristic theorems for
type \<^typ>\<open>three\<close>.

The attentive reader has realized long ago that the
above lengthy definition can be collapsed into one line:
\<close>

datatype better_three = A | B | C

text\<open>\noindent
In fact, the \isacommand{datatype} command performs internally more or less
the same derivations as we did, which gives you some idea what life would be
like without \isacommand{datatype}.

Although \<^typ>\<open>three\<close> could be defined in one line, we have chosen this
example to demonstrate \isacommand{typedef} because its simplicity makes the
key concepts particularly easy to grasp. If you would like to see a
non-trivial example that cannot be defined more directly, we recommend the
definition of \emph{finite multisets} in the Library~@{cite "HOL-Library"}.

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
\<close>

(*<*)end(*>*)
