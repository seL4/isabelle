(*<*)theory Typedef = Main:(*>*)

section{*Introducing New Types*}

text{*\label{sec:adv-typedef}
By now we have seen a number of ways for introducing new types, for example
type synonyms, recursive datatypes and records. For most applications, this
repertoire should be quite sufficient. Very occasionally you may feel the
need for a more advanced type. If you cannot do without that type, and you are
certain that it is not definable by any of the standard means,
then read on.
\begin{warn}
  Types in HOL must be non-empty; otherwise the quantifier rules would be
  unsound, because $\exists x.\ x=x$ is a theorem.
\end{warn}
*}

subsection{*Declaring New Types*}

text{*\label{sec:typedecl}
The most trivial way of introducing a new type is by a \bfindex{type
declaration}: *}

typedecl my_new_type

text{*\noindent\indexbold{*typedecl}%
This does not define @{typ my_new_type} at all but merely introduces its
name. Thus we know nothing about this type, except that it is
non-empty. Such declarations without definitions are
useful only if that type can be viewed as a parameter of a theory and we do
not intend to impose any restrictions on it. A typical example is given in
\S\ref{sec:VMC}, where we define transition relations over an arbitrary type
of states without any internal structure.

In principle we can always get rid of such type declarations by making those
types parameters of every other type, thus keeping the theory generic. In
practice, however, the resulting clutter can sometimes make types hard to
read.

If you are looking for a quick and dirty way of introducing a new type
together with its properties: declare the type and state its properties as
axioms. Example:
*}

axioms
just_one: "\<exists>x::my_new_type. \<forall>y. x = y"

text{*\noindent
However, we strongly discourage this approach, except at explorative stages
of your development. It is extremely easy to write down contradictory sets of
axioms, in which case you will be able to prove everything but it will mean
nothing.  Here the axiomatic approach is
unnecessary: a one-element type called @{typ unit} is already defined in HOL.
*}

subsection{*Defining New Types*}

text{*\label{sec:typedef}
Now we come to the most general method of safely introducing a new type, the
\bfindex{type definition}. All other methods, for example
\isacommand{datatype}, are based on it. The principle is extremely simple:
any non-empty subset of an existing type can be turned into a new type.  Thus
a type definition is merely a notational device: you introduce a new name for
a subset of an existing type. This does not add any logical power to HOL,
because you could base all your work directly on the subset of the existing
type. However, the resulting theories could easily become undigestible
because instead of implicit types you would have explicit sets in your
formulae.

Let us work a simple example, the definition of a three-element type.
It is easily represented by the first three natural numbers:
*}

typedef three = "{n. n \<le> 2}"

txt{*\noindent\indexbold{*typedef}%
In order to enforce that the representing set on the right-hand side is
non-empty, this definition actually starts a proof to that effect:
@{subgoals[display,indent=0]}
Fortunately, this is easy enough to show: take 0 as a witness.
*}

apply(rule_tac x = 0 in exI);
by simp

text{*
This type definition introduces the new type @{typ three} and asserts
that it is a \emph{copy} of the set @{term"{0,1,2}"}. This assertion
is expressed via a bijection between the \emph{type} @{typ three} and the
\emph{set} @{term"{0,1,2}"}. To this end, the command declares the following
constants behind the scenes:
\begin{center}
\begin{tabular}{rcl}
@{term three} &::& @{typ"nat set"} \\
@{term Rep_three} &::& @{typ"three \<Rightarrow> nat"}\\
@{term Abs_three} &::& @{typ"nat \<Rightarrow> three"}
\end{tabular}
\end{center}
Constant @{term three} is just an abbreviation (@{thm[source]three_def}):
@{thm[display]three_def}
The situation is best summarized with the help of the following diagram,
where squares are types and circles are sets:
\begin{center}
\unitlength1mm
\thicklines
\begin{picture}(100,40)
\put(3,13){\framebox(15,15){@{typ three}}}
\put(55,5){\framebox(30,30){@{term three}}}
\put(70,32){\makebox(0,0){@{typ nat}}}
\put(70,20){\circle{40}}
\put(10,15){\vector(1,0){60}}
\put(25,14){\makebox(0,0)[tl]{@{term Rep_three}}}
\put(70,25){\vector(-1,0){60}}
\put(25,26){\makebox(0,0)[bl]{@{term Abs_three}}}
\end{picture}
\end{center}
Finally, \isacommand{typedef} asserts that @{term Rep_three} is
surjective on the subset @{term three} and @{term Abs_three} and @{term
Rep_three} are inverses of each other:
\begin{center}
\begin{tabular}{rl}
@{thm Rep_three[no_vars]} &~~ (@{thm[source]Rep_three}) \\
@{thm Rep_three_inverse[no_vars]} &~~ (@{thm[source]Rep_three_inverse}) \\
@{thm Abs_three_inverse[no_vars]} &~~ (@{thm[source]Abs_three_inverse})
\end{tabular}
\end{center}
%
From this example it should be clear what \isacommand{typedef} does
in general given a name (here @{text three}) and a set
(here @{term"{n. n\<le>2}"}).

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

constdefs
  A:: three
 "A \<equiv> Abs_three 0"
  B:: three
 "B \<equiv> Abs_three 1"
  C :: three
 "C \<equiv> Abs_three 2";

text{*
So far, everything was easy. But it is clear that reasoning about @{typ
three} will be hell if we have to go back to @{typ nat} every time. Thus our
aim must be to raise our level of abstraction by deriving enough theorems
about type @{typ three} to characterize it completely. And those theorems
should be phrased in terms of @{term A}, @{term B} and @{term C}, not @{term
Abs_three} and @{term Rep_three}. Because of the simplicity of the example,
we merely need to prove that @{term A}, @{term B} and @{term C} are distinct
and that they exhaust the type.

We start with a helpful version of injectivity of @{term Abs_three} on the
representing subset:
*}

lemma [simp]:
 "\<lbrakk> x \<in> three; y \<in> three \<rbrakk> \<Longrightarrow> (Abs_three x = Abs_three y) = (x=y)";

txt{*\noindent
We prove each direction separately. From @{prop"Abs_three x = Abs_three y"}
we use @{thm[source]arg_cong} to apply @{term Rep_three} to both sides,
deriving @{prop[display]"Rep_three(Abs_three x) = Rep_three(Abs_three y)"}
Thus we get the required @{prop"x =
y"} by simplification with @{thm[source]Abs_three_inverse}. 
The other direction
is trivial by simplification:
*}

apply(rule iffI);
 apply(drule_tac f = Rep_three in arg_cong);
 apply(simp add:Abs_three_inverse);
by simp;

text{*\noindent
Analogous lemmas can be proved in the same way for arbitrary type definitions.

Distinctness of @{term A}, @{term B} and @{term C} follows immediately
if we expand their definitions and rewrite with the above simplification rule:
*}

lemma "A \<noteq> B \<and> B \<noteq> A \<and> A \<noteq> C \<and> C \<noteq> A \<and> B \<noteq> C \<and> C \<noteq> B";
by(simp add:A_def B_def C_def three_def);

text{*\noindent
Of course we rely on the simplifier to solve goals like @{prop"0 \<noteq> 1"}.

The fact that @{term A}, @{term B} and @{term C} exhaust type @{typ three} is
best phrased as a case distinction theorem: if you want to prove @{prop"P x"}
(where @{term x} is of type @{typ three}) it suffices to prove @{prop"P A"},
@{prop"P B"} and @{prop"P C"}. First we prove the analogous proposition for the
representation: *}

lemma cases_lemma: "\<lbrakk> Q 0; Q 1; Q 2; n : three \<rbrakk> \<Longrightarrow>  Q n";

txt{*\noindent
Expanding @{thm[source]three_def} yields the premise @{prop"n\<le>2"}. Repeated
elimination with @{thm[source]le_SucE}
@{thm[display]le_SucE}
reduces @{prop"n\<le>2"} to the three cases @{prop"n\<le>0"}, @{prop"n=1"} and
@{prop"n=2"} which are trivial for simplification:
*}

apply(simp add:three_def);
apply((erule le_SucE)+);
apply simp_all;
done

text{*
Now the case distinction lemma on type @{typ three} is easy to derive if you know how to:
*}

lemma three_cases: "\<lbrakk> P A; P B; P C \<rbrakk> \<Longrightarrow> P x";

txt{*\noindent
We start by replacing the @{term x} by @{term"Abs_three(Rep_three x)"}:
*}

apply(rule subst[OF Rep_three_inverse]);

txt{*\noindent
This substitution step worked nicely because there was just a single
occurrence of a term of type @{typ three}, namely @{term x}.
When we now apply the lemma, @{term Q} becomes @{term"\<lambda>n. P(Abs_three
n)"} because @{term"Rep_three x"} is the only term of type @{typ nat}:
*}

apply(rule cases_lemma);

txt{*
@{subgoals[display,indent=0]}
The resulting subgoals are easily solved by simplification:
*}

apply(simp_all add:A_def B_def C_def Rep_three);
done

text{*\noindent
This concludes the derivation of the characteristic theorems for
type @{typ three}.

The attentive reader has realized long ago that the
above lengthy definition can be collapsed into one line:
*}

datatype three' = A | B | C;

text{*\noindent
In fact, the \isacommand{datatype} command performs internally more or less
the same derivations as we did, which gives you some idea what life would be
like without \isacommand{datatype}.

Although @{typ three} could be defined in one line, we have chosen this
example to demonstrate \isacommand{typedef} because its simplicity makes the
key concepts particularly easy to grasp. If you would like to see a
nontrivial example that cannot be defined more directly, we recommend the
definition of \emph{finite multisets} in the HOL Library.

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
abstract functions $F$ and properties $P$.
*}

(*<*)end(*>*)
