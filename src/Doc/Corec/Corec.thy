(*  Title:      Doc/Corec/Corec.thy
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Andrei Popescu, Middlesex University
    Author:     Dmitriy Traytel, ETH Zuerich

Tutorial for nonprimitively corecursive definitions.
*)

theory Corec
imports Main Datatypes.Setup "HOL-Library.BNF_Corec"
  "HOL-Library.FSet"
begin

section \<open>Introduction
  \label{sec:introduction}\<close>

text \<open>
Isabelle's (co)datatype package @{cite "isabelle-datatypes"} offers a convenient
syntax for introducing codatatypes. For example, the type of (infinite) streams
can be defined as follows (cf. \<^file>\<open>~~/src/HOL/Library/Stream.thy\<close>):
\<close>

    codatatype 'a stream =
      SCons (shd: 'a) (stl: "'a stream")

text \<open>
\noindent
The (co)datatype package also provides two commands, \keyw{primcorec} and
\keyw{prim\-corec\-ur\-sive}, for defining primitively corecursive functions.

This tutorial presents a definitional package for functions beyond
primitive corecursion. It describes @{command corec} and related commands:\
@{command corecursive}, @{command friend_of_corec}, and @{command coinduction_upto}.
It also covers the @{method corec_unique} proof method.
The package is not part of @{theory Main}; it is located in
\<^file>\<open>~~/src/HOL/Library/BNF_Corec.thy\<close>.

The @{command corec} command generalizes \keyw{primcorec} in three main
respects. First, it allows multiple constructors around corecursive calls, where
\keyw{primcorec} expects exactly one. For example:
\<close>

    corec oneTwos :: "nat stream" where
      "oneTwos = SCons 1 (SCons 2 oneTwos)"

text \<open>
Second, @{command corec} allows other functions than constructors to appear in
the corecursive call context (i.e., around any self-calls on the right-hand side
of the equation). The requirement on these functions is that they must be
\emph{friendly}. Intuitively, a function is friendly if it needs to destruct
at most one constructor of input to produce one constructor of output.
We can register functions as friendly using the @{command friend_of_corec}
command, or by passing the @{text friend} option to @{command corec}. The
friendliness check relies on an internal syntactic check in combination with
a parametricity subgoal, which must be discharged manually (typically using
@{method transfer_prover} or @{method transfer_prover_eq}).

Third, @{command corec} allows self-calls that are not guarded by a constructor,
as long as these calls occur in a friendly context (a context consisting
exclusively of friendly functions) and can be shown to be terminating
(well founded). The mixture of recursive and corecursive calls in a single
function can be quite useful in practice.

Internally, the package synthesizes corecursors that take into account the
possible call contexts. The corecursor is accompanined by a corresponding,
equally general coinduction principle. The corecursor and the coinduction
principle grow in expressiveness as we interact with it. In process algebra
terminology, corecursion and coinduction take place \emph{up to} friendly
contexts.

The package fully adheres to the LCF philosophy @{cite mgordon79}: The
characteristic theorems associated with the specified corecursive functions are
derived rather than introduced axiomatically.
(Exceptionally, most of the internal proof obligations are omitted if the
@{text quick_and_dirty} option is enabled.)
The package is described in a pair of scientific papers
@{cite "blanchette-et-al-2015-fouco" and "blanchette-et-al-201x-amico"}. Some
of the text and examples below originate from there.

This tutorial is organized as follows:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item Section \ref{sec:introductory-examples}, ``Introductory Examples,''
describes how to specify corecursive functions and to reason about them.

\item Section \ref{sec:command-syntax}, ``Command Syntax,'' describes the syntax
of the commands offered by the package.

\item Section \ref{sec:generated-theorems}, ``Generated Theorems,'' lists the
theorems produced by the package's commands.

\item Section \ref{sec:proof-methods}, ``Proof Methods,'' briefly describes the
@{method corec_unique} and @{method transfer_prover_eq} proof methods.

\item Section \ref{sec:attribute}, ``Attribute,'' briefly describes the
@{attribute friend_of_corec_simps} attribute, which can be used to strengthen
the tactics underlying the @{command friend_of_corec} and @{command corec}
@{text "(friend)"} commands.

\item Section \ref{sec:known-bugs-and-limitations}, ``Known Bugs and
Limitations,'' concludes with known open issues.
\end{itemize}

Although it is more powerful than \keyw{primcorec} in many respects,
@{command corec} suffers from a number of limitations. Most notably, it does
not support mutually corecursive codatatypes, and it is less efficient than
\keyw{primcorec} because it needs to dynamically synthesize corecursors and
corresponding coinduction principles to accommodate the friends.

\newbox\boxA
\setbox\boxA=\hbox{\texttt{NOSPAM}}

\newcommand\authoremaili{\texttt{jasmin.blan{\color{white}NOSPAM}\kern-\wd\boxA{}chette@\allowbreak
gmail.\allowbreak com}}

Comments and bug reports concerning either the package or this tutorial should
be directed to the first author at \authoremaili{} or to the
\texttt{cl-isabelle-users} mailing list.
\<close>


section \<open>Introductory Examples
  \label{sec:introductory-examples}\<close>

text \<open>
The package is illustrated through concrete examples featuring different flavors
of corecursion. More examples can be found in the directory
\<^dir>\<open>~~/src/HOL/Corec_Examples\<close>.
\<close>


subsection \<open>Simple Corecursion
  \label{ssec:simple-corecursion}\<close>

text \<open>
The case studies by Rutten~@{cite rutten05} and Hinze~@{cite hinze10} on stream
calculi serve as our starting point. The following definition of pointwise sum
can be performed with either \keyw{primcorec} or @{command corec}:
\<close>

    primcorec ssum :: "('a :: plus) stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
      "ssum xs ys = SCons (shd xs + shd ys) (ssum (stl xs) (stl ys))"

text \<open>
\noindent
Pointwise sum meets the friendliness criterion. We register it as a friend using
the @{command friend_of_corec} command. The command requires us to give a
specification of @{const ssum} where a constructor (@{const SCons}) occurs at
the outermost position on the right-hand side. Here, we can simply reuse the
\keyw{primcorec} specification above:
\<close>

    friend_of_corec ssum :: "('a :: plus) stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
      "ssum xs ys = SCons (shd xs + shd ys) (ssum (stl xs) (stl ys))"
       apply (rule ssum.code)
      by transfer_prover

text \<open>
\noindent
The command emits two subgoals. The first subgoal corresponds to the equation we
specified and is trivial to discharge. The second subgoal is a parametricity
property that captures the the requirement that the function may destruct at
most one constructor of input to produce one constructor of output. This subgoal
can usually be discharged using the @{text transfer_prover} or
@{method transfer_prover_eq} proof method (Section~\ref{ssec:transfer-prover-eq}).
The latter replaces equality relations by their relator terms according to the
@{thm [source] relator_eq} theorem collection before it invokes
@{method transfer_prover}.

After registering @{const ssum} as a friend, we can use it in the corecursive
call context, either inside or outside the constructor guard:
\<close>

    corec fibA :: "nat stream" where
      "fibA = SCons 0 (ssum (SCons 1 fibA) fibA)"

text \<open>\blankline\<close>

    corec fibB :: "nat stream" where
      "fibB = ssum (SCons 0 (SCons 1 fibB)) (SCons 0 fibB)"

text \<open>
Using the @{text "friend"} option, we can simultaneously define a function and
register it as a friend:
\<close>

    corec (friend)
      sprod :: "('a :: {plus,times}) stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream"
    where
      "sprod xs ys =
       SCons (shd xs * shd ys) (ssum (sprod xs (stl ys)) (sprod (stl xs) ys))"

text \<open>\blankline\<close>

    corec (friend) sexp :: "nat stream \<Rightarrow> nat stream" where
      "sexp xs = SCons (2 ^^ shd xs) (sprod (stl xs) (sexp xs))"

text \<open>
\noindent
The parametricity subgoal is given to @{text transfer_prover_eq}
(Section~\ref{ssec:transfer-prover-eq}).

The @{const sprod} and @{const sexp} functions provide shuffle product and
exponentiation on streams. We can use them to define the stream of factorial
numbers in two different ways:
\<close>

    corec factA :: "nat stream" where
      "factA = (let zs = SCons 1 factA in sprod zs zs)"

text \<open>\blankline\<close>

    corec factB :: "nat stream" where
      "factB = sexp (SCons 0 factB)"

text \<open>
The arguments of friendly functions can be of complex types involving the
target codatatype. The following example defines the supremum of a finite set of
streams by primitive corecursion and registers it as friendly:
\<close>

    corec (friend) sfsup :: "nat stream fset \<Rightarrow> nat stream" where
      "sfsup X = SCons (Sup (fset (fimage shd X))) (sfsup (fimage stl X))"

text \<open>
\noindent
In general, the arguments may be any bounded natural functor (BNF)
@{cite "isabelle-datatypes"}, with the restriction that the target codatatype
(@{typ "nat stream"}) may occur only in a \emph{live} position of the BNF. For
this reason, the following function, on unbounded sets, cannot be registered as
a friend:
\<close>

    primcorec ssup :: "nat stream set \<Rightarrow> nat stream" where
      "ssup X = SCons (Sup (image shd X)) (ssup (image stl X))"


subsection \<open>Nested Corecursion
  \label{ssec:nested-corecursion}\<close>

text \<open>
The package generally supports arbitrary codatatypes with multiple constructors
and nesting through other type constructors (BNFs). Consider the following type
of finitely branching Rose trees of potentially infinite depth:
\<close>

    codatatype 'a tree =
      Node (lab: 'a) (sub: "'a tree list")

text \<open>
We first define the pointwise sum of two trees analogously to @{const ssum}:
\<close>

    corec (friend) tsum :: "('a :: plus) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
      "tsum t u =
       Node (lab t + lab u) (map (\<lambda>(t', u'). tsum t' u') (zip (sub t) (sub u)))"

text \<open>
\noindent
Here, @{const map} is the standard map function on lists, and @{const zip}
converts two parallel lists into a list of pairs. The @{const tsum} function is
primitively corecursive. Instead of @{command corec} @{text "(friend)"}, we could
also have used \keyw{primcorec} and @{command friend_of_corec}, as we did for
@{const ssum}.

Once @{const tsum} is registered as friendly, we can use it in the corecursive
call context of another function:
\<close>

    corec (friend) ttimes :: "('a :: {plus,times}) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
      "ttimes t u = Node (lab t * lab u)
         (map (\<lambda>(t', u'). tsum (ttimes t u') (ttimes t' u)) (zip (sub t) (sub u)))"

text \<open>
All the syntactic convenience provided by \keyw{primcorec} is also supported by
@{command corec}, @{command corecursive}, and @{command friend_of_corec}. In
particular, nesting through the function type can be expressed using
@{text \<lambda>}-abstractions and function applications rather than through composition
(@{term "op \<circ>"}, the map function for @{text \<Rightarrow>}). For example:
\<close>

    codatatype 'a language =
      Lang (\<oo>: bool) (\<dd>: "'a \<Rightarrow> 'a language")

text \<open>\blankline\<close>

    corec (friend) Plus :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
      "Plus r s = Lang (\<oo> r \<or> \<oo> s) (\<lambda>a. Plus (\<dd> r a) (\<dd> s a))"

text \<open>\blankline\<close>

    corec (friend) Times :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
      "Times r s = Lang (\<oo> r \<and> \<oo> s)
         (\<lambda>a. if \<oo> r then Plus (Times (\<dd> r a) s) (\<dd> s a) else Times (\<dd> r a) s)"

text \<open>\blankline\<close>

    corec (friend) Star :: "'a language \<Rightarrow> 'a language" where
      "Star r = Lang True (\<lambda>a. Times (\<dd> r a) (Star r))"

text \<open>\blankline\<close>

    corec (friend) Inter :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
      "Inter r s = Lang (\<oo> r \<and> \<oo> s) (\<lambda>a. Inter (\<dd> r a) (\<dd> s a))"

text \<open>\blankline\<close>

    corec (friend) PLUS :: "'a language list \<Rightarrow> 'a language" where
      "PLUS xs = Lang (\<exists>x \<in> set xs. \<oo> x) (\<lambda>a. PLUS (map (\<lambda>r. \<dd> r a) xs))"


subsection \<open>Mixed Recursion--Corecursion
  \label{ssec:mixed-recursion-corecursion}\<close>

text \<open>
It is often convenient to let a corecursive function perform some finite
computation before producing a constructor. With mixed recursion--corecursion, a
finite number of unguarded recursive calls perform this calculation before
reaching a guarded corecursive call. Intuitively, the unguarded recursive call
can be unfolded to arbitrary finite depth, ultimately yielding a purely
corecursive definition. An example is the @{term primes} function from Di
Gianantonio and Miculan @{cite "di-gianantonio-miculan-2003"}:
\<close>

    corecursive primes :: "nat \<Rightarrow> nat \<Rightarrow> nat stream" where
      "primes m n =
       (if (m = 0 \<and> n > 1) \<or> coprime m n then
          SCons n (primes (m * n) (n + 1))
        else
          primes m (n + 1))"
      apply (relation "measure (\<lambda>(m, n).
        if n = 0 then 1 else if coprime m n then 0 else m - n mod m)")
       apply (auto simp: mod_Suc diff_less_mono2 intro: Suc_lessI elim!: not_coprimeE)
      apply (metis dvd_1_iff_1 dvd_eq_mod_eq_0 mod_0 mod_Suc mod_Suc_eq mod_mod_cancel)
      done

text \<open>
\noindent
The @{command corecursive} command is a variant of @{command corec} that allows
us to specify a termination argument for any unguarded self-call.

When called with @{text "m = 1"} and @{text "n = 2"}, the @{const primes}
function computes the stream of prime numbers. The unguarded call in the
@{text else} branch increments @{term n} until it is coprime to the first
argument @{term m} (i.e., the greatest common divisor of @{term m} and
@{term n} is @{text 1}).

For any positive integers @{term m} and @{term n}, the numbers @{term m} and
@{text "m * n + 1"} are coprime, yielding an upper bound on the number of times
@{term n} is increased. Hence, the function will take the @{text else} branch at
most finitely often before taking the then branch and producing one constructor.
There is a slight complication when @{text "m = 0 \<and> n > 1"}: Without the first
disjunct in the @{text "if"} condition, the function could stall. (This corner
case was overlooked in the original example
@{cite "di-gianantonio-miculan-2003"}.)

In the following examples, termination is discharged automatically by
@{command corec} by invoking @{method lexicographic_order}:
\<close>

    corec catalan :: "nat \<Rightarrow> nat stream" where
      "catalan n =
       (if n > 0 then ssum (catalan (n - 1)) (SCons 0 (catalan (n + 1)))
        else SCons 1 (catalan 1))"

text \<open>\blankline\<close>

    corec collatz :: "nat \<Rightarrow> nat stream" where
      "collatz n = (if even n \<and> n > 0 then collatz (n div 2)
         else SCons n (collatz (3 * n + 1)))"

text \<open>
A more elaborate case study, revolving around the filter function on lazy lists,
is presented in \<^file>\<open>~~/src/HOL/Corec_Examples/LFilter.thy\<close>.
\<close>


subsection \<open>Self-Friendship
  \label{ssec:self-friendship}\<close>

text \<open>
The package allows us to simultaneously define a function and use it as its own
friend, as in the following definition of a ``skewed product'':
\<close>

    corec (friend)
      sskew :: "('a :: {plus,times}) stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream"
    where
      "sskew xs ys =
       SCons (shd xs * shd ys) (sskew (sskew xs (stl ys)) (sskew (stl xs) ys))"

text \<open>
\noindent
Such definitions, with nested self-calls on the right-hand side, cannot be
separated into a @{command corec} part and a @{command friend_of_corec} part.
\<close>


subsection \<open>Coinduction
  \label{ssec:coinduction}\<close>

text \<open>
Once a corecursive specification has been accepted, we normally want to reason
about it. The @{text codatatype} command generates a structural coinduction
principle that matches primitively corecursive functions. For nonprimitive
specifications, our package provides the more advanced proof principle of
\emph{coinduction up to congruence}---or simply \emph{coinduction up-to}.

The structural coinduction principle for @{typ "'a stream"}, called
@{thm [source] stream.coinduct}, is as follows:
%
\begin{indentblock}
@{thm stream.coinduct[no_vars]}
\end{indentblock}
%
Coinduction allows us to prove an equality @{text "l = r"} on streams by
providing a relation @{text R} that relates @{text l} and @{text r} (first
premise) and that constitutes a bisimulation (second premise). Streams that are
related by a bisimulation cannot be distinguished by taking observations (via
the selectors @{const shd} and @{const stl}); hence they must be equal.

The coinduction up-to principle after registering @{const sskew} as friendly is
available as @{thm [source] sskew.coinduct} and as one of the components of
the theorem collection @{thm [source] stream.coinduct_upto}:
%
\begin{indentblock}
@{thm sskew.coinduct[no_vars]}
\end{indentblock}
%
This rule is almost identical to structural coinduction, except that the
corecursive application of @{term R} is generalized to
@{term "stream.v5.congclp R"}.

The @{const stream.v5.congclp} predicate is equipped with the following
introduction rules:

\begin{indentblock}
\begin{description}

\item[@{thm [source] sskew.cong_base}\rm:] ~ \\
@{thm sskew.cong_base[no_vars]}

\item[@{thm [source] sskew.cong_refl}\rm:] ~ \\
@{thm sskew.cong_refl[no_vars]}

\item[@{thm [source] sskew.cong_sym}\rm:] ~ \\
@{thm sskew.cong_sym[no_vars]}

\item[@{thm [source] sskew.cong_trans}\rm:] ~ \\
@{thm sskew.cong_trans[no_vars]}

\item[@{thm [source] sskew.cong_SCons}\rm:] ~ \\
@{thm sskew.cong_SCons[no_vars]}

\item[@{thm [source] sskew.cong_ssum}\rm:] ~ \\
@{thm sskew.cong_ssum[no_vars]}

\item[@{thm [source] sskew.cong_sprod}\rm:] ~ \\
@{thm sskew.cong_sprod[no_vars]}

\item[@{thm [source] sskew.cong_sskew}\rm:] ~ \\
@{thm sskew.cong_sskew[no_vars]}

\end{description}
\end{indentblock}
%
The introduction rules are also available as
@{thm [source] sskew.cong_intros}.

Notice that there is no introduction rule corresponding to @{const sexp},
because @{const sexp} has a more restrictive result type than @{const sskew}
(@{typ "nat stream"} vs. @{typ "('a :: {plus,times}) stream"}.

The version numbers, here @{text v5}, distinguish the different congruence
closures generated for a given codatatype as more friends are registered. As
much as possible, it is recommended to avoid referring to them in proof
documents.

Since the package maintains a set of incomparable corecursors, there is also a
set of associated coinduction principles and a set of sets of introduction
rules. A technically subtle point is to make Isabelle choose the right rules in
most situations. For this purpose, the package maintains the collection
@{thm [source] stream.coinduct_upto} of coinduction principles ordered by
increasing generality, which works well with Isabelle's philosophy of applying
the first rule that matches. For example, after registering @{const ssum} as a
friend, proving the equality @{term "l = r"} on @{typ "nat stream"} might
require coinduction principle for @{term "nat stream"}, which is up to
@{const ssum}.

The collection @{thm [source] stream.coinduct_upto} is guaranteed to be complete
and up to date with respect to the type instances of definitions considered so
far, but occasionally it may be necessary to take the union of two incomparable
coinduction principles. This can be done using the @{command coinduction_upto}
command. Consider the following definitions:
\<close>

    codatatype ('a, 'b) tllist =
      TNil (terminal: 'b)
    | TCons (thd: 'a) (ttl: "('a, 'b) tllist")

text \<open>\blankline\<close>

    corec (friend) square_elems :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
      "square_elems xs =
       (case xs of
         TNil z \<Rightarrow> TNil z
       | TCons y ys \<Rightarrow> TCons (y ^^ 2) (square_elems ys))"

text \<open>\blankline\<close>

    corec (friend) square_terminal :: "('a, int) tllist \<Rightarrow> ('a, int) tllist" where
      "square_terminal xs =
       (case xs of
         TNil z \<Rightarrow> TNil (z ^^ 2)
       | TCons y ys \<Rightarrow> TCons y (square_terminal ys))"

text \<open>
At this point, @{thm [source] tllist.coinduct_upto} contains three variants of the
coinduction principles:
%
\begin{itemize}
\item @{typ "('a, int) tllist"} up to @{const TNil}, @{const TCons}, and
  @{const square_terminal};
\item @{typ "(nat, 'b) tllist"} up to @{const TNil}, @{const TCons}, and
  @{const square_elems};
\item @{typ "('a, 'b) tllist"} up to @{const TNil} and @{const TCons}.
\end{itemize}
%
The following variant is missing:
%
\begin{itemize}
\item @{typ "(nat, int) tllist"} up to @{const TNil}, @{const TCons},
  @{const square_elems}, and @{const square_terminal}.
\end{itemize}
%
To generate it without having to define a new function with @{command corec},
we can use the following command:
\<close>

    coinduction_upto nat_int_tllist: "(nat, int) tllist"

text \<open>
\noindent
This produces the theorems
%
\begin{indentblock}
@{thm [source] nat_int_tllist.coinduct_upto} \\
@{thm [source] nat_int_tllist.cong_intros}
\end{indentblock}
%
(as well as the individually named introduction rules) and extends
the dynamic collections @{thm [source] tllist.coinduct_upto} and
@{thm [source] tllist.cong_intros}.
\<close>


subsection \<open>Uniqueness Reasoning
  \label{ssec:uniqueness-reasoning}\<close>

text \<open>
It is sometimes possible to achieve better automation by using a more
specialized proof method than coinduction. Uniqueness principles maintain a good
balance between expressiveness and automation. They exploit the property that a
corecursive definition is the unique solution to a fixpoint equation.

The @{command corec}, @{command corecursive}, and @{command friend_of_corec}
commands generate a property @{text f.unique} about the function of interest
@{term f} that can be used to prove that any function that satisfies
@{term f}'s corecursive specification must be equal to~@{term f}. For example:
\[@{thm ssum.unique[no_vars]}\]

The uniqueness principles are not restricted to functions defined using
@{command corec} or @{command corecursive} or registered with
@{command friend_of_corec}. Suppose @{term "t x"} is an arbitrary term
depending on @{term x}. The @{method corec_unique} proof method, provided by our
tool, transforms subgoals of the form
\[@{term "(\<forall>x. f x = H x f) \<Longrightarrow> f x = t x"}\]
into
\[@{term "\<forall>x. t x = H x t"}\]
The higher-order functional @{term H} must be such that @{term "f x = H x f"}
would be a valid @{command corec} specification, but without nested self-calls
or unguarded (recursive) calls. Thus, @{method corec_unique} proves uniqueness
of @{term t} with respect to the given corecursive equation regardless of how
@{term t} was defined. For example:
\<close>

    lemma
      fixes f :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream"
      assumes "\<forall>xs ys. f xs ys =
        SCons (shd ys * shd xs) (ssum (f xs (stl ys)) (f (stl xs) ys))"
      shows "f = sprod"
        using assms
      proof corec_unique
        show "sprod = (\<lambda>xs ys :: nat stream.
            SCons (shd ys * shd xs) (ssum (sprod xs (stl ys)) (sprod (stl xs) ys)))"
          apply (rule ext)+
          apply (subst sprod.code)
          by simp
      qed

text \<open>
The proof method relies on some theorems generated by the package. If no function
over a given codatatype has been defined using @{command corec} or
@{command corecursive} or registered as friendly using @{command friend_of_corec},
the theorems will not be available yet. In such cases, the theorems can be
explicitly generated using the command
\<close>

    coinduction_upto stream: "'a stream"


section \<open>Command Syntax
  \label{sec:command-syntax}\<close>

subsection \<open>\keyw{corec} and \keyw{corecursive}
  \label{ssec:corec-and-corecursive-syntax}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "corec"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def "corecursive"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  (@@{command corec} | @@{command corecursive}) target? \<newline>
    @{syntax cr_options}? fix @'where' prop
  ;
  @{syntax_def cr_options}: '(' ((@{syntax plugins} | 'friend' | 'transfer') + ',') ')'
\<close>}

\medskip

\noindent
The @{command corec} and @{command corecursive} commands introduce a corecursive
function over a codatatype.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{fix} denotes name with an optional type signature, and \synt{prop} denotes
a HOL proposition @{cite "isabelle-isar-ref"}.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text plugins} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). By default, all plugins are enabled.

\item
The @{text friend} option indicates that the defined function should be
registered as a friend. This gives rise to additional proof obligations.

\item
The @{text transfer} option indicates that an unconditional transfer rule
should be generated and proved @{text "by transfer_prover"}. The
@{text "[transfer_rule]"} attribute is set on the generated theorem.
\end{itemize}

The @{command corec} command is an abbreviation for @{command corecursive}
with appropriate applications of @{method transfer_prover_eq}
(Section~\ref{ssec:transfer-prover-eq}) and @{method lexicographic_order} to
discharge any emerging proof obligations.
\<close>


subsection \<open>\keyw{friend_of_corec}
  \label{ssec:friend-of-corec-syntax}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "friend_of_corec"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  @@{command friend_of_corec} target? \<newline>
    @{syntax foc_options}? fix @'where' prop
  ;
  @{syntax_def foc_options}: '(' ((@{syntax plugins} | 'transfer') + ',') ')'
\<close>}

\medskip

\noindent
The @{command friend_of_corec} command registers a corecursive function as
friendly.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{fix} denotes name with an optional type signature, and \synt{prop} denotes
a HOL proposition @{cite "isabelle-isar-ref"}.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text plugins} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). By default, all plugins are enabled.

\item
The @{text transfer} option indicates that an unconditional transfer rule
should be generated and proved @{text "by transfer_prover"}. The
@{text "[transfer_rule]"} attribute is set on the generated theorem.
\end{itemize}
\<close>


subsection \<open>\keyw{coinduction_upto}
  \label{ssec:coinduction-upto-syntax}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "coinduction_upto"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command coinduction_upto} target? name ':' type
\<close>}

\medskip

\noindent
The @{command coinduction_upto} generates a coinduction up-to rule for a given
instance of a (possibly polymorphic) codatatype and notes the result with the
specified prefix.

The syntactic entity \synt{name} denotes an identifier and \synt{type} denotes a
type @{cite "isabelle-isar-ref"}.
\<close>


section \<open>Generated Theorems
  \label{sec:generated-theorems}\<close>

text \<open>
The full list of named theorems generated by the package can be obtained by
issuing the command \keyw{print_theorems} immediately after the datatype definition.
This list excludes low-level theorems that reveal internal constructions. To
make these accessible, add the line
\<close>

    declare [[bnf_internals]]
(*<*)
    declare [[bnf_internals = false]]
(*>*)

text \<open>
In addition to the theorem listed below for each command provided by the
package, all commands update the dynamic theorem collections

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{coinduct_upto}]

\item[@{text "t."}\hthm{cong_intros}]

\end{description}
\end{indentblock}
%
for the corresponding codatatype @{text t} so that they always contain the most
powerful coinduction up-to principles derived so far.
\<close>


subsection \<open>\keyw{corec} and \keyw{corecursive}
  \label{ssec:corec-and-corecursive-theorems}\<close>

text \<open>
For a function @{term f} over codatatype @{text t}, the @{command corec} and
@{command corecursive} commands generate the following properties (listed for
@{const sexp}, cf. Section~\ref{ssec:simple-corecursion}):

\begin{indentblock}
\begin{description}

\item[@{text "f."}\hthm{code} @{text "[code]"}\rm:] ~ \\
@{thm sexp.code[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
@{cite "isabelle-datatypes"}.

\item[@{text "f."}\hthm{coinduct} @{text "[consumes 1, case_names t, case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]"}\rm:] ~ \\
@{thm sexp.coinduct[no_vars]}

\item[@{text "f."}\hthm{cong_intros}\rm:] ~ \\
@{thm sexp.cong_intros[no_vars]}

\item[@{text "f."}\hthm{unique}\rm:] ~ \\
@{thm sexp.unique[no_vars]} \\
This property is not generated for mixed recursive--corecursive definitions.

\item[@{text "f."}\hthm{inner_induct}\rm:] ~ \\
This property is only generated for mixed recursive--corecursive definitions.
For @{const primes} (Section~\ref{ssec:mixed-recursion-corecursion}, it reads as
follows: \\[\jot]
@{thm primes.inner_induct[no_vars]}

\end{description}
\end{indentblock}

\noindent
The individual rules making up @{text "f.cong_intros"} are available as

\begin{indentblock}
\begin{description}

\item[@{text "f."}\hthm{cong_base}]

\item[@{text "f."}\hthm{cong_refl}]

\item[@{text "f."}\hthm{cong_sym}]

\item[@{text "f."}\hthm{cong_trans}]

\item[@{text "f."}\hthm{cong_C}@{text "\<^sub>1"}, \ldots, @{text "f."}\hthm{cong_C}@{text "\<^sub>n"}] ~ \\
where @{text "C\<^sub>1"}, @{text "\<dots>"}, @{text "C\<^sub>n"} are @{text t}'s
constructors

\item[@{text "f."}\hthm{cong_f}@{text "\<^sub>1"}, \ldots, @{text "f."}\hthm{cong_f}@{text "\<^sub>m"}] ~ \\
where @{text "f\<^sub>1"}, @{text "\<dots>"}, @{text "f\<^sub>m"} are the available
friends for @{text t}

\end{description}
\end{indentblock}
\<close>


subsection \<open>\keyw{friend_of_corec}
  \label{ssec:friend-of-corec-theorems}\<close>

text \<open>
The @{command friend_of_corec} command generates the same theorems as
@{command corec} and @{command corecursive}, except that it adds an optional
@{text "friend."} component to the names to prevent potential clashes (e.g.,
@{text "f.friend.code"}).
\<close>


subsection \<open>\keyw{coinduction_upto}
  \label{ssec:coinduction-upto-theorems}\<close>

text \<open>
The @{command coinduction_upto} command generates the following properties
(listed for @{text nat_int_tllist}):

\begin{indentblock}
\begin{description}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t."}\hthm{coinduct_upto} @{text "[consumes 1, case_names t,"} \\
  \phantom{@{text "t."}\hthm{coinduct_upto} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
@{thm nat_int_tllist.coinduct_upto[no_vars]}

\item[@{text "t."}\hthm{cong_intros}\rm:] ~ \\
@{thm nat_int_tllist.cong_intros[no_vars]}

\end{description}
\end{indentblock}

\noindent
The individual rules making up @{text "t.cong_intros"} are available
separately as @{text "t.cong_base"}, @{text "t.cong_refl"}, etc.\
(Section~\ref{ssec:corec-and-corecursive-theorems}).
\<close>


section \<open>Proof Methods
  \label{sec:proof-methods}\<close>

subsection \<open>\textit{corec_unique}
  \label{ssec:corec-unique}\<close>

text \<open>
The @{method corec_unique} proof method can be used to prove the uniqueness of
a corecursive specification. See Section~\ref{ssec:uniqueness-reasoning} for
details.
\<close>


subsection \<open>\textit{transfer_prover_eq}
  \label{ssec:transfer-prover-eq}\<close>

text \<open>
The @{method transfer_prover_eq} proof method replaces the equality relation
@{term "op ="} with compound relator expressions according to
@{thm [source] relator_eq} before calling @{method transfer_prover} on the
current subgoal. It tends to work better than plain @{method transfer_prover} on
the parametricity proof obligations of @{command corecursive} and
@{command friend_of_corec}, because they often contain equality relations on
complex types, which @{method transfer_prover} cannot reason about.
\<close>


section \<open>Attribute
  \label{sec:attribute}\<close>


subsection \<open>\textit{friend_of_corec_simps}
  \label{ssec:friend-of-corec-simps}\<close>

text \<open>
The @{attribute friend_of_corec_simps} attribute declares naturality theorems
to be used by @{command friend_of_corec} and @{command corec} @{text "(friend)"} in
deriving the user specification from reduction to primitive corecursion.
Internally, these commands derive naturality theorems from the parametricity proof
obligations dischared by the user or the @{method transfer_prover_eq} method, but
this derivation fails if in the arguments of a higher-order constant a type variable
occurs on both sides of the function type constructor. The required naturality
theorem can then be declared with @{attribute friend_of_corec_simps}. See
@{file "~~/src/HOL/Corec_Examples/Tests/Iterate_GPV.thy"} for an example.
\<close>


section \<open>Known Bugs and Limitations
  \label{sec:known-bugs-and-limitations}\<close>

text \<open>
This section lists the known bugs and limitations of the corecursion package at
the time of this writing.

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
\emph{Mutually corecursive codatatypes are not supported.}

\item
\emph{The signature of friend functions may not depend on type variables beyond
those that appear in the codatatype.}

\item
\emph{The internal tactics may fail on legal inputs.}
In some cases, this limitation can be circumvented using the
@{attribute friend_of_corec_simps} attribute
(Section~\ref{ssec:friend-of-corec-simps}).

\item
\emph{The @{text transfer} option is not implemented yet.}

\item
\emph{The constructor and destructor views offered by {\upshape\keyw{primcorec}}
are not supported by @{command corec} and @{command corecursive}.}

\item
\emph{There is no mechanism for registering custom plugins.}

\item
\emph{The package does not interact well with locales.}

\item
\emph{The undocumented @{text corecUU_transfer} theorem is not as polymorphic as
it could be.}

\item
\emph{All type variables occurring in the arguments of a friendly function must occur
as direct arguments of the type constructor of the resulting type.}

\end{enumerate}
\<close>

end
