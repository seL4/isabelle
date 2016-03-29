(*  Title:      Doc/Corec/Corec.thy
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Andrei Popescu, Middlesex University
    Author:     Dmitriy Traytel, ETH Zuerich

Tutorial for nonprimitively corecursive definitions.
*)

theory Corec
imports
  GCD
  "../Datatypes/Setup"
  "~~/src/HOL/Library/BNF_Corec"
  "~~/src/HOL/Library/FSet"
begin

section \<open>Introduction
  \label{sec:introduction}\<close>

text \<open>
...
@{cite "isabelle-datatypes"}

* friend
* up to

* versioning

BNF

link to papers

* plugins (code)
\<close>


section \<open>Introductory Examples
  \label{sec:introductory-examples}\<close>

text \<open>
\<close>


subsection \<open>Simple Corecursion
  \label{ssec:simple-corecursion}\<close>

text \<open>
The case studies by Rutten~@{cite rutten05} and Hinze~@{cite hinze10} on stream
calculi serve as our starting point. Streams can be defined as follows
(cf. @{file "~~/src/HOL/Library/Stream.thy"}):
\<close>

    codatatype 'a stream =
      SCons (shd: 'a) (stl: "'a stream")

text \<open>
The @{command corec} command makes it possible to define functions where the
corecursive call occurs under two or more constructors:
\<close>

    corec oneTwos :: "nat stream" where
      "oneTwos = SCons 1 (SCons 2 oneTwos)"

thm oneTwos.cong_intros

text \<open>
\noindent
This is already beyond the syntactic fragment supported by \keyw{primcorec}.

The following definition of pointwise sum can be performed with either
\keyw{primcorec} or @{command corec}:
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
The command emits two subgoals. The first one corresponds to the equation we
specified and is trivial to discharge. The second one is a parametricity subgoal
and can usually be discharged using the @{text transfer_prover} proof method.

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
The parametricity subgoal is given to @{text transfer_prover}.

The @{const sprod} and @{const sexp} functions provide shuffle product and
exponentiation on streams. We can use them to define the stream of factorial
numbers in two different ways:
\<close>

    corec factA :: "nat stream" where
      "factA = (let zs = SCons 1 factA in sprod zs zs)"

    corec factB :: "nat stream" where
      "factB = sexp (SCons 0 factB)"

text \<open>
The arguments of friendly operations can be of complex types involving the
target codatatype. The following example defines the supremum of a finite set of
streams by primitive corecursion and registers it as friendly:
\<close>

    corec (friend) sfsup :: "nat stream fset \<Rightarrow> nat stream" where
      "sfsup X = SCons (Sup (fset (fimage shd X))) (sfsup (fimage stl X))"

text \<open>
\noindent
In general, the arguments may be any BNF, with the restriction that the target
codatatype (@{typ "nat stream"}) may occur only in a live position of the BNF.
For this reason, the following operation, on unbounded sets, cannot be
registered as a friend:
\<close>

    corec ssup :: "nat stream set \<Rightarrow> nat stream" where
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

    corec (friend) tplus :: "('a :: plus) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
      "tplus t u =
       Node (lab t + lab u) (map (\<lambda>(t', u'). tplus t' u') (zip (sub t) (sub u)))"

text \<open>
\noindent
Here, @{const map} is the standard map function on lists, and @{const zip}
converts two parallel lists into a list of pairs. The @{const tplus} function is
primitively corecursive. Instead of @{text "corec (friend)"}, we could also have
used \keyw{primcorec} and @{command friend_of_corec}, as we did for
@{const ssum}.

Once @{const tplus} is registered as friendly, we can use it in the corecursive
call context:
\<close>

    corec (friend) ttimes :: "('a :: {plus,times}) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
      "ttimes t u = Node (lab t * lab u)
         (map (\<lambda>(t', u'). tplus (ttimes t u') (ttimes t' u)) (zip (sub t) (sub u)))"

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
reaching a guarded corecursive call.

Intuitively, the unguarded recursive call can be unfolded to arbitrary finite
depth, ultimately yielding a purely corecursive definition. An example is the
@{term primes} function from Di Gianantonio and Miculan
@{cite "di-gianantonio-miculan-2003"}:
\<close>

    corecursive primes :: "nat \<Rightarrow> nat \<Rightarrow> nat stream" where
      "primes m n =
       (if (m = 0 \<and> n > 1) \<or> coprime m n then
          SCons n (primes (m * n) (n + 1))
        else
          primes m (n + 1))"
      apply (relation "measure (\<lambda>(m, n).
        if n = 0 then 1 else if coprime m n then 0 else m - n mod m)")
       apply (auto simp: mod_Suc intro: Suc_lessI)
       apply (metis One_nat_def coprime_Suc_nat gcd.commute gcd_red_nat)
      by (metis diff_less_mono2 lessI mod_less_divisor)

text \<open>
\noindent
The @{command corecursive} command is a variant of @{command corec} that allows
us to specify a termination argument for any unguarded self-call.

When called with @{term "m = 1"} and @{term "n = 2"}, the @{const primes}
function computes the stream of prime numbers. The unguarded call in the
@{text else} branch increments @{term n} until it is coprime to the first
argument @{term m} (i.e., the greatest common divisor of @{term m} and
@{term n} is @{term 1}).

For any positive integers @{term m} and @{term n}, the numbers @{term m} and
@{term "m * n + 1"} are coprime, yielding an upper bound on the number of times
@{term n} is increased. Hence, the function will take the @{text else} branch at
most finitely often before taking the then branch and producing one constructor.
There is a slight complication when @{term "m = 0 \<and> n > 1"}: Without the first
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

    corec collatz :: "nat \<Rightarrow> nat stream" where
      "collatz n = (if even n \<and> n > 0 then collatz (n div 2)
         else SCons n (collatz (3 * n + 1)))"

text \<open>
A more elaborate case study, revolving around the filter function on lazy lists,
is presented in @{file "~~/src/HOL/Corec_Examples/LFilter.thy"}.
\<close>


subsection \<open>Self-Friendship
  \label{ssec:self-friendship}\<close>

text \<open>
Paradoxically, the package allows us to simultaneously define a function and use
it as its own friend, as in the following definition of a ``skewed product'':
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
the collection @{thm [source] stream.coinduct_upto}:
%
\begin{indentblock}
@{thm sfsup.coinduct[no_vars]}
\end{indentblock}
%
This rule is almost identical to structural coinduction, except that the
corecursive application of @{term R} is replaced by
@{term "stream.v5.congclp R"}. The @{const stream.v5.congclp} predicate is
equipped with the following introduction rules:

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

    corec (friend) square_elems :: "(nat, 'b) tllist \<Rightarrow> (nat, 'b) tllist" where
      "square_elems xs =
       (case xs of
         TNil z \<Rightarrow> TNil z
       | TCons y ys \<Rightarrow> TCons (y ^^ 2) (square_elems ys))"

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
To generate it, without having to define a new function with @{command corec},
we can use the following command:
\<close>

    coinduction_upto nat_int_tllist: "(nat, int) tllist"

text \<open>
\noindent
This produces the theorems @{thm [source] nat_int_tllist.coinduct_upto} and
@{thm [source] nat_int_tllist.cong_intros} (as well as the individually named
introduction rules) and extends @{thm [source] tllist.coinduct_upto} and
@{thm [source] tllist.cong_intros}.
\<close>


subsection \<open>Uniqueness Reasoning
  \label{ssec:uniqueness-reasoning}\<close>

text \<open>
It is sometimes possible to achieve better automation by using a more
specialized proof method than coinduction. Uniqueness principles maintain a good
balance between expressiveness and automation. They exploit the property that a
corecursive specification is the unique solution to a fixpoint equation.

The @{command corec}, @{command corecursive}, and @{command friend_of_corec}
commands generate a property @{text f.unique} about the function of interest
@{term f} that can be used to prove that any function that satisfies
@{term f}'s corecursive specification must be equal to @{term f}. For example:
\[@{thm ssum.unique[no_vars]}\]

The uniqueness principles are not restricted to functions defined using
@{command corec} or @{command corecursive} or registered with
@{command friend_of_corec}. Suppose @{term "t x"} is an arbitrary term
depending on @{term x}. The @{method corec_unique} proof method, provided by our
tool, transforms subgoals of the form
\[@{term "(\<forall>x. f x = H x f) \<Longrightarrow> f x = t x"}\]
into
\[@{term "\<forall>x. t x = H x t"}\]
The higher-order functional @{term H} must be such that the equation
@{term "f x = H x f"} would be a valid @{command corec} specification---but
without nested self-calls or unguarded calls. Thus, @{method corec_unique}
proves uniqueness of @{term t} with respect to the given fixpoint equation
regardless of how @{term t} was defined. For example:
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


section \<open>Command Syntax
  \label{sec:command-syntax}\<close>

subsection \<open>\keyw{corec} and \keyw{corecursive}
  \label{ssec:corec-and-corecursive}\<close>

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

The @{command corec} command is an abbreviation for @{command corecursive} with
@{text "apply transfer_prover"} or @{text "apply lexicographic_order"} to
discharge any emerging proof obligations.
\<close>


subsection \<open>\keyw{friend_of_corec}
  \label{ssec:friend-of-corec}\<close>

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
  \label{ssec:coinduction-upto}\<close>

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
...
\<close>


subsection \<open>\keyw{corec} and \keyw{corecursive}
  \label{ssec:corec-and-corecursive}\<close>

text \<open>
...
\<close>


subsection \<open>\keyw{friend_of_corec}
  \label{ssec:friend-of-corec}\<close>

text \<open>
...
\<close>


subsection \<open>\keyw{coinduction_upto}
  \label{ssec:coinduction-upto}\<close>

text \<open>
...
\<close>


section \<open>Proof Method
  \label{sec:proof-method}\<close>

text \<open>
...
\<close>


subsection \<open>\textit{corec_unique}
  \label{ssec:corec-unique}\<close>

text \<open>
...
\<close>


section \<open>Known Bugs and Limitations
  \label{sec:known-bugs-and-limitations}\<close>

text \<open>
This section lists the known bugs and limitations of the corecursion package at
the time of this writing.

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
\emph{TODO.} TODO.

  * no mutual types
  * limitation on type of friend
  * unfinished tactics
  * polymorphism of corecUU_transfer
  * alternative views
  * plugins

\end{enumerate}
\<close>

end
