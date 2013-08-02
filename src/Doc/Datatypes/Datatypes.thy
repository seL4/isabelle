(*  Title:      Doc/Datatypes/Datatypes.thy
    Author:     Jasmin Blanchette, TU Muenchen

Tutorial for (co)datatype definitions with the new package.
*)

theory Datatypes
imports Setup
keywords
  "primrec_new" :: thy_decl and
  "primcorec" :: thy_decl
begin

(*<*)
(* FIXME: Evil setup until "primrec_new" and "primcorec" are in place. *)
ML_command {*
fun add_dummy_cmd _ _ lthy = lthy;

val _ = Outer_Syntax.local_theory @{command_spec "primrec_new"} ""
  (Parse.fixes -- Parse_Spec.where_alt_specs >> uncurry add_dummy_cmd);

val _ = Outer_Syntax.local_theory @{command_spec "primcorec"} ""
  (Parse.fixes -- Parse_Spec.where_alt_specs >> uncurry add_dummy_cmd);
*}
(*>*)


section {* Introduction
  \label{sec:introduction} *}

text {*
The 2013 edition of Isabelle introduced new definitional package for datatypes
and codatatypes. The datatype support is similar to that provided by the earlier
package due to Berghofer and Wenzel \cite{Berghofer-Wenzel:1999:TPHOL},
documented in the Isar reference manual \cite{isabelle-isar-ref};
indeed, replacing the keyword @{command datatype} by @{command datatype_new} is
usually all that is needed to port existing theories to use the new package.

Perhaps the main advantage of the new package is that it supports definitions
with recursion through a large class of non-datatypes, notably finite sets:
*}

    datatype_new 'a treeFS = NodeFS 'a "'a treeFS fset"

text {*
\noindent
Another strong point is that the package supports local definitions:
*}

    context linorder
    begin
      datatype_new flag = Less | Eq | Greater
    end

text {*
\noindent
The package also provides some convenience, notably automatically generated
destructors.

The command @{command datatype_new} is expected to displace @{command datatype}
in a future release. Authors of new theories are encouraged to use
@{command datatype_new}, and maintainers of older theories may want to consider
upgrading in the coming months.

In addition to plain inductive datatypes, the package supports coinductive
datatypes, or \emph{codatatypes}, which may have infinite values. For example,
the following command introduces a codatatype of infinite streams:
*}

    codatatype 'a stream = Stream 'a "'a stream"

text {*
\noindent
Mixed inductive--coinductive recursion is possible via nesting. Compare the
following four examples:
*}

    datatype_new 'a treeFF = NodeFF 'a "'a treeFF list"
    datatype_new 'a treeFI = NodeFI 'a "'a treeFF stream"
    codatatype 'a treeIF = NodeIF 'a "'a treeFF list"
    codatatype 'a treeII = NodeII 'a "'a treeFF stream"

text {*
The first two tree types allow only finite branches, whereas the last two allow
infinite branches. Orthogonally, the nodes in the first and third types have
finite branching, whereas those of the second and fourth have infinitely many
direct subtrees.

To use the package, it is necessary to import the @{theory BNF} theory, which
can be precompiled as the \textit{HOL-BNF} image. The following commands show
how to launch jEdit/PIDE with the image loaded and how to build the image
without launching jEdit:
*}

text {*
\noindent
\ \ \ \ \texttt{isabelle jedit -l HOL-BNF} \\
\noindent
\hbox{}\ \ \ \ \texttt{isabelle build -b HOL-BNF}
*}

text {*
The package, like its predecessor, fully adheres to the LCF philosophy
\cite{mgordon79}: The characteristic theorems associated with the specified
(co)datatypes are derived rather than introduced axiomatically.%
\footnote{Nonetheless, if the \textit{quick\_and\_dirty} option is enabled, some
of the internal constructions and most of the internal proof obligations are
skipped.}
The package's metatheory is described in a pair of papers
\cite{traytel-et-al-2012,blanchette-et-al-wit}.
*}

text {*
This tutorial is organized as follows:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item Section \ref{sec:defining-datatypes}, ``Defining Datatypes,''
describes how to specify datatypes using the @{command datatype_new} command.

\item Section \ref{sec:defining-recursive-functions}, ``Defining Recursive 
Functions,'' describes how to specify recursive functions using
\keyw{primrec\_new}, @{command fun}, and @{command function}.

\item Section \ref{sec:defining-codatatypes}, ``Defining Codatatypes,''
describes how to specify codatatypes using the @{command codatatype} command.

\item Section \ref{sec:defining-corecursive-functions}, ``Defining Corecursive 
Functions,'' describes how to specify corecursive functions using the
\keyw{primcorec} command.

\item Section \ref{sec:registering-bounded-natural-functors}, ``Registering 
Bounded Natural Functors,'' explains how to set up the (co)datatype package to
allow nested recursion through custom well-behaved type constructors.

\item Section \ref{sec:generating-free-constructor-theorems}, ``Generating Free 
Constructor Theorems,'' explains how to derive convenience theorems for free
constructors, as performed internally by @{command datatype_new} and
@{command codatatype}.

\item Section \ref{sec:standard-ml-interface}, ``Standard ML Interface,''
describes the package's programmatic interface.

\item Section \ref{sec:interoperability}, ``Interoperability,''
is concerned with the packages' interaction with other Isabelle packages and
tools, such as the code generator and the counterexample generators.

\item Section \ref{sec:known-bugs-and-limitations}, ``Known Bugs and 
Limitations,'' concludes with known open issues at the time of writing.
\end{itemize}


\newbox\boxA
\setbox\boxA=\hbox{\texttt{nospam}}

\newcommand\authoremaili{\texttt{blan{\color{white}nospam}\kern-\wd\boxA{}chette@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailii{\texttt{pope{\color{white}nospam}\kern-\wd\boxA{}scua@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailiii{\texttt{tray{\color{white}nospam}\kern-\wd\boxA{}tel@\allowbreak
in.\allowbreak tum.\allowbreak de}}

\noindent
Comments and bug reports concerning either
the tool or the manual should be directed to the authors at
\authoremaili, \authoremailii, and \authoremailiii.

\begin{framed}
\noindent
\textbf{Warning:} This document is under heavy construction. Please apologise
for its appearance and come back in a few months. If you have ideas regarding
material that should be included, please let the authors know.
\end{framed}

*}

section {* Defining Datatypes
  \label{sec:defining-datatypes} *}

text {*
This section describes how to specify datatypes using the @{command datatype_new}
command. The command is first illustrated through concrete examples featuring
different flavors of recursion. More examples can be found in the directory
\verb|~~/src/HOL/BNF/Examples|.
*}


subsection {* Examples
  \label{ssec:datatype-examples} *}

subsubsection {* Nonrecursive Types *}

text {*
enumeration type:
*}

    datatype_new trool = Truue | Faalse | Perhaaps

text {*
Haskell-style option type:
*}

    datatype_new 'a maybe = Nothing | Just 'a

text {*
triple:
*}

    datatype_new ('a, 'b, 'c) triple = Triple 'a 'b 'c


subsubsection {* Simple Recursion *}

text {*
simplest recursive type: natural numbers
*}

    datatype_new nat = Zero | Suc nat

text {*
lists were shown in the introduction

terminated lists are a variant:
*}

    datatype_new ('a, 'b) tlist = TNil 'b | TCons 'a "('a, 'b) tlist"

text {*
On the right-hand side of the equal sign, the usual Isabelle conventions apply:
Nonatomic types must be enclosed in double quotes.
*}


subsubsection {* Mutual Recursion *}

text {*
Mutual recursion = Define several types simultaneously, referring to each other.

Simple example: distinction between even and odd natural numbers:
*}

    datatype_new even_nat = Zero | Even_Suc odd_nat
    and odd_nat = Odd_Suc even_nat

text {*
More complex, and more realistic, example:
*}

    datatype_new ('a, 'b) expr =
      Term "('a, 'b) trm" | Sum "('a, 'b) trm" "('a, 'b) expr"
    and ('a, 'b) trm =
      Factor "('a, 'b) fact" | Prod "('a, 'b) fact" "('a, 'b) trm"
    and ('a, 'b) fact =
      Const 'a | Var 'b | Sub_Expr "('a, 'b) expr"


subsubsection {* Nested Recursion *}

text {*
Nested recursion = Have recursion through a type constructor.

The introduction showed some examples of trees with nesting through lists.

More complex example, which reuses our maybe and triple types:
*}

    datatype_new 'a triple_tree =
      Triple_Node "('a triple_tree maybe, bool, 'a triple_tree maybe) triple"

text {*
Recursion may not be arbitrary; e.g. impossible to define
*}

(*
    datatype_new 'a foo = Foo (*<*) datatype_new 'a bar = Bar  "'a foo \<Rightarrow> 'a foo"
*)

    datatype_new 'a evil = Evil (*<*)'a
    typ (*>*)"'a evil \<Rightarrow> 'a evil"

text {*
Issue: => allows recursion only on its right-hand side.
This issue is inherited by polymorphic datatypes (and codatatypes)
defined in terms of =>.
In general, type constructors "('a1, ..., 'an) k" allow recursion on a subset
of their type arguments.
*}


subsubsection {* Auxiliary Constants and Syntaxes *}

text {*
The @{command datatype_new} command introduces various constants in addition to the
constructors. Given a type @{text "('a1,\<dots>,'aM) t"} with constructors
@{text "t.C\<^sub>1"}, \ldots, @{text "t.C\<^sub>m"}, the following auxiliary
constants are introduced (among others):

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{Set functions} (\emph{natural transformations}):
@{text t_set1}, \ldots, @{text t_setM}

\item \emph{Map function} (\emph{functorial action}): @{text t_map}

\item \emph{Relator}: @{text t_rel}

\item \emph{Iterator}: @{text t_fold}

\item \emph{Recursor}: @{text t_rec}

\item \emph{Discriminators}: @{text "t.is_C\<^sub>1"}, \ldots,
@{text "t.is_C\<^sub>m"}

\item \emph{Selectors}:
@{text t.un_C}$_{11}$, \ldots, @{text t.un_C}$_{1n_1}$, \ldots,
@{text t.un_C}$_{m1}$, \ldots, @{text t.un_C}$_{mn_m}$
\end{itemize}

The discriminators and selectors are collectively called \emph{destructors}. The
@{text "t."} prefix is an optional component of the name and is normally hidden.

The set functions, map function, relator, discriminators, and selectors can be
given custom names, as in the example below:
*}

(*<*)hide_const Nil Cons hd tl(*>*)
    datatype_new (set: 'a) list (map: map rel: list_all2) =
      null: Nil (defaults tl: Nil)
    | Cons (hd: 'a) (tl: "'a list")

text {*
\noindent
The command introduces a discriminator @{const null} and a pair of selectors
@{const hd} and @{const tl} characterized as follows:
%
\[@{thm list.collapse(1)[of xs, no_vars]}
  \qquad @{thm list.collapse(2)[of xs, no_vars]}\]
%
For two-constructor datatypes, a single discriminator constant suffices. The
discriminator associated with @{const Cons} is simply @{text "\<not> null"}.

The \keyw{defaults} keyword following the @{const Nil} constructor specifies a
default value for selectors associated with other constructors. Here, it is
used to specify that the tail of the empty list is the empty list (instead of
being unspecified).

Because @{const Nil} is a nullary constructor, it is also possible to use @{text
"= Nil"} as a discriminator. This is specified by specifying @{text "="} instead
of the identifier @{const null} in the declaration above. Although this may look
appealing, the mixture of constructors and selectors in the resulting
characteristic theorems can lead Isabelle's automation to switch between the
constructor and the destructor view in surprising ways.
*}

text {*
The usual mixfix syntaxes are available for both types and constructors. For example:

%%% FIXME: remove trailing underscore and use locale trick instead once this is
%%% supported.
*}

    datatype_new ('a, 'b) prod (infixr "*" 20) =
      Pair 'a 'b

    datatype_new (set_: 'a) list_ =
      null: Nil ("[]")
    | Cons (hd: 'a) (tl: "'a list_") (infixr "#" 65)


subsection {* Syntax
  \label{ssec:datatype-syntax} *}

text {*
Datatype definitions have the following general syntax:

@{rail "
  @@{command datatype_new} @{syntax target}? @{syntax dt_options}? \\
    (@{syntax dt_name} '=' (@{syntax ctor} + '|') + @'and')
  ;
  @{syntax_def dt_options}: '(' ((@'no_dests' | @'rep_compat') + ',') ')'
"}

The syntactic quantity @{syntax target} can be used to specify a local context
(e.g., @{text "(in linorder)"}). It is documented in the Isar reference manual
\cite{isabelle-isar-ref}.

The optional target is followed by optional options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The \keyw{no\_dests} option indicates that no destructors (i.e.,
discriminators and selectors) should be generated.

\item
The \keyw{rep\_compat} option indicates that the names generated by the
package should contain optional (and normally not displayed) @{text "new."}
components to prevent clashes with a later call to @{command rep_datatype}. See
Section~\ref{ssec:datatype-compatibility-issues} for details.
\end{itemize}

The left-hand sides of the datatype equations specify the name of the type to
define, its type parameters, and optional additional information:

@{rail "
  @{syntax_def dt_name}: @{syntax tyargs}? @{syntax name}
    @{syntax map_rel}? @{syntax mixfix}?
  ;
  @{syntax_def tyargs}: @{syntax typefree} | '(' ((@{syntax name} ':')? @{syntax typefree} + ',') ')'
  ;
  @{syntax_def map_rel}: '(' ((('map' | 'rel') ':' @{syntax name}) +) ')'
"}

\noindent
The syntactic quantity @{syntax name} denotes an identifier, @{syntax typefree}
denotes fixed type variable (@{typ 'a}, @{typ 'b}, \ldots), and @{syntax
mixfix} denotes the usual parenthesized mixfix notation. They are documented in
the Isar reference manual \cite{isabelle-isar-ref}.

The optional names preceding the type variables allow to override the default
names of the set functions (@{text t_set1}, \ldots, @{text t_setM}).
Inside a mutually recursive datatype specification, all defined datatypes must
specify exactly the same type variables in the same order.

@{rail "
  @{syntax_def ctor}: (@{syntax name} ':')? @{syntax name} (@{syntax ctor_arg} * ) \\
    @{syntax sel_defaults}? @{syntax mixfix}?
"}

\noindent
The main constituents of a constructor specification is the name of the
constructor and the list of its argument types. An optional discriminator name
can be supplied at the front to override the default name
(@{text t.un_C}$_{ij}$).

@{rail "
  @{syntax_def ctor_arg}: @{syntax type} | '(' @{syntax name} ':' @{syntax type} ')'
"}

\noindent
In addition to the type of a constructor argument, it is possible to specify a
name for the corresponding selector to override the default name
(@{text t.un_C}$_{ij}$). The same selector names can be reused for several
constructors as long as they have the same type.

@{rail "
  @{syntax_def sel_defaults}: '(' @'defaults' (@{syntax name} ':' @{syntax term} +) ')'
"}

\noindent
Given a constructor
@{text "C \<Colon> \<sigma>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<sigma>\<^sub>p \<Rightarrow> \<sigma>"},
default values can be specified for any selector
@{text "un_D \<Colon> \<sigma> \<Rightarrow> \<tau>"}
associated with other constructors. The specified default value must have type
@{text "\<sigma>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<sigma>\<^sub>p \<Rightarrow> \<tau>"}
(i.e., it may dependend on @{text C}'s arguments).
*}

subsection {* Generated Theorems
  \label{ssec:datatype-generated-theorems} *}

text {*
  * free ctor theorems
    * case syntax

  * per-type theorems
    * sets, map, rel
    * induct, fold, rec
    * simps

  * multi-type (``common'') theorems
    * induct

  * mention what is registered with which attribute
    * and also nameless safes
*}


subsection {* Compatibility Issues
  \label{ssec:datatype-compatibility-issues} *}

text {*
  * main incompabilities between two packages
    * differences in theorem names (e.g. singular vs. plural for some props?)
    * differences in "simps"?
    * different recursor/induction in nested case
        * discussed in Section~\ref{sec:defining-recursive-functions}
    * different ML interfaces / extension mechanisms

  * register new datatype as old datatype
    * motivation:
      * do recursion through new datatype in old datatype
        (e.g. useful when porting to the new package one type at a time)
      * use old primrec
      * use fun
      * use extensions like size (needed for fun), the AFP order, Quickcheck,
        Nitpick
      * provide exactly the same theorems with the same names (compatibility)
    * option 1
      * \keyw{rep\_compat}
      * \keyw{rep\_datatype}
      * has some limitations
        * mutually recursive datatypes? (fails with rep\_datatype?)
        * nested datatypes? (fails with datatype\_new?)
    * option 2
      * \keyw{datatype\_compat}
      * not fully implemented yet?

  * register old datatype as new datatype
    * no clean way yet
    * if the goal is to do recursion through old datatypes, can register it as
      a BNF (Section XXX)
    * can also derive destructors etc. using @{command wrap_free_constructors}
      (Section XXX)
*}


section {* Defining Recursive Functions
  \label{sec:defining-recursive-functions} *}

text {*
This describes how to specify recursive functions over datatypes
specified using @{command datatype_new}. The focus in on the \keyw{primrec\_new}
command, which supports primitive recursion. A few examples feature the
@{command fun} and @{command function} commands, described in a separate
tutorial \cite{isabelle-function}.

%%% TODO: partial_function?
*}

text {*
More examples in \verb|~~/src/HOL/BNF/Examples|.
*}

subsection {* Examples
  \label{ssec:primrec-examples} *}

subsubsection {* Nonrecursive Types *}


subsubsection {* Simple Recursion *}


subsubsection {* Mutual Recursion *}


subsubsection {* Nested Recursion *}


subsubsection {* Nested-as-Mutual Recursion *}


subsection {* Syntax
  \label{ssec:primrec-syntax} *}

text {*
Primitive recursive functions have the following general syntax:

@{rail "
  @@{command primrec_new} @{syntax target}? @{syntax \"fixes\"} \\ @'where'
    (@{syntax primrec_equation} + '|')
  ;
  @{syntax_def primrec_equation}: @{syntax thmdecl}? @{syntax prop}
"}
*}


subsection {* Generated Theorems
  \label{ssec:primrec-generated-theorems} *}

text {*
  * synthesized nonrecursive definition
  * user specification is rederived from it, exactly as entered

  * induct
    * mutualized
    * without some needless induction hypotheses if not used
  * fold, rec
    * mutualized
*}

subsection {* Recursive Default Values for Selectors
  \label{ssec:recursive-default-values-for-selectors} *}

text {*
A datatype selector @{text un_D} can have a default value for each constructor
on which it is not otherwise specified. Occasionally, it is useful to have the
default value be defined recursively. This produces a chicken-and-egg situation
that appears unsolvable, because the datatype is not introduced yet at the
moment when the selectors are introduced. Of course, we can always define the
selectors manually afterward, but we then have to state and prove all the
characteristic theorems ourselves instead of letting the package do it.

Fortunately, there is a fairly elegant workaround that relies on overloading and
that avoids the tedium of manual derivations:

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
Introduce a fully unspecified constant @{text "un_D\<^sub>0 \<Colon> 'a"} using
@{keyword consts}.

\item
Define the datatype, specifying @{text "un_D\<^sub>0"} as the selector's default value.

\item
Define the behavior of @{text "un_D\<^sub>0"} on values of the newly introduced datatype
using the @{command overloading} command.

\item
Derive the desired equation on @{text un_D} from the characteristic equations
for @{text "un_D\<^sub>0"}.
\end{enumerate}

The following example illustrates this procedure:
*}

    consts termi\<^sub>0 :: 'a

    datatype_new (*<*)(rep_compat) (*>*)('a, 'b) tlist_ =
      TNil (termi: 'b) (defaults ttl: TNil)
    | TCons (thd: 'a) (ttl : "('a, 'b) tlist_") (defaults termi: "\<lambda>_ xs. termi\<^sub>0 xs")

(*<*)
    rep_datatype TNil TCons
    by (erule tlist_.induct, assumption) auto
(*>*)

    overloading
      termi\<^sub>0 \<equiv> "termi\<^sub>0 \<Colon> ('a, 'b) tlist_ \<Rightarrow> 'b"
    begin

(*<*)(*FIXME: use primrec_new and avoid rep_datatype*)(*>*)
    fun termi\<^sub>0 :: "('a, 'b) tlist_ \<Rightarrow> 'b" where
    "termi\<^sub>0 (TNil y) = y" |
    "termi\<^sub>0 (TCons x xs) = termi\<^sub>0 xs"

    end

    lemma terminal_TCons[simp]: "termi (TCons x xs) = termi xs"
    by (cases xs) auto


subsection {* Compatibility Issues
  \label{ssec:datatype-compatibility-issues} *}

text {*
  * different induction in nested case
    * solution: define nested-as-mutual functions with primrec,
      and look at .induct

  * different induction and recursor in nested case
    * only matters to low-level users; they can define a dummy function to force
      generation of mutualized recursor
*}


section {* Defining Codatatypes
  \label{sec:defining-codatatypes} *}

text {*
This section describes how to specify codatatypes using the @{command codatatype}
command.
*}


subsection {* Examples
  \label{ssec:codatatype-examples} *}

text {*
More examples in \verb|~~/src/HOL/BNF/Examples|.
*}


subsection {* Syntax
  \label{ssec:codatatype-syntax} *}

text {*
Definitions of codatatypes have almost exactly the same syntax as for datatypes
(Section~\ref{ssec:datatype-syntax}), with two exceptions: The command is called
@{command codatatype}; the \keyw{no\_dests} option is not available, because
destructors are a central notion for codatatypes.
*}

subsection {* Generated Theorems
  \label{ssec:codatatype-generated-theorems} *}


section {* Defining Corecursive Functions
  \label{sec:defining-corecursive-functions} *}

text {*
This section describes how to specify corecursive functions using the
\keyw{primcorec} command.

%%% TODO: partial_function? E.g. for defining tail recursive function on lazy
%%% lists (cf. terminal0 in TLList.thy)
*}


subsection {* Examples
  \label{ssec:primcorec-examples} *}

text {*
More examples in \verb|~~/src/HOL/BNF/Examples|.

Also, for default values, the same trick as for datatypes is possible for
codatatypes (Section~\ref{ssec:recursive-default-values-for-selectors}).
*}


subsection {* Syntax
  \label{ssec:primcorec-syntax} *}

text {*
Primitive corecrusvie definitions have the following general syntax:

@{rail "
  @@{command primcorec} @{syntax target}? @{syntax \"fixes\"} \\ @'where'
    (@{syntax primcorec_formula} + '|')
  ;
  @{syntax_def primcorec_formula}: @{syntax thmdecl}? @{syntax prop}
    (@'of' (@{syntax term} * ))?
"}
*}


subsection {* Generated Theorems
  \label{ssec:primcorec-generated-theorems} *}


section {* Registering Bounded Natural Functors
  \label{sec:registering-bounded-natural-functors} *}

text {*
This section explains how to set up the (co)datatype package to allow nested
recursion through custom well-behaved type constructors. The key concept is that
of a bounded natural functor (BNF).

    * @{command bnf}
    * @{command print_bnfs}
*}


subsection {* Example
  \label{ssec:bnf-examples} *}

text {*
More examples in \verb|~~/src/HOL/BNF/Basic_BNFs.thy| and
\verb|~~/src/HOL/BNF/More_BNFs.thy|.

Mention distinction between live and dead type arguments;
mention =>.
*}


subsection {* Syntax
  \label{ssec:bnf-syntax} *}


section {* Generating Free Constructor Theorems
  \label{sec:generating-free-constructor-theorems} *}

text {*
This section explains how to derive convenience theorems for free constructors,
as performed internally by @{command datatype_new} and @{command codatatype}.

  * need for this is rare but may arise if you want e.g. to add destructors to
    a type not introduced by ...

  * also useful for compatibility with old package, e.g. add destructors to
    old @{command datatype}

  * @{command wrap_free_constructors}
    * \keyw{no\_dests}, \keyw{rep\_compat}
*}


subsection {* Example
  \label{ssec:ctors-examples} *}


subsection {* Syntax
  \label{ssec:ctors-syntax} *}


subsection {* Generated Theorems
  \label{ssec:ctors-generated-theorems} *}


section {* Standard ML Interface
  \label{sec:standard-ml-interface} *}

text {*
This section describes the package's programmatic interface.
*}


section {* Interoperability
  \label{sec:interoperability} *}

text {*
This section is concerned with the packages' interaction with other Isabelle
packages and tools, such as the code generator and the counterexample
generators.
*}


subsection {* Transfer and Lifting
  \label{ssec:transfer-and-lifting} *}


subsection {* Code Generator
  \label{ssec:code-generator} *}


subsection {* Quickcheck
  \label{ssec:quickcheck} *}


subsection {* Nitpick
  \label{ssec:nitpick} *}


subsection {* Nominal Isabelle
  \label{ssec:nominal-isabelle} *}


section {* Known Bugs and Limitations
  \label{sec:known-bugs-and-limitations} *}

text {*
This section lists known open issues of the package.
*}

text {*
* primrec\_new and primcorec are vaporware

* slow n-ary mutual (co)datatype, avoid as much as possible (e.g. using nesting)

* issues with HOL-Proofs?

* partial documentation

* too much output by commands like "datatype_new" and "codatatype"

* no direct way to define recursive functions for default values -- but show trick
  based on overloading
*}


section {* Acknowledgments
  \label{sec:acknowledgments} *}

text {*
Tobias Nipkow and Makarius Wenzel made this work possible. Andreas Lochbihler
provided lots of comments on earlier versions of the package, especially for the
coinductive part. Brian Huffman suggested major simplifications to the internal
constructions, much of which has yet to be implemented. Florian Haftmann and
Christian Urban provided general advice advice on Isabelle and package writing.
Stefan Milius and Lutz Schr\"oder suggested an elegant prove to eliminate one of
the BNF assumptions.
*}

end
