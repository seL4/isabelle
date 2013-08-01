(*  Title:      Doc/Datatypes/Datatypes.thy
    Author:     Jasmin Blanchette, TU Muenchen

Tutorial for (co)datatype definitions with the new package.
*)

theory Datatypes
imports Setup
begin

section {* Introduction *}

text {*
The 2013 edition of Isabelle introduced new definitional package for datatypes
and codatatypes. The datatype support is similar to that provided by the earlier
package due to Berghofer and Wenzel \cite{Berghofer-Wenzel:1999:TPHOL};
indeed, replacing @{command datatype} by @{command datatype_new} is usually sufficient
to port existing specifications to the new package. What makes the new package
attractive is that it supports definitions with recursion through a large class
of non-datatypes, notably finite sets:
*}

    datatype_new 'a treeFS = TreeFS 'a "'a treeFS fset"

text {*
\noindent
Another advantage of the new package is that it supports local definitions:
*}

    context linorder
    begin
      datatype_new flag = Less | Eq | Greater
    end

text {*
\noindent
Finally, the package also provides some convenience, notably automatically
generated destructors.

The command @{command datatype_new} is expected to displace @{command datatype} in a future
release. Authors of new theories are encouraged to use @{command datatype_new}, and
maintainers of older theories may want to consider upgrading in the coming months.

The package also provides codatatypes (or ``coinductive datatypes''), which may
have infinite values. The following command introduces a codatatype of infinite
streams:
*}

    codatatype 'a stream = Stream 'a "'a stream"

text {*
\noindent
Mixed inductive--coinductive recursion is possible via nesting.
Compare the following four examples:
*}

    datatype_new 'a treeFF = TreeFF 'a "'a treeFF list"
    datatype_new 'a treeFI = TreeFI 'a "'a treeFF stream"
    codatatype 'a treeIF = TreeIF 'a "'a treeFF list"
    codatatype 'a treeII = TreeII 'a "'a treeFF stream"

text {*
To use the package, it is necessary to import the @{theory BNF} theory, which
can be precompiled as the \textit{HOL-BNF} image. The following commands show
how to launch jEdit/PIDE with the image loaded and how to build the image
without launching jEdit:
*}

text {*
\noindent
\ \ \ \ \texttt{isabelle jedit -l HOL-BNF} \\
\ \ \ \ \texttt{isabelle build -b HOL-BNF}
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
for its appearance and come back in a few months.
\end{framed}

*}

section {* Defining Datatypes%
  \label{sec:defining-datatypes} *}

text {*
This section describes how to specify datatypes using the @{command datatype_new}
command. The command is first illustrated through concrete examples featuring
different flavors of recursion. More examples can be found in the directory
\verb|~~/src/HOL/BNF/Examples|.
*}


subsection {* Introductory Examples *}

subsubsection {* Nonrecursive Types *}

text {*
enumeration type:
*}

    datatype_new trool = Truue | Faalse | Maaybe

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
      Factor "('a, 'b) factor" | Prod "('a, 'b) factor" "('a, 'b) trm"
    and ('a, 'b) factor =
      Const 'a | Var 'b | Sub_Expr "('a, 'b) expr"


subsubsection {* Nested Recursion *}

text {*
Nested recursion = Have recursion through a type constructor.

The introduction showed some examples of trees with nesting through lists.

More complex example, which reuses our maybe and triple types:
*}

    datatype_new 'a triple_tree =
      Triple_Tree "('a triple_tree maybe, bool, 'a triple_tree maybe) triple"

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
@{text t.C1}, \ldots, @{text t.C}$\!M,$ the following auxiliary constants are
introduced (among others):

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{Set functions} (\emph{natural transformations}): @{text t_set1},
\ldots, @{text t_set}$M$

\item \emph{Map function} (\emph{functorial action}): @{text t_map}

\item \emph{Relator}: @{text t_rel}

\item \emph{Iterator}: @{text t_fold}

\item \emph{Recursor}: @{text t_rec}

\item \emph{Discriminators}: @{text t.is_C1}, \ldots, @{text t.is_C}$\!M$

\item \emph{Selectors}:
@{text t.un_C11}, \ldots, @{text t.un_C1}$k_1$, \ldots,
@{text t.un_C}$\!M$@{text 1}, \ldots, @{text t.un_C}$\!Mk_M$
\end{itemize}

The discriminators and selectors are collectively called \emph{destructors}.
The @{text "t."} prefix is optional.

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


subsection {* General Syntax *}

text {*
Datatype definitions have the following general syntax:

@{rail "
  @@{command datatype_new} ('(' (@{syntax dt_option} + ',') ')')? \\
    (@{syntax dt_name} '=' (@{syntax ctor} + '|') + @'and')
"}

Two options are supported:

@{rail "
  @{syntax_def dt_option}: @'no_dests' | @'rep_compat'
"}

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

Left-hand sides specify the name of the type to define, its type parameters,
and more:

@{rail "
  @{syntax_def dt_name}: @{syntax type_params}? @{syntax name} \\
    @{syntax map_rel}? @{syntax mixfix}?
  ;
  @{syntax_def type_params}: @{syntax typefree} | '(' ((@{syntax name} ':')? @{syntax typefree} + ',') ')'
  ;
  @{syntax_def map_rel}: '(' ((('map' | 'rel') ':' @{syntax name}) +) ')'
"}

@{syntax name} specifies the type name ...

@{syntax typefree} is type variable ('a, 'b, \ldots)
The names are for the set functions.

Additional constraint: All mutually recursive datatypes defined together must
specify the same type variables in the same order.

@{syntax mixfix} is the usual parenthesized mixfix notation, documented in the
Isar reference manual \cite{isabelle-isar-ref}.

@{rail "
  @{syntax_def ctor}: (@{syntax name} ':')? @{syntax name} (@{syntax ctor_arg} *) \\
    @{syntax sel_defaults}? @{syntax mixfix}?
"}


First, optional name: discriminator. Second, mandatory name: name of
constructor. Default names for discriminators are generated.

@{rail "
  @{syntax_def ctor_arg}: @{syntax type} | '(' (@{syntax name} ':')? @{syntax type} ')'
  ;
  @{syntax_def sel_defaults}: '(' @'defaults' (@{syntax name} ':' @{syntax term} *) ')'
"}
*}


subsection {* Characteristic Theorems *}


subsection {* Compatibility Issues%
  \label{ssec:datatype-compatibility-issues} *}


section {* Defining Recursive Functions%
  \label{sec:defining-recursive-functions} *}

text {*
This describes how to specify recursive functions over datatypes
specified using @{command datatype_new}. The focus in on the \keyw{primrec\_new}
command, which supports primitive recursion. A few examples feature the
@{command fun} and @{command function} commands, described in a separate
tutorial \cite{isabelle-function}.
%%% TODO: partial_function?
*}


subsection {* Introductory Examples *}

text {*
More examples in \verb|~~/src/HOL/BNF/Examples|.
*}


subsection {* General Syntax *}


subsection {* Characteristic Theorems *}


subsection {* Compatibility Issues *}


section {* Defining Codatatypes%
  \label{sec:defining-codatatypes} *}

text {*
This section describes how to specify codatatypes using the @{command codatatype}
command.
*}


subsection {* Introductory Examples *}

text {*
More examples in \verb|~~/src/HOL/BNF/Examples|.
*}


subsection {* General Syntax *}

text {*
\keyw{no\_dests} is not available.
*}

subsection {* Characteristic Theorems *}


section {* Defining Corecursive Functions%
  \label{sec:defining-corecursive-functions} *}

text {*
This section describes how to specify corecursive functions using the
\keyw{primcorec} command.
*}


subsection {* Introductory Examples *}

text {*
More examples in \verb|~~/src/HOL/BNF/Examples|.
*}


subsection {* General Syntax *}


subsection {* Characteristic Theorems *}


section {* Registering Bounded Natural Functors%
  \label{sec:registering-bounded-natural-functors} *}

text {*
This section explains how to set up the (co)datatype package to allow nested
recursion through custom well-behaved type constructors. The key concept is that
of a bounded natural functor (BNF).
*}


subsection {* Introductory Example *}

text {*
More examples in \verb|~~/src/HOL/BNF/Basic_BNFs.thy| and
\verb|~~/src/HOL/BNF/More_BNFs.thy|.

Mention distinction between live and dead type arguments;
mention =>.
*}


subsection {* General Syntax *}


section {* Generating Free Constructor Theorems%
  \label{sec:generating-free-constructor-theorems} *}

text {*
This section explains how to derive convenience theorems for free constructors,
as performed internally by @{command datatype_new} and @{command codatatype}.

  * need for this is rare but may arise if you want e.g. to add destructors to
    a type not introduced by ...

  * also useful for compatibility with old package, e.g. add destructors to
    old @{command datatype}
*}


subsection {* Introductory Example *}


subsection {* General Syntax *}


section {* Standard ML Interface%
  \label{sec:standard-ml-interface} *}

text {*
This section describes the package's programmatic interface.
*}


section {* Interoperability%
  \label{sec:interoperability} *}

text {*
This section is concerned with the packages' interaction with other Isabelle
packages and tools, such as the code generator and the counterexample
generators.
*}


subsection {* Transfer and Lifting *}


subsection {* Code Generator *}


subsection {* Quickcheck *}


subsection {* Nitpick *}


subsection {* Nominal Isabelle *}


section {* Known Bugs and Limitations%
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


section {* Acknowledgments%
  \label{sec:acknowledgments} *}

text {*
  * same people as usual
    * Tobias Nipkow
    * Makarius Wenzel
    * Andreas Lochbihler
    * Brian Huffman
  * also:
    * Stefan Milius
    * Lutz Schr\"oder
*}

end
