(*  Title:      Doc/Datatypes/Datatypes.thy
    Author:     Jasmin Blanchette, TU Muenchen

Tutorial for (co)datatype definitions with the new package.
*)

theory Datatypes
imports BNF
begin

section {* Introduction *}

text {*
The 2013 edition of Isabelle introduced new definitional package for datatypes
and codatatypes. The datatype support is similar to that provided by the earlier
package due to Berghofer and Wenzel \cite{Berghofer-Wenzel:1999:TPHOL};
indeed, replacing \cmd{datatype} by \cmd{datatype\_new} is usually sufficient
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
generated destructors. For example, the command
*}

(*<*)hide_const Nil Cons hd tl(*>*)
    datatype_new 'a list = null: Nil | Cons (hd: 'a) (tl: "'a list")

text {*
\noindent
introduces a discriminator @{const null} and a pair of selectors @{const hd} and
@{const tl} characterized as follows:
%
\[@{thm list.collapse(1)[no_vars]}\qquad @{thm list.collapse(2)[no_vars]}\]

The command \cmd{datatype\_new} is expected to displace \cmd{datatype} in a future
release. Authors of new theories are encouraged to use \cmd{datatype\_new}, and
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
\item Section \ref{sec:defining-datatypes}, ``Defining Datatypes,''
describes how to specify datatypes using the \cmd{datatype\_new} command.

\item Section \ref{sec:defining-recursive-functions}, ``Defining Recursive 
Functions,'' describes how to specify recursive functions using
\cmd{primrec\_new}, \cmd{fun}, and \cmd{function}.

\item Section \ref{sec:defining-codatatypes}, ``Defining Codatatypes,''
describes how to specify codatatypes using the \cmd{codatatype} command.

\item Section \ref{sec:defining-corecursive-functions}, ``Defining Corecursive 
Functions,'' describes how to specify corecursive functions using the
\cmd{primcorec} command.

\item Section \ref{sec:registering-bounded-natural-functors}, ``Registering 
Bounded Natural Functors,'' explains how to set up the (co)datatype package to
allow nested recursion through custom well-behaved type constructors.

\item Section \ref{sec:generating-free-constructor-theorems}, ``Generating Free 
Constructor Theorems,'' explains how to derive convenience theorems for free
constructors, as performed internally by \cmd{datatype\_new} and
\cmd{codatatype}.

\item Section \ref{sec:standard-ml-interface}, ``Standard ML Interface,''
describes the package's programmatic interface.

\item Section \ref{sec:interoperability}, ``Interoperability,''
is concerned with the packages' interaction with other Isabelle packages and
tools, such as the code generator and the counterexample generators.

\item Section \ref{sec:known-bugs-and-limitations}, ``Known Bugs and 
Limitations,'' concludes with open issues.
\end{itemize}
*}

section {* Defining Datatypes%
  \label{sec:defining-datatypes} *}

text {*
This section describes how to specify datatypes using the \cmd{datatype\_new}
command. The command is first illustrated through concrete examples featuring
different flavors of recursion. More examples are available in
\verb|~~/src/HOL/BNF/Examples|. The syntax is largely modeled after that of the
existing \cmd{datatype} command.
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
* destructors
* also mention special syntaxes
*}

subsection {* General Syntax *}

subsection {* Characteristic Theorems *}

subsection {* Compatibility Issues *}


section {* Defining Recursive Functions%
  \label{sec:defining-recursive-functions} *}

text {*
This describes how to specify recursive functions over datatypes
specified using \cmd{datatype\_new}. The focus in on the \cmd{primrec\_new}
command, which supports primitive recursion. A few examples feature the
\cmd{fun} and \cmd{function} commands, described in a separate tutorial  
\cite{isabelle-function}.
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
This section describes how to specify codatatypes using the \cmd{codatatype}
command.
*}

subsection {* Introductory Examples *}

text {*
More examples in \verb|~~/src/HOL/BNF/Examples|.
*}

subsection {* General Syntax *}

subsection {* Characteristic Theorems *}


section {* Defining Corecursive Functions%
  \label{sec:defining-corecursive-functions} *}

text {*
This section describes how to specify corecursive functions using the
\cmd{primcorec} command.
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
as performed internally by \cmd{datatype\_new} and \cmd{codatatype}.

  * need for this is rare but may arise if you want e.g. to add destructors to
    a type not introduced by ...

  * also useful for compatibility with old package, e.g. add destructors to
    old \cmd{datatype}
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
*}

end
