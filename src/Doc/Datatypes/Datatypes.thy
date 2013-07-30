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

datatype_new 'a tree = Node 'a "('a tree fset)"

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

@{thm [display] list.collapse[no_vars]}

The command \cmd{datatype\_new} is expected to displace \cmd{datatype} in a future
release. Authors of new theories are encouraged to use \cmd{datatype\_new}, and
maintainers of older theories might want to consider upgrading now.

The package also provides codatatypes (or ``coinductive datatypes''), which may
have infinite values. The following command introduces a type of infinite
streams:
*}

codatatype 'a stream = Stream 'a "('a stream)"

text {*
\noindent
Mixed inductive--coinductive recursion is possible via nesting.
Compare the following four examples:
*}

datatype_new 'a treeFF = TreeFF 'a "('a treeFF list)"
datatype_new 'a treeFI = TreeFI 'a "('a treeFF stream)"
codatatype 'a treeIF = TreeIF 'a "('a treeFF list)"
codatatype 'a treeII = TreeII 'a "('a treeFF stream)"

text {*
To use the package, it is necessary to import the @{theory BNF} theory, which
can be precompiled as the \textit{HOL-BNF}:
*}

text {*
\noindent
\texttt{isabelle build -b HOL-BNF}
*}

text {*
  * TODO: LCF tradition
  * internals: LICS paper
*}

text {*
This tutorial is organized as follows:

  * datatypes
  * primitive recursive functions
  * codatatypes
  * primitive corecursive functions

the following sections focus on more technical aspects:
how to register bounded natural functors (BNFs), i.e., type
constructors via which (co)datatypes can (co)recurse,
and how to derive convenience theorems for free constructors,
as performed internally by \cmd{datatype\_new} and \cmd{codatatype}.

then: Standard ML interface

interaction with other tools
  * code generator (and Quickcheck)
  * Nitpick
*}

section {* Registering Bounded Natural Functors *}

subsection {* Introductory Example *}

subsection {* General Syntax *}

section {* Generating Free Constructor Theorems *}

section {* Defining Datatypes *}

subsection {* Introductory Examples *}

subsubsection {* Nonrecursive Types *}

subsubsection {* Simple Recursion *}

subsubsection {* Mutual Recursion *}

subsubsection {* Nested Recursion *}

subsubsection {* Auxiliary Constants *}

subsection {* General Syntax *}

subsection {* Characteristic Theorems *}

subsection {* Compatibility Issues *}


section {* Defining Primitive Recursive Functions *}

subsection {* Introductory Examples *}

subsection {* General Syntax *}

subsection {* Characteristic Theorems *}

subsection {* Compatibility Issues *}


section {* Defining Codatatypes *}

subsection {* Introductory Examples *}

subsection {* General Syntax *}

subsection {* Characteristic Theorems *}


section {* Defining Primitive Corecursive Functions *}

subsection {* Introductory Examples *}

subsection {* General Syntax *}

subsection {* Characteristic Theorems *}

subsection {* Compatibility Issues *}


section {* Registering Bounded Natural Functors *}

subsection {* Introductory Example *}

subsection {* General Syntax *}


section {* Generating Free Constructor Theorems *}

subsection {* Introductory Example *}

subsection {* General Syntax *}

section {* Registering Bounded Natural Functors *}

section {* Standard ML Interface *}

section {* Interoperability Issues *}

subsection {* Transfer and Lifting *}

subsection {* Code Generator *}

subsection {* Quickcheck *}

subsection {* Nitpick *}

subsection {* Nominal Isabelle *}

section {* Known Bugs and Limitations *}

text {*
* slow n-ary mutual (co)datatype, avoid as much as possible (e.g. using nesting)
*}

end
