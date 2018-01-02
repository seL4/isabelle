(*  Title:      Doc/Datatypes/Datatypes.thy
    Author:     Julian Biendarra, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, Ecole de technologie superieure
    Author:     Lorenz Panny, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen

Tutorial for (co)datatype definitions.
*)

theory Datatypes
imports
  Setup
  "HOL-Library.BNF_Axiomatization"
  "HOL-Library.Cardinal_Notations"
  "HOL-Library.Countable"
  "HOL-Library.FSet"
  "HOL-Library.Simps_Case_Conv"
begin

section \<open>Introduction
  \label{sec:introduction}\<close>

text \<open>
The 2013 edition of Isabelle introduced a definitional package for freely
generated datatypes and codatatypes. This package replaces the earlier
implementation due to Berghofer and Wenzel @{cite "Berghofer-Wenzel:1999:TPHOL"}.
Perhaps the main advantage of the new package is that it supports recursion
through a large class of non-datatypes, such as finite sets:
\<close>

    datatype 'a tree\<^sub>f\<^sub>s = Node\<^sub>f\<^sub>s (lbl\<^sub>f\<^sub>s: 'a) (sub\<^sub>f\<^sub>s: "'a tree\<^sub>f\<^sub>s fset")

text \<open>
\noindent
Another strong point is the support for local definitions:
\<close>

    context linorder
    begin
    datatype flag = Less | Eq | Greater
    end

text \<open>
\noindent
Furthermore, the package provides a lot of convenience, including automatically
generated discriminators, selectors, and relators as well as a wealth of
properties about them.

In addition to inductive datatypes, the package supports coinductive
datatypes, or \emph{codatatypes}, which allow infinite values. For example, the
following command introduces the type of lazy lists, which comprises both finite
and infinite values:
\<close>

(*<*)
    locale early
    locale late
(*>*)
    codatatype (*<*)(in early) (*>*)'a llist = LNil | LCons 'a "'a llist"

text \<open>
\noindent
Mixed inductive--coinductive recursion is possible via nesting. Compare the
following four Rose tree examples:
\<close>

    datatype (*<*)(in early) (*>*)'a tree\<^sub>f\<^sub>f = Node\<^sub>f\<^sub>f 'a "'a tree\<^sub>f\<^sub>f list"
    datatype (*<*)(in early) (*>*)'a tree\<^sub>f\<^sub>i = Node\<^sub>f\<^sub>i 'a "'a tree\<^sub>f\<^sub>i llist"
    codatatype (*<*)(in early) (*>*)'a tree\<^sub>i\<^sub>f = Node\<^sub>i\<^sub>f 'a "'a tree\<^sub>i\<^sub>f list"
    codatatype (*<*)(in early) (*>*)'a tree\<^sub>i\<^sub>i = Node\<^sub>i\<^sub>i 'a "'a tree\<^sub>i\<^sub>i llist"

text \<open>
The first two tree types allow only paths of finite length, whereas the last two
allow infinite paths. Orthogonally, the nodes in the first and third types have
finitely many direct subtrees, whereas those of the second and fourth may have
infinite branching.

The package is part of @{theory Main}. Additional functionality is provided by
the theory \<^file>\<open>~~/src/HOL/Library/BNF_Axiomatization.thy\<close>.

The package, like its predecessor, fully adheres to the LCF philosophy
@{cite mgordon79}: The characteristic theorems associated with the specified
(co)datatypes are derived rather than introduced axiomatically.%
\footnote{However, some of the
internal constructions and most of the internal proof obligations are omitted
if the @{text quick_and_dirty} option is enabled.}
The package is described in a number of scientific papers
@{cite "traytel-et-al-2012" and "blanchette-et-al-2014-impl" and
"panny-et-al-2014" and "blanchette-et-al-2015-wit"}.
The central notion is that of a \emph{bounded natural functor} (BNF)---a
well-behaved type constructor for which nested (co)recursion is supported.

This tutorial is organized as follows:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item Section \ref{sec:defining-datatypes}, ``Defining Datatypes,''
describes how to specify datatypes using the @{command datatype} command.

\item Section \ref{sec:defining-primitively-recursive-functions}, ``Defining
Primitively Recursive Functions,'' describes how to specify functions
using @{command primrec}. (A separate tutorial @{cite "isabelle-function"}
describes the more powerful \keyw{fun} and \keyw{function} commands.)

\item Section \ref{sec:defining-codatatypes}, ``Defining Codatatypes,''
describes how to specify codatatypes using the @{command codatatype} command.

\item Section \ref{sec:defining-primitively-corecursive-functions},
``Defining Primitively Corecursive Functions,'' describes how to specify
functions using the @{command primcorec} and
@{command primcorecursive} commands. (A separate tutorial
@{cite "isabelle-corec"} describes the more powerful \keyw{corec} and
\keyw{corecursive} commands.)

\item Section \ref{sec:registering-bounded-natural-functors}, ``Registering
Bounded Natural Functors,'' explains how to use the @{command bnf} command
to register arbitrary type constructors as BNFs.

\item Section
\ref{sec:deriving-destructors-and-theorems-for-free-constructors},
``Deriving Destructors and Theorems for Free Constructors,'' explains how to
use the command @{command free_constructors} to derive destructor constants
and theorems for freely generated types, as performed internally by
@{command datatype} and @{command codatatype}.

%\item Section \ref{sec:using-the-standard-ml-interface}, ``Using the Standard
%ML Interface,'' describes the package's programmatic interface.

\item Section \ref{sec:selecting-plugins}, ``Selecting Plugins,'' is concerned
with the package's interoperability with other Isabelle packages and tools, such
as the code generator, Transfer, Lifting, and Quickcheck.

\item Section \ref{sec:known-bugs-and-limitations}, ``Known Bugs and
Limitations,'' concludes with known open issues.
\end{itemize}

\newbox\boxA
\setbox\boxA=\hbox{\texttt{NOSPAM}}

\newcommand\authoremaili{\texttt{jasmin.blan{\color{white}NOSPAM}\kern-\wd\boxA{}chette@\allowbreak
gmail.\allowbreak com}}

Comments and bug reports concerning either the package or this tutorial should
be directed to the second author at \authoremaili{} or to the
\texttt{cl-isabelle-users} mailing list.
\<close>


section \<open>Defining Datatypes
  \label{sec:defining-datatypes}\<close>

text \<open>
Datatypes can be specified using the @{command datatype} command.
\<close>


subsection \<open>Introductory Examples
  \label{ssec:datatype-introductory-examples}\<close>

text \<open>
Datatypes are illustrated through concrete examples featuring different flavors
of recursion. More examples can be found in the directory
\<^dir>\<open>~~/src/HOL/Datatype_Examples\<close>.
\<close>


subsubsection \<open>Nonrecursive Types
  \label{sssec:datatype-nonrecursive-types}\<close>

text \<open>
Datatypes are introduced by specifying the desired names and argument types for
their constructors. \emph{Enumeration} types are the simplest form of datatype.
All their constructors are nullary:
\<close>

    datatype trool = Truue | Faalse | Perhaaps

text \<open>
\noindent
@{const Truue}, @{const Faalse}, and @{const Perhaaps} have the type @{typ trool}.

Polymorphic types are possible, such as the following option type, modeled after
its homologue from the @{theory Option} theory:
\<close>

(*<*)
    hide_const None Some map_option
    hide_type option
(*>*)
    datatype 'a option = None | Some 'a

text \<open>
\noindent
The constructors are @{text "None :: 'a option"} and
@{text "Some :: 'a \<Rightarrow> 'a option"}.

The next example has three type parameters:
\<close>

    datatype ('a, 'b, 'c) triple = Triple 'a 'b 'c

text \<open>
\noindent
The constructor is
@{text "Triple :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> ('a, 'b, 'c) triple"}.
Unlike in Standard ML, curried constructors are supported. The uncurried variant
is also possible:
\<close>

    datatype ('a, 'b, 'c) triple\<^sub>u = Triple\<^sub>u "'a * 'b * 'c"

text \<open>
\noindent
Occurrences of nonatomic types on the right-hand side of the equal sign must be
enclosed in double quotes, as is customary in Isabelle.
\<close>


subsubsection \<open>Simple Recursion
  \label{sssec:datatype-simple-recursion}\<close>

text \<open>
Natural numbers are the simplest example of a recursive type:
\<close>

    datatype nat = Zero | Succ nat

text \<open>
\noindent
Lists were shown in the introduction. Terminated lists are a variant that
stores a value of type @{typ 'b} at the very end:
\<close>

    datatype (*<*)(in early) (*>*)('a, 'b) tlist = TNil 'b | TCons 'a "('a, 'b) tlist"


subsubsection \<open>Mutual Recursion
  \label{sssec:datatype-mutual-recursion}\<close>

text \<open>
\emph{Mutually recursive} types are introduced simultaneously and may refer to
each other. The example below introduces a pair of types for even and odd
natural numbers:
\<close>

    datatype even_nat = Even_Zero | Even_Succ odd_nat
    and odd_nat = Odd_Succ even_nat

text \<open>
\noindent
Arithmetic expressions are defined via terms, terms via factors, and factors via
expressions:
\<close>

    datatype ('a, 'b) exp =
      Term "('a, 'b) trm" | Sum "('a, 'b) trm" "('a, 'b) exp"
    and ('a, 'b) trm =
      Factor "('a, 'b) fct" | Prod "('a, 'b) fct" "('a, 'b) trm"
    and ('a, 'b) fct =
      Const 'a | Var 'b | Expr "('a, 'b) exp"


subsubsection \<open>Nested Recursion
  \label{sssec:datatype-nested-recursion}\<close>

text \<open>
\emph{Nested recursion} occurs when recursive occurrences of a type appear under
a type constructor. The introduction showed some examples of trees with nesting
through lists. A more complex example, that reuses our @{type option} type,
follows:
\<close>

    datatype 'a btree =
      BNode 'a "'a btree option" "'a btree option"

text \<open>
\noindent
Not all nestings are admissible. For example, this command will fail:
\<close>

    datatype 'a wrong = W1 | W2 (*<*)'a
    typ (*>*)"'a wrong \<Rightarrow> 'a"

text \<open>
\noindent
The issue is that the function arrow @{text "\<Rightarrow>"} allows recursion
only through its right-hand side. This issue is inherited by polymorphic
datatypes defined in terms of~@{text "\<Rightarrow>"}:
\<close>

    datatype ('a, 'b) fun_copy = Fun "'a \<Rightarrow> 'b"
    datatype 'a also_wrong = W1 | W2 (*<*)'a
    typ (*>*)"('a also_wrong, 'a) fun_copy"

text \<open>
\noindent
The following definition of @{typ 'a}-branching trees is legal:
\<close>

    datatype 'a ftree = FTLeaf 'a | FTNode "'a \<Rightarrow> 'a ftree"

text \<open>
\noindent
And so is the definition of hereditarily finite sets:
\<close>

    datatype hfset = HFSet "hfset fset"

text \<open>
\noindent
In general, type constructors @{text "('a\<^sub>1, \<dots>, 'a\<^sub>m) t"}
allow recursion on a subset of their type arguments @{text 'a\<^sub>1}, \ldots,
@{text 'a\<^sub>m}. These type arguments are called \emph{live}; the remaining
type arguments are called \emph{dead}. In @{typ "'a \<Rightarrow> 'b"} and
@{typ "('a, 'b) fun_copy"}, the type variable @{typ 'a} is dead and
@{typ 'b} is live.

Type constructors must be registered as BNFs to have live arguments. This is
done automatically for datatypes and codatatypes introduced by the
@{command datatype} and @{command codatatype} commands.
Section~\ref{sec:registering-bounded-natural-functors} explains how to
register arbitrary type constructors as BNFs.

Here is another example that fails:
\<close>

    datatype 'a pow_list = PNil 'a (*<*)'a
    datatype 'a pow_list' = PNil' 'a (*>*)| PCons "('a * 'a) pow_list"

text \<open>
\noindent
This attempted definition features a different flavor of nesting, where the
recursive call in the type specification occurs around (rather than inside)
another type constructor.
\<close>


subsubsection \<open>Auxiliary Constants
  \label{sssec:datatype-auxiliary-constants}\<close>

text \<open>
The @{command datatype} command introduces various constants in addition to
the constructors. With each datatype are associated set functions, a map
function, a predicator, a relator, discriminators, and selectors, all of which can be given
custom names. In the example below, the familiar names @{text null}, @{text hd},
@{text tl}, @{text set}, @{text map}, and @{text list_all2} override the
default names @{text is_Nil}, @{text un_Cons1}, @{text un_Cons2},
@{text set_list}, @{text map_list}, and @{text rel_list}:
\<close>

(*<*)
    no_translations
      "[x, xs]" == "x # [xs]"
      "[x]" == "x # []"

    no_notation
      Nil ("[]") and
      Cons (infixr "#" 65)

    hide_type list
    hide_const Nil Cons case_list hd tl set map list_all2 rec_list size_list list_all

    context early
    begin
(*>*)
    datatype (set: 'a) list =
      null: Nil
    | Cons (hd: 'a) (tl: "'a list")
    for
      map: map
      rel: list_all2
      pred: list_all
    where
      "tl Nil = Nil"

text \<open>
\noindent
The types of the constants that appear in the specification are listed below.

\medskip

\begin{tabular}{@ {}ll@ {}}
Constructors: &
  @{text "Nil :: 'a list"} \\
&
  @{text "Cons :: 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"} \\
Discriminator: &
  @{text "null :: 'a list \<Rightarrow> bool"} \\
Selectors: &
  @{text "hd :: 'a list \<Rightarrow> 'a"} \\
&
  @{text "tl :: 'a list \<Rightarrow> 'a list"} \\
Set function: &
  @{text "set :: 'a list \<Rightarrow> 'a set"} \\
Map function: &
  @{text "map :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"} \\
Relator: &
  @{text "list_all2 :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"}
\end{tabular}

\medskip

The discriminator @{const null} and the selectors @{const hd} and @{const tl}
are characterized by the following conditional equations:
%
\[@{thm list.collapse(1)[of xs, no_vars]}
  \qquad @{thm list.collapse(2)[of xs, no_vars]}\]
%
For two-constructor datatypes, a single discriminator constant is sufficient.
The discriminator associated with @{const Cons} is simply
@{term "\<lambda>xs. \<not> null xs"}.

The \keyw{where} clause at the end of the command specifies a default value for
selectors applied to constructors on which they are not a priori specified.
In the example, it is used to ensure that the tail of the empty list is itself
(instead of being left unspecified).

Because @{const Nil} is nullary, it is also possible to use
@{term "\<lambda>xs. xs = Nil"} as a discriminator. This is the default behavior
if we omit the identifier @{const null} and the associated colon. Some users
argue against this, because the mixture of constructors and selectors in the
characteristic theorems can lead Isabelle's automation to switch between the
constructor and the destructor view in surprising ways.

The usual mixfix syntax annotations are available for both types and
constructors. For example:
\<close>

(*<*)
    end
(*>*)
    datatype ('a, 'b) prod (infixr "*" 20) = Pair 'a 'b

text \<open>\blankline\<close>

    datatype (set: 'a) list =
      null: Nil ("[]")
    | Cons (hd: 'a) (tl: "'a list") (infixr "#" 65)
    for
      map: map
      rel: list_all2
      pred: list_all

text \<open>
\noindent
Incidentally, this is how the traditional syntax can be set up:
\<close>

    syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]")

text \<open>\blankline\<close>

    translations
      "[x, xs]" == "x # [xs]"
      "[x]" == "x # []"


subsection \<open>Command Syntax
  \label{ssec:datatype-command-syntax}\<close>

subsubsection \<open>\keyw{datatype}
  \label{sssec:datatype}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "datatype"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command datatype} target? @{syntax dt_options}? @{syntax dt_spec}
  ;
  @{syntax_def dt_options}: '(' ((@{syntax plugins} | 'discs_sels') + ',') ')'
  ;
  @{syntax_def plugins}: 'plugins' ('only' | 'del') ':' (name +)
  ;
  @{syntax_def dt_spec}: (@{syntax dt_name} '=' (@{syntax dt_ctor} + '|') \<newline>
     @{syntax map_rel_pred}? (@'where' (prop + '|'))? + @'and')
  ;
  @{syntax_def map_rel_pred}: @'for' ((('map' | 'rel' | 'pred') ':' name) +)
\<close>}

\medskip

\noindent
The @{command datatype} command introduces a set of mutually recursive
datatypes specified by their constructors.

The syntactic entity \synt{target} can be used to specify a local
context (e.g., @{text "(in linorder)"} @{cite "isabelle-isar-ref"}),
and \synt{prop} denotes a HOL proposition.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text plugins} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). By default, all plugins are enabled.

\item
The @{text "discs_sels"} option indicates that discriminators and selectors
should be generated. The option is implicitly enabled if names are specified for
discriminators or selectors.
\end{itemize}

The optional \keyw{where} clause specifies default values for selectors.
Each proposition must be an equation of the form
@{text "un_D (C \<dots>) = \<dots>"}, where @{text C} is a constructor and
@{text un_D} is a selector.

The left-hand sides of the datatype equations specify the name of the type to
define, its type parameters, and additional information:

@{rail \<open>
  @{syntax_def dt_name}: @{syntax tyargs}? name mixfix?
  ;
  @{syntax_def tyargs}: typefree | '(' (('dead' | name ':')? typefree + ',') ')'
\<close>}

\medskip

\noindent
The syntactic entity \synt{name} denotes an identifier, \synt{mixfix} denotes
the usual parenthesized mixfix notation, and \synt{typefree} denotes fixed type
variable (@{typ 'a}, @{typ 'b}, \ldots) @{cite "isabelle-isar-ref"}.

The optional names preceding the type variables allow to override the default
names of the set functions (@{text set\<^sub>1_t}, \ldots, @{text set\<^sub>m_t}). Type
arguments can be marked as dead by entering @{text dead} in front of the
type variable (e.g., @{text "(dead 'a)"}); otherwise, they are live or dead
(and a set function is generated or not) depending on where they occur in the
right-hand sides of the definition. Declaring a type argument as dead can speed
up the type definition but will prevent any later (co)recursion through that
type argument.

Inside a mutually recursive specification, all defined datatypes must
mention exactly the same type variables in the same order.

@{rail \<open>
  @{syntax_def dt_ctor}: (name ':')? name (@{syntax dt_ctor_arg} * ) mixfix?
\<close>}

\medskip

\noindent
The main constituents of a constructor specification are the name of the
constructor and the list of its argument types. An optional discriminator name
can be supplied at the front. If discriminators are enabled (cf.\ the
@{text "discs_sels"} option) but no name is supplied, the default is
@{text "\<lambda>x. x = C\<^sub>j"} for nullary constructors and
@{text t.is_C\<^sub>j} otherwise.

@{rail \<open>
  @{syntax_def dt_ctor_arg}: type | '(' name ':' type ')'
\<close>}

\medskip

\noindent
The syntactic entity \synt{type} denotes a HOL type @{cite "isabelle-isar-ref"}.

In addition to the type of a constructor argument, it is possible to specify a
name for the corresponding selector. The same selector name can be reused for
arguments to several constructors as long as the arguments share the same type.
If selectors are enabled (cf.\ the @{text "discs_sels"} option) but no name is
supplied, the default name is @{text un_C\<^sub>ji}.
\<close>


subsubsection \<open>\keyw{datatype_compat}
  \label{sssec:datatype-compat}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "datatype_compat"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command datatype_compat} (name +)
\<close>}

\medskip

\noindent
The @{command datatype_compat} command registers new-style datatypes as
old-style datatypes and invokes the old-style plugins. For example:
\<close>

    datatype_compat even_nat odd_nat

text \<open>\blankline\<close>

    ML \<open>Old_Datatype_Data.get_info @{theory} @{type_name even_nat}\<close>

text \<open>
The syntactic entity \synt{name} denotes an identifier @{cite "isabelle-isar-ref"}.

The command is sometimes useful when migrating from the old datatype package to
the new one.

A few remarks concern nested recursive datatypes:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The old-style, nested-as-mutual induction rule and recursor theorems are
generated under their usual names but with ``@{text "compat_"}'' prefixed
(e.g., @{text compat_tree.induct}, @{text compat_tree.inducts}, and
@{text compat_tree.rec}). These theorems should be identical to the ones
generated by the old datatype package, \emph{up to the order of the
premises}---meaning that the subgoals generated by the @{text induct} or
@{text induction} method may be in a different order than before.

\item All types through which recursion takes place must be new-style datatypes
or the function type.
\end{itemize}
\<close>


subsection \<open>Generated Constants
  \label{ssec:datatype-generated-constants}\<close>

text \<open>
Given a datatype @{text "('a\<^sub>1, \<dots>, 'a\<^sub>m) t"} with $m$ live type variables
and $n$ constructors @{text "t.C\<^sub>1"}, \ldots, @{text "t.C\<^sub>n"}, the following
auxiliary constants are introduced:

\medskip

\begin{tabular}{@ {}ll@ {}}
Case combinator: &
  @{text t.case_t} (rendered using the familiar @{text case}--@{text of} syntax) \\
Discriminators: &
  @{text t.is_C\<^sub>1}$, \ldots, $@{text t.is_C\<^sub>n} \\
Selectors: &
  @{text t.un_C\<^sub>11}$, \ldots, $@{text t.un_C\<^sub>1k\<^sub>1} \\
& \quad\vdots \\
& @{text t.un_C\<^sub>n1}$, \ldots, $@{text t.un_C\<^sub>nk\<^sub>n} \\
Set functions: &
  @{text t.set\<^sub>1_t}, \ldots, @{text t.set\<^sub>m_t} \\
Map function: &
  @{text t.map_t} \\
Relator: &
  @{text t.rel_t} \\
Recursor: &
  @{text t.rec_t}
\end{tabular}

\medskip

\noindent
The discriminators and selectors are generated only if the @{text "discs_sels"}
option is enabled or if names are specified for discriminators or selectors.
The set functions, map function, predicator, and relator are generated only if $m > 0$.

In addition, some of the plugins introduce their own constants
(Section~\ref{sec:selecting-plugins}). The case combinator, discriminators,
and selectors are collectively called \emph{destructors}. The prefix
``@{text "t."}'' is an optional component of the names and is normally hidden.
\<close>


subsection \<open>Generated Theorems
  \label{ssec:datatype-generated-theorems}\<close>

text \<open>
The characteristic theorems generated by @{command datatype} are grouped in
three broad categories:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The \emph{free constructor theorems}
(Section~\ref{sssec:free-constructor-theorems}) are properties of the
constructors and destructors that can be derived for any freely generated type.
Internally, the derivation is performed by @{command free_constructors}.

\item The \emph{functorial theorems} (Section~\ref{sssec:functorial-theorems})
are properties of datatypes related to their BNF nature.

\item The \emph{inductive theorems} (Section~\ref{sssec:inductive-theorems})
are properties of datatypes related to their inductive nature.

\end{itemize}

\noindent
The full list of named theorems can be obtained by issuing the command
\keyw{print_theorems} immediately after the datatype definition. This list
includes theorems produced by plugins (Section~\ref{sec:selecting-plugins}),
but normally excludes low-level theorems that reveal internal constructions.
To make these accessible, add the line
\<close>

    declare [[bnf_internals]]
(*<*)
    declare [[bnf_internals = false]]
(*>*)


subsubsection \<open>Free Constructor Theorems
  \label{sssec:free-constructor-theorems}\<close>

(*<*)
    consts nonnull :: 'a
(*>*)

text \<open>
The free constructor theorems are partitioned in three subgroups. The first
subgroup of properties is concerned with the constructors. They are listed below
for @{typ "'a list"}:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{inject} @{text "[iff, induct_simp]"}\rm:] ~ \\
@{thm list.inject[no_vars]}

\item[@{text "t."}\hthm{distinct} @{text "[simp, induct_simp]"}\rm:] ~ \\
@{thm list.distinct(1)[no_vars]} \\
@{thm list.distinct(2)[no_vars]}

\item[@{text "t."}\hthm{exhaust} @{text "[cases t, case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
@{thm list.exhaust[no_vars]}

\item[@{text "t."}\hthm{nchotomy}\rm:] ~ \\
@{thm list.nchotomy[no_vars]}

\end{description}
\end{indentblock}

\noindent
In addition, these nameless theorems are registered as safe elimination rules:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{distinct {\upshape[}THEN notE}@{text ", elim!"}\hthm{\upshape]}\rm:] ~ \\
@{thm list.distinct(1)[THEN notE, elim!, no_vars]} \\
@{thm list.distinct(2)[THEN notE, elim!, no_vars]}

\end{description}
\end{indentblock}

\noindent
The next subgroup is concerned with the case combinator:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{case} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.case(1)[no_vars]} \\
@{thm list.case(2)[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "t."}\hthm{case_cong} @{text "[fundef_cong]"}\rm:] ~ \\
@{thm list.case_cong[no_vars]}

\item[@{text "t."}\hthm{case_cong_weak} @{text "[cong]"}\rm:] ~ \\
@{thm list.case_cong_weak[no_vars]}

\item[@{text "t."}\hthm{case_distrib}\rm:] ~ \\
@{thm list.case_distrib[no_vars]}

\item[@{text "t."}\hthm{split}\rm:] ~ \\
@{thm list.split[no_vars]}

\item[@{text "t."}\hthm{split_asm}\rm:] ~ \\
@{thm list.split_asm[no_vars]}

\item[@{text "t."}\hthm{splits} = @{text "split split_asm"}]

\end{description}
\end{indentblock}

\noindent
The third subgroup revolves around discriminators and selectors:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{disc} @{text "[simp]"}\rm:] ~ \\
@{thm list.disc(1)[no_vars]} \\
@{thm list.disc(2)[no_vars]}

\item[@{text "t."}\hthm{discI}\rm:] ~ \\
@{thm list.discI(1)[no_vars]} \\
@{thm list.discI(2)[no_vars]}

\item[@{text "t."}\hthm{sel} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.sel(1)[no_vars]} \\
@{thm list.sel(2)[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "t."}\hthm{collapse} @{text "[simp]"}\rm:] ~ \\
@{thm list.collapse(1)[no_vars]} \\
@{thm list.collapse(2)[no_vars]} \\
The @{text "[simp]"} attribute is exceptionally omitted for datatypes equipped
with a single nullary constructor, because a property of the form
@{prop "x = C"} is not suitable as a simplification rule.

\item[@{text "t."}\hthm{distinct_disc} @{text "[dest]"}\rm:] ~ \\
These properties are missing for @{typ "'a list"} because there is only one
proper discriminator. If the datatype had been introduced with a second
discriminator called @{const nonnull}, they would have read as follows: \\[\jot]
@{prop "null list \<Longrightarrow> \<not> nonnull list"} \\
@{prop "nonnull list \<Longrightarrow> \<not> null list"}

\item[@{text "t."}\hthm{exhaust_disc} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
@{thm list.exhaust_disc[no_vars]}

\item[@{text "t."}\hthm{exhaust_sel} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
@{thm list.exhaust_sel[no_vars]}

\item[@{text "t."}\hthm{expand}\rm:] ~ \\
@{thm list.expand[no_vars]}

\item[@{text "t."}\hthm{split_sel}\rm:] ~ \\
@{thm list.split_sel[no_vars]}

\item[@{text "t."}\hthm{split_sel_asm}\rm:] ~ \\
@{thm list.split_sel_asm[no_vars]}

\item[@{text "t."}\hthm{split_sels} = @{text "split_sel split_sel_asm"}]

\item[@{text "t."}\hthm{case_eq_if}\rm:] ~ \\
@{thm list.case_eq_if[no_vars]}

\item[@{text "t."}\hthm{disc_eq_case}\rm:] ~ \\
@{thm list.disc_eq_case(1)[no_vars]} \\
@{thm list.disc_eq_case(2)[no_vars]}

\end{description}
\end{indentblock}

\noindent
In addition, equational versions of @{text t.disc} are registered with the
@{text "[code]"} attribute. The @{text "[code]"} attribute is set by the
@{text code} plugin (Section~\ref{ssec:code-generator}).
\<close>


subsubsection \<open>Functorial Theorems
  \label{sssec:functorial-theorems}\<close>

text \<open>
The functorial theorems are generated for type constructors with at least
one live type argument (e.g., @{typ "'a list"}). They are partitioned in two
subgroups. The first subgroup consists of properties involving the
constructors or the destructors and either a set function, the map function,
the predicator, or the relator:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{case_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.case_transfer[no_vars]} \\
This property is generated by the @{text transfer} plugin
(Section~\ref{ssec:transfer}).
%The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
%(Section~\ref{ssec:transfer}).

\item[@{text "t."}\hthm{sel_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
This property is missing for @{typ "'a list"} because there is no common
selector to all constructors. \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}).

\item[@{text "t."}\hthm{ctr_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.ctr_transfer(1)[no_vars]} \\
@{thm list.ctr_transfer(2)[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) .

\item[@{text "t."}\hthm{disc_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.disc_transfer(1)[no_vars]} \\
@{thm list.disc_transfer(2)[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}).

\item[@{text "t."}\hthm{set} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.set(1)[no_vars]} \\
@{thm list.set(2)[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "t."}\hthm{set_cases} @{text "[consumes 1, cases set: set\<^sub>i_t]"}\rm:] ~ \\
@{thm list.set_cases[no_vars]}

\item[@{text "t."}\hthm{set_intros}\rm:] ~ \\
@{thm list.set_intros(1)[no_vars]} \\
@{thm list.set_intros(2)[no_vars]}

\item[@{text "t."}\hthm{set_sel}\rm:] ~ \\
@{thm list.set_sel[no_vars]}

\item[@{text "t."}\hthm{map} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.map(1)[no_vars]} \\
@{thm list.map(2)[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "t."}\hthm{map_disc_iff} @{text "[simp]"}\rm:] ~ \\
@{thm list.map_disc_iff[no_vars]}

\item[@{text "t."}\hthm{map_sel}\rm:] ~ \\
@{thm list.map_sel[no_vars]}

\item[@{text "t."}\hthm{pred_inject} @{text "[simp]"}\rm:] ~ \\
@{thm list.pred_inject(1)[no_vars]} \\
@{thm list.pred_inject(2)[no_vars]}

\item[@{text "t."}\hthm{rel_inject} @{text "[simp]"}\rm:] ~ \\
@{thm list.rel_inject(1)[no_vars]} \\
@{thm list.rel_inject(2)[no_vars]}

\item[@{text "t."}\hthm{rel_distinct} @{text "[simp]"}\rm:] ~ \\
@{thm list.rel_distinct(1)[no_vars]} \\
@{thm list.rel_distinct(2)[no_vars]}

\item[@{text "t."}\hthm{rel_intros}\rm:] ~ \\
@{thm list.rel_intros(1)[no_vars]} \\
@{thm list.rel_intros(2)[no_vars]}

\item[@{text "t."}\hthm{rel_cases} @{text "[consumes 1, case_names t\<^sub>1 \<dots> t\<^sub>m, cases pred]"}\rm:] ~ \\
@{thm list.rel_cases[no_vars]}

\item[@{text "t."}\hthm{rel_sel}\rm:] ~ \\
@{thm list.rel_sel[no_vars]}

\end{description}
\end{indentblock}

\noindent
In addition, equational versions of @{text t.rel_inject} and @{text
rel_distinct} are registered with the @{text "[code]"} attribute. The
@{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

The second subgroup consists of more abstract properties of the set functions,
the map function, the predicator, and the relator:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{inj_map}\rm:] ~ \\
@{thm list.inj_map[no_vars]}

\item[@{text "t."}\hthm{inj_map_strong}\rm:] ~ \\
@{thm list.inj_map_strong[no_vars]}

\item[@{text "t."}\hthm{map_comp}\rm:] ~ \\
@{thm list.map_comp[no_vars]}

\item[@{text "t."}\hthm{map_cong0}\rm:] ~ \\
@{thm list.map_cong0[no_vars]}

\item[@{text "t."}\hthm{map_cong} @{text "[fundef_cong]"}\rm:] ~ \\
@{thm list.map_cong[no_vars]}

\item[@{text "t."}\hthm{map_cong_pred}\rm:] ~ \\
@{thm list.map_cong_pred[no_vars]}

\item[@{text "t."}\hthm{map_cong_simp}\rm:] ~ \\
@{thm list.map_cong_simp[no_vars]}

\item[@{text "t."}\hthm{map_id0}\rm:] ~ \\
@{thm list.map_id0[no_vars]}

\item[@{text "t."}\hthm{map_id}\rm:] ~ \\
@{thm list.map_id[no_vars]}

\item[@{text "t."}\hthm{map_ident}\rm:] ~ \\
@{thm list.map_ident[no_vars]}

\item[@{text "t."}\hthm{map_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.map_transfer[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\item[@{text "t."}\hthm{pred_cong} @{text "[fundef_cong]"}\rm:] ~ \\
@{thm list.pred_cong[no_vars]}

\item[@{text "t."}\hthm{pred_cong_simp}\rm:] ~ \\
@{thm list.pred_cong_simp[no_vars]}

\item[@{text "t."}\hthm{pred_map}\rm:] ~ \\
@{thm list.pred_map[no_vars]}

\item[@{text "t."}\hthm{pred_mono_strong}\rm:] ~ \\
@{thm list.pred_mono_strong[no_vars]}

\item[@{text "t."}\hthm{pred_rel}\rm:] ~ \\
@{thm list.pred_rel[no_vars]}

\item[@{text "t."}\hthm{pred_set}\rm:] ~ \\
@{thm list.pred_set[no_vars]}

\item[@{text "t."}\hthm{pred_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.pred_transfer[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\item[@{text "t."}\hthm{pred_True}\rm:] ~ \\
@{thm list.pred_True[no_vars]}

\item[@{text "t."}\hthm{set_map}\rm:] ~ \\
@{thm list.set_map[no_vars]}

\item[@{text "t."}\hthm{set_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.set_transfer[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\item[@{text "t."}\hthm{rel_compp} @{text "[relator_distr]"}\rm:] ~ \\
@{thm list.rel_compp[no_vars]} \\
The @{text "[relator_distr]"} attribute is set by the @{text lifting} plugin
(Section~\ref{ssec:lifting}).

\item[@{text "t."}\hthm{rel_conversep}\rm:] ~ \\
@{thm list.rel_conversep[no_vars]}

\item[@{text "t."}\hthm{rel_eq}\rm:] ~ \\
@{thm list.rel_eq[no_vars]}

\item[@{text "t."}\hthm{rel_eq_onp}\rm:] ~ \\
@{thm list.rel_eq_onp[no_vars]}

\item[@{text "t."}\hthm{rel_flip}\rm:] ~ \\
@{thm list.rel_flip[no_vars]}

\item[@{text "t."}\hthm{rel_map}\rm:] ~ \\
@{thm list.rel_map(1)[no_vars]} \\
@{thm list.rel_map(2)[no_vars]}

\item[@{text "t."}\hthm{rel_mono} @{text "[mono, relator_mono]"}\rm:] ~ \\
@{thm list.rel_mono[no_vars]} \\
The @{text "[relator_mono]"} attribute is set by the @{text lifting} plugin
(Section~\ref{ssec:lifting}).

\item[@{text "t."}\hthm{rel_mono_strong}\rm:] ~ \\
@{thm list.rel_mono_strong[no_vars]}

\item[@{text "t."}\hthm{rel_cong} @{text "[fundef_cong]"}\rm:] ~ \\
@{thm list.rel_cong[no_vars]}

\item[@{text "t."}\hthm{rel_cong_simp}\rm:] ~ \\
@{thm list.rel_cong_simp[no_vars]}

\item[@{text "t."}\hthm{rel_refl}\rm:] ~ \\
@{thm list.rel_refl[no_vars]}

\item[@{text "t."}\hthm{rel_refl_strong}\rm:] ~ \\
@{thm list.rel_refl_strong[no_vars]}

\item[@{text "t."}\hthm{rel_reflp}\rm:] ~ \\
@{thm list.rel_reflp[no_vars]}

\item[@{text "t."}\hthm{rel_symp}\rm:] ~ \\
@{thm list.rel_symp[no_vars]}

\item[@{text "t."}\hthm{rel_transp}\rm:] ~ \\
@{thm list.rel_transp[no_vars]}

\item[@{text "t."}\hthm{rel_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.rel_transfer[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\end{description}
\end{indentblock}
\<close>


subsubsection \<open>Inductive Theorems
  \label{sssec:inductive-theorems}\<close>

text \<open>
The inductive theorems are as follows:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n, induct t]"}\rm:] ~ \\
@{thm list.induct[no_vars]}

\item[@{text "t."}\hthm{rel_induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n, induct pred]"}\rm:] ~ \\
@{thm list.rel_induct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm: \\
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{rel_induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm: \\
\end{tabular}] ~ \\
Given $m > 1$ mutually recursive datatypes, this induction rule can be used to
prove $m$ properties simultaneously.

\item[@{text "t."}\hthm{rec} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.rec(1)[no_vars]} \\
@{thm list.rec(2)[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "t."}\hthm{rec_o_map}\rm:] ~ \\
@{thm list.rec_o_map[no_vars]}

\item[@{text "t."}\hthm{rec_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.rec_transfer[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\end{description}
\end{indentblock}

\noindent
For convenience, @{command datatype} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{simps}] = @{text t.inject} @{text t.distinct} @{text t.case} @{text t.rec} @{text t.map} @{text t.rel_inject} \\
@{text t.rel_distinct} @{text t.set}

\end{description}
\end{indentblock}
\<close>


subsection \<open>Proof Method
  \label{ssec:datatype-proof-method}\<close>

subsubsection \<open>\textit{countable_datatype}
  \label{sssec:datatype-compat}\<close>

text \<open>
The theory \<^file>\<open>~~/src/HOL/Library/Countable.thy\<close> provides a
proof method called @{method countable_datatype} that can be used to prove the
countability of many datatypes, building on the countability of the types
appearing in their definitions and of any type arguments. For example:
\<close>

    instance list :: (countable) countable
      by countable_datatype


subsection \<open>Compatibility Issues
  \label{ssec:datatype-compatibility-issues}\<close>

text \<open>
The command @{command datatype} has been designed to be highly compatible with
the old command, to ease migration. There are nonetheless a few
incompatibilities that may arise when porting:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{The Standard ML interfaces are different.} Tools and extensions
written to call the old ML interfaces will need to be adapted to the new
interfaces. The @{text BNF_LFP_Compat} structure provides convenience functions
that simulate the old interfaces in terms of the new ones.

\item \emph{The recursor @{text rec_t} has a different signature for nested
recursive datatypes.} In the old package, nested recursion through non-functions
was internally reduced to mutual recursion. This reduction was visible in the
type of the recursor, used by \keyw{primrec}. Recursion through functions was
handled specially. In the new package, nested recursion (for functions and
non-functions) is handled in a more modular fashion. The old-style recursor can
be generated on demand using @{command primrec} if the recursion is via
new-style datatypes, as explained in
Section~\ref{sssec:primrec-nested-as-mutual-recursion}, or using
@{command datatype_compat}.

\item \emph{Accordingly, the induction rule is different for nested recursive
datatypes.} Again, the old-style induction rule can be generated on demand
using @{command primrec} if the recursion is via new-style datatypes, as
explained in Section~\ref{sssec:primrec-nested-as-mutual-recursion}, or using
@{command datatype_compat}. For recursion through functions, the old-style
induction rule can be obtained by applying the @{text "[unfolded
all_mem_range]"} attribute on @{text t.induct}.

\item \emph{The @{const size} function has a slightly different definition.}
The new function returns @{text 1} instead of @{text 0} for some nonrecursive
constructors. This departure from the old behavior made it possible to implement
@{const size} in terms of the generic function @{text "t.size_t"}. Moreover,
the new function considers nested occurrences of a value, in the nested
recursive case. The old behavior can be obtained by disabling the @{text size}
plugin (Section~\ref{sec:selecting-plugins}) and instantiating the
@{text size} type class manually.

\item \emph{The internal constructions are completely different.} Proof texts
that unfold the definition of constants introduced by the old command will
be difficult to port.

\item \emph{Some constants and theorems have different names.}
For non-mutually recursive datatypes,
the alias @{text t.inducts} for @{text t.induct} is no longer generated.
For $m > 1$ mutually recursive datatypes,
@{text "rec_t\<^sub>1_\<dots>_t\<^sub>m_i"} has been renamed
@{text "rec_t\<^sub>i"} for each @{text "i \<in> {1, \<dots>, m}"},
@{text "t\<^sub>1_\<dots>_t\<^sub>m.inducts(i)"} has been renamed
@{text "t\<^sub>i.induct"} for each @{text "i \<in> {1, \<dots>, m}"}, and the
collection @{text "t\<^sub>1_\<dots>_t\<^sub>m.size"} (generated by the
@{text size} plugin, Section~\ref{ssec:size}) has been divided into
@{text "t\<^sub>1.size"}, \ldots, @{text "t\<^sub>m.size"}.

\item \emph{The @{text t.simps} collection has been extended.}
Previously available theorems are available at the same index as before.

\item \emph{Variables in generated properties have different names.} This is
rarely an issue, except in proof texts that refer to variable names in the
@{text "[where \<dots>]"} attribute. The solution is to use the more robust
@{text "[of \<dots>]"} syntax.
\end{itemize}

%FIXME old_datatype no longer exists
The old command is still available as \keyw{old_datatype} in theory
\<^file>\<open>~~/src/HOL/Library/Old_Datatype.thy\<close>. However, there is no general
way to register old-style datatypes as new-style datatypes. If the objective
is to define new-style datatypes with nested recursion through old-style
datatypes, the old-style datatypes can be registered as a BNF
(Section~\ref{sec:registering-bounded-natural-functors}). If the objective is
to derive discriminators and selectors, this can be achieved using
@{command free_constructors}
(Section~\ref{sec:deriving-destructors-and-theorems-for-free-constructors}).
\<close>


section \<open>Defining Primitively Recursive Functions
  \label{sec:defining-primitively-recursive-functions}\<close>

text \<open>
Recursive functions over datatypes can be specified using the @{command primrec}
command, which supports primitive recursion, or using the more general
\keyw{fun}, \keyw{function}, and \keyw{partial_function} commands. In this
tutorial, the focus is on @{command primrec}; \keyw{fun} and \keyw{function} are
described in a separate tutorial @{cite "isabelle-function"}.
\<close>


subsection \<open>Introductory Examples
  \label{ssec:primrec-introductory-examples}\<close>

text \<open>
Primitive recursion is illustrated through concrete examples based on the
datatypes defined in Section~\ref{ssec:datatype-introductory-examples}. More
examples can be found in the directory \<^dir>\<open>~~/src/HOL/Datatype_Examples\<close>.
\<close>


subsubsection \<open>Nonrecursive Types
  \label{sssec:primrec-nonrecursive-types}\<close>

text \<open>
Primitive recursion removes one layer of constructors on the left-hand side in
each equation. For example:
\<close>

    primrec (nonexhaustive) bool_of_trool :: "trool \<Rightarrow> bool" where
      "bool_of_trool Faalse \<longleftrightarrow> False"
    | "bool_of_trool Truue \<longleftrightarrow> True"

text \<open>\blankline\<close>

    primrec the_list :: "'a option \<Rightarrow> 'a list" where
      "the_list None = []"
    | "the_list (Some a) = [a]"

text \<open>\blankline\<close>

    primrec the_default :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
      "the_default d None = d"
    | "the_default _ (Some a) = a"

text \<open>\blankline\<close>

    primrec mirrror :: "('a, 'b, 'c) triple \<Rightarrow> ('c, 'b, 'a) triple" where
      "mirrror (Triple a b c) = Triple c b a"

text \<open>
\noindent
The equations can be specified in any order, and it is acceptable to leave out
some cases, which are then unspecified. Pattern matching on the left-hand side
is restricted to a single datatype, which must correspond to the same argument
in all equations.
\<close>


subsubsection \<open>Simple Recursion
  \label{sssec:primrec-simple-recursion}\<close>

text \<open>
For simple recursive types, recursive calls on a constructor argument are
allowed on the right-hand side:
\<close>

    primrec replicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
      "replicate Zero _ = []"
    | "replicate (Succ n) x = x # replicate n x"

text \<open>\blankline\<close>

    primrec (nonexhaustive) at :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
      "at (x # xs) j =
         (case j of
            Zero \<Rightarrow> x
          | Succ j' \<Rightarrow> at xs j')"

text \<open>\blankline\<close>

    primrec (*<*)(in early) (transfer) (*>*)tfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) tlist \<Rightarrow> 'b" where
      "tfold _ (TNil y) = y"
    | "tfold f (TCons x xs) = f x (tfold f xs)"

text \<open>
\noindent
Pattern matching is only available for the argument on which the recursion takes
place. Fortunately, it is easy to generate pattern-maching equations using the
@{command simps_of_case} command provided by the theory
\<^file>\<open>~~/src/HOL/Library/Simps_Case_Conv.thy\<close>.
\<close>

    simps_of_case at_simps_alt: at.simps

text \<open>
This generates the lemma collection @{thm [source] at_simps_alt}:
%
\[@{thm at_simps_alt(1)[no_vars]}
  \qquad @{thm at_simps_alt(2)[no_vars]}\]
%
The next example is defined using \keyw{fun} to escape the syntactic
restrictions imposed on primitively recursive functions:
\<close>

    fun at_least_two :: "nat \<Rightarrow> bool" where
      "at_least_two (Succ (Succ _)) \<longleftrightarrow> True"
    | "at_least_two _ \<longleftrightarrow> False"


subsubsection \<open>Mutual Recursion
  \label{sssec:primrec-mutual-recursion}\<close>

text \<open>
The syntax for mutually recursive functions over mutually recursive datatypes
is straightforward:
\<close>

    primrec
      nat_of_even_nat :: "even_nat \<Rightarrow> nat" and
      nat_of_odd_nat :: "odd_nat \<Rightarrow> nat"
    where
      "nat_of_even_nat Even_Zero = Zero"
    | "nat_of_even_nat (Even_Succ n) = Succ (nat_of_odd_nat n)"
    | "nat_of_odd_nat (Odd_Succ n) = Succ (nat_of_even_nat n)"

text \<open>\blankline\<close>

    primrec
      eval\<^sub>e :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) exp \<Rightarrow> int" and
      eval\<^sub>t :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) trm \<Rightarrow> int" and
      eval\<^sub>f :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) fct \<Rightarrow> int"
    where
      "eval\<^sub>e \<gamma> \<xi> (Term t) = eval\<^sub>t \<gamma> \<xi> t"
    | "eval\<^sub>e \<gamma> \<xi> (Sum t e) = eval\<^sub>t \<gamma> \<xi> t + eval\<^sub>e \<gamma> \<xi> e"
    | "eval\<^sub>t \<gamma> \<xi> (Factor f) = eval\<^sub>f \<gamma> \<xi> f"
    | "eval\<^sub>t \<gamma> \<xi> (Prod f t) = eval\<^sub>f \<gamma> \<xi> f + eval\<^sub>t \<gamma> \<xi> t"
    | "eval\<^sub>f \<gamma> _ (Const a) = \<gamma> a"
    | "eval\<^sub>f _ \<xi> (Var b) = \<xi> b"
    | "eval\<^sub>f \<gamma> \<xi> (Expr e) = eval\<^sub>e \<gamma> \<xi> e"

text \<open>
\noindent
Mutual recursion is possible within a single type, using \keyw{fun}:
\<close>

    fun
      even :: "nat \<Rightarrow> bool" and
      odd :: "nat \<Rightarrow> bool"
    where
      "even Zero = True"
    | "even (Succ n) = odd n"
    | "odd Zero = False"
    | "odd (Succ n) = even n"


subsubsection \<open>Nested Recursion
  \label{sssec:primrec-nested-recursion}\<close>

text \<open>
In a departure from the old datatype package, nested recursion is normally
handled via the map functions of the nesting type constructors. For example,
recursive calls are lifted to lists using @{const map}:
\<close>

(*<*)
    datatype 'a tree\<^sub>f\<^sub>f = Node\<^sub>f\<^sub>f (lbl\<^sub>f\<^sub>f: 'a) (sub\<^sub>f\<^sub>f: "'a tree\<^sub>f\<^sub>f list")
(*>*)
    primrec at\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f \<Rightarrow> nat list \<Rightarrow> 'a" where
      "at\<^sub>f\<^sub>f (Node\<^sub>f\<^sub>f a ts) js =
         (case js of
            [] \<Rightarrow> a
          | j # js' \<Rightarrow> at (map (\<lambda>t. at\<^sub>f\<^sub>f t js') ts) j)"

text \<open>
\noindent
The next example features recursion through the @{text option} type. Although
@{text option} is not a new-style datatype, it is registered as a BNF with the
map function @{const map_option}:
\<close>

    primrec (*<*)(in early) (*>*)sum_btree :: "('a::{zero,plus}) btree \<Rightarrow> 'a" where
      "sum_btree (BNode a lt rt) =
         a + the_default 0 (map_option sum_btree lt) +
           the_default 0 (map_option sum_btree rt)"

text \<open>
\noindent
The same principle applies for arbitrary type constructors through which
recursion is possible. Notably, the map function for the function type
(@{text \<Rightarrow>}) is simply composition (@{text "op \<circ>"}):
\<close>

    primrec (*<*)(in early) (*>*)relabel_ft :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
      "relabel_ft f (FTLeaf x) = FTLeaf (f x)"
    | "relabel_ft f (FTNode g) = FTNode (relabel_ft f \<circ> g)"

text \<open>
\noindent
For convenience, recursion through functions can also be expressed using
$\lambda$-abstractions and function application rather than through composition.
For example:
\<close>

    primrec relabel_ft :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
      "relabel_ft f (FTLeaf x) = FTLeaf (f x)"
    | "relabel_ft f (FTNode g) = FTNode (\<lambda>x. relabel_ft f (g x))"

text \<open>\blankline\<close>

    primrec (nonexhaustive) subtree_ft :: "'a \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
      "subtree_ft x (FTNode g) = g x"

text \<open>
\noindent
For recursion through curried $n$-ary functions, $n$ applications of
@{term "op \<circ>"} are necessary. The examples below illustrate the case where
$n = 2$:
\<close>

    datatype 'a ftree2 = FTLeaf2 'a | FTNode2 "'a \<Rightarrow> 'a \<Rightarrow> 'a ftree2"

text \<open>\blankline\<close>

    primrec (*<*)(in early) (*>*)relabel_ft2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree2 \<Rightarrow> 'a ftree2" where
      "relabel_ft2 f (FTLeaf2 x) = FTLeaf2 (f x)"
    | "relabel_ft2 f (FTNode2 g) = FTNode2 (op \<circ> (op \<circ> (relabel_ft2 f)) g)"

text \<open>\blankline\<close>

    primrec relabel_ft2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree2 \<Rightarrow> 'a ftree2" where
      "relabel_ft2 f (FTLeaf2 x) = FTLeaf2 (f x)"
    | "relabel_ft2 f (FTNode2 g) = FTNode2 (\<lambda>x y. relabel_ft2 f (g x y))"

text \<open>\blankline\<close>

    primrec (nonexhaustive) subtree_ft2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a ftree2 \<Rightarrow> 'a ftree2" where
      "subtree_ft2 x y (FTNode2 g) = g x y"

text \<open>
For any datatype featuring nesting, the predicator can be used instead of the
map function, typically when defining predicates. For example:
\<close>

    primrec increasing_tree :: "int \<Rightarrow> int tree\<^sub>f\<^sub>f \<Rightarrow> bool" where
      "increasing_tree m (Node\<^sub>f\<^sub>f n ts) \<longleftrightarrow>
       n \<ge> m \<and> list_all (increasing_tree (n + 1)) ts"


subsubsection \<open>Nested-as-Mutual Recursion
  \label{sssec:primrec-nested-as-mutual-recursion}\<close>

(*<*)
    locale n2m
    begin
(*>*)

text \<open>
For compatibility with the old package, but also because it is sometimes
convenient in its own right, it is possible to treat nested recursive datatypes
as mutually recursive ones if the recursion takes place though new-style
datatypes. For example:
\<close>

    primrec (nonexhaustive)
      at\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f \<Rightarrow> nat list \<Rightarrow> 'a" and
      ats\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a"
    where
      "at\<^sub>f\<^sub>f (Node\<^sub>f\<^sub>f a ts) js =
         (case js of
            [] \<Rightarrow> a
          | j # js' \<Rightarrow> ats\<^sub>f\<^sub>f ts j js')"
    | "ats\<^sub>f\<^sub>f (t # ts) j =
         (case j of
            Zero \<Rightarrow> at\<^sub>f\<^sub>f t
          | Succ j' \<Rightarrow> ats\<^sub>f\<^sub>f ts j')"

text \<open>
\noindent
Appropriate induction rules are generated as
@{thm [source] at\<^sub>f\<^sub>f.induct},
@{thm [source] ats\<^sub>f\<^sub>f.induct}, and
@{thm [source] at\<^sub>f\<^sub>f_ats\<^sub>f\<^sub>f.induct}. The
induction rules and the underlying recursors are generated dynamically
and are kept in a cache to speed up subsequent definitions.

Here is a second example:
\<close>

    primrec
      sum_btree :: "('a::{zero,plus}) btree \<Rightarrow> 'a" and
      sum_btree_option :: "'a btree option \<Rightarrow> 'a"
    where
      "sum_btree (BNode a lt rt) =
         a + sum_btree_option lt + sum_btree_option rt"
    | "sum_btree_option None = 0"
    | "sum_btree_option (Some t) = sum_btree t"

text \<open>
%  * can pretend a nested type is mutually recursive (if purely inductive)
%  * avoids the higher-order map
%  * e.g.

%  * this can always be avoided;
%     * e.g. in our previous example, we first mapped the recursive
%       calls, then we used a generic at function to retrieve the result
%
%  * there's no hard-and-fast rule of when to use one or the other,
%    just like there's no rule when to use fold and when to use
%    primrec
%
%  * higher-order approach, considering nesting as nesting, is more
%    compositional -- e.g. we saw how we could reuse an existing polymorphic
%    at or the_default, whereas @{const ats\<^sub>f\<^sub>f} is much more specific
%
%  * but:
%     * is perhaps less intuitive, because it requires higher-order thinking
%     * may seem inefficient, and indeed with the code generator the
%       mutually recursive version might be nicer
%     * is somewhat indirect -- must apply a map first, then compute a result
%       (cannot mix)
%     * the auxiliary functions like @{const ats\<^sub>f\<^sub>f} are sometimes useful in own right
%
%  * impact on automation unclear
%
\<close>
(*<*)
    end
(*>*)


subsection \<open>Command Syntax
  \label{ssec:primrec-command-syntax}\<close>

subsubsection \<open>\keyw{primrec}
  \label{sssec:primrec}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "primrec"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command primrec} target? @{syntax pr_options}? fixes \<newline>
  @'where' (@{syntax pr_equation} + '|')
  ;
  @{syntax_def pr_options}: '(' ((@{syntax plugins} | 'nonexhaustive' | 'transfer') + ',') ')'
  ;
  @{syntax_def pr_equation}: thmdecl? prop
\<close>}

\medskip

\noindent
The @{command primrec} command introduces a set of mutually recursive functions
over datatypes.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{fixes} denotes a list of names with optional type signatures,
\synt{thmdecl} denotes an optional name for the formula that follows, and
\synt{prop} denotes a HOL proposition @{cite "isabelle-isar-ref"}.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text plugins} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). By default, all plugins are enabled.

\item
The @{text nonexhaustive} option indicates that the functions are not
necessarily specified for all constructors. It can be used to suppress the
warning that is normally emitted when some constructors are missing.

\item
The @{text transfer} option indicates that an unconditional transfer rule
should be generated and proved @{text "by transfer_prover"}. The
@{text "[transfer_rule]"} attribute is set on the generated theorem.
\end{itemize}

%%% TODO: elaborate on format of the equations
%%% TODO: elaborate on mutual and nested-to-mutual
\<close>


subsection \<open>Generated Theorems
  \label{ssec:primrec-generated-theorems}\<close>

(*<*)
    context early
    begin
(*>*)

text \<open>
The @{command primrec} command generates the following properties (listed
for @{const tfold}):

\begin{indentblock}
\begin{description}

\item[@{text "f."}\hthm{simps} @{text "[simp, code]"}\rm:] ~ \\
@{thm tfold.simps(1)[no_vars]} \\
@{thm tfold.simps(2)[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "f."}\hthm{transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm tfold.transfer[no_vars]} \\
This theorem is generated by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) for functions declared with the @{text transfer}
option enabled.

\item[@{text "f."}\hthm{induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
This induction rule is generated for nested-as-mutual recursive functions
(Section~\ref{sssec:primrec-nested-as-mutual-recursion}).

\item[@{text "f\<^sub>1_\<dots>_f\<^sub>m."}\hthm{induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
This induction rule is generated for nested-as-mutual recursive functions
(Section~\ref{sssec:primrec-nested-as-mutual-recursion}). Given $m > 1$ mutually
recursive functions, this rule can be used to prove $m$ properties
simultaneously.

\end{description}
\end{indentblock}
\<close>

(*<*)
    end
(*>*)


subsection \<open>Recursive Default Values for Selectors
  \label{ssec:primrec-recursive-default-values-for-selectors}\<close>

text \<open>
A datatype selector @{text un_D} can have a default value for each constructor
on which it is not otherwise specified. Occasionally, it is useful to have the
default value be defined recursively. This leads to a chicken-and-egg
situation, because the datatype is not introduced yet at the moment when the
selectors are introduced. Of course, we can always define the selectors
manually afterward, but we then have to state and prove all the characteristic
theorems ourselves instead of letting the package do it.

Fortunately, there is a workaround that relies on overloading to relieve us
from the tedium of manual derivations:

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
Introduce a fully unspecified constant @{text "un_D\<^sub>0 :: 'a"} using
@{command consts}.

\item
Define the datatype, specifying @{text "un_D\<^sub>0"} as the selector's default
value.

\item
Define the behavior of @{text "un_D\<^sub>0"} on values of the newly introduced
datatype using the \keyw{overloading} command.

\item
Derive the desired equation on @{text un_D} from the characteristic equations
for @{text "un_D\<^sub>0"}.
\end{enumerate}

\noindent
The following example illustrates this procedure:
\<close>

(*<*)
    hide_const termi
(*>*)
    consts termi\<^sub>0 :: 'a

text \<open>\blankline\<close>

    datatype ('a, 'b) tlist =
      TNil (termi: 'b)
    | TCons (thd: 'a) (ttl: "('a, 'b) tlist")
    where
      "ttl (TNil y) = TNil y"
    | "termi (TCons _ xs) = termi\<^sub>0 xs"

text \<open>\blankline\<close>

    overloading
      termi\<^sub>0 \<equiv> "termi\<^sub>0 :: ('a, 'b) tlist \<Rightarrow> 'b"
    begin
    primrec termi\<^sub>0 :: "('a, 'b) tlist \<Rightarrow> 'b" where
      "termi\<^sub>0 (TNil y) = y"
    | "termi\<^sub>0 (TCons x xs) = termi\<^sub>0 xs"
    end

text \<open>\blankline\<close>

    lemma termi_TCons[simp]: "termi (TCons x xs) = termi xs"
      by (cases xs) auto


subsection \<open>Compatibility Issues
  \label{ssec:primrec-compatibility-issues}\<close>

text \<open>
The command @{command primrec}'s behavior on new-style datatypes has been
designed to be highly compatible with that for old-style datatypes, to ease
migration. There is nonetheless at least one incompatibility that may arise when
porting to the new package:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{Some theorems have different names.}
For $m > 1$ mutually recursive functions,
@{text "f\<^sub>1_\<dots>_f\<^sub>m.simps"} has been broken down into separate
subcollections @{text "f\<^sub>i.simps"}.
\end{itemize}
\<close>


section \<open>Defining Codatatypes
  \label{sec:defining-codatatypes}\<close>

text \<open>
Codatatypes can be specified using the @{command codatatype} command. The
command is first illustrated through concrete examples featuring different
flavors of corecursion. More examples can be found in the directory
\<^dir>\<open>~~/src/HOL/Datatype_Examples\<close>. The \emph{Archive of Formal Proofs} also
includes some useful codatatypes, notably for lazy lists @{cite
"lochbihler-2010"}.
\<close>


subsection \<open>Introductory Examples
  \label{ssec:codatatype-introductory-examples}\<close>

subsubsection \<open>Simple Corecursion
  \label{sssec:codatatype-simple-corecursion}\<close>

text \<open>
Non-corecursive codatatypes coincide with the corresponding datatypes, so they
are rarely used in practice. \emph{Corecursive codatatypes} have the same syntax
as recursive datatypes, except for the command name. For example, here is the
definition of lazy lists:
\<close>

    codatatype (lset: 'a) llist =
      lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a llist")
    for
      map: lmap
      rel: llist_all2
      pred: llist_all
    where
      "ltl LNil = LNil"

text \<open>
\noindent
Lazy lists can be infinite, such as @{text "LCons 0 (LCons 0 (\<dots>))"} and
@{text "LCons 0 (LCons 1 (LCons 2 (\<dots>)))"}. Here is a related type, that of
infinite streams:
\<close>

    codatatype (sset: 'a) stream =
      SCons (shd: 'a) (stl: "'a stream")
    for
      map: smap
      rel: stream_all2

text \<open>
\noindent
Another interesting type that can
be defined as a codatatype is that of the extended natural numbers:
\<close>

    codatatype enat = EZero | ESucc enat

text \<open>
\noindent
This type has exactly one infinite element, @{text "ESucc (ESucc (ESucc (\<dots>)))"},
that represents $\infty$. In addition, it has finite values of the form
@{text "ESucc (\<dots> (ESucc EZero)\<dots>)"}.

Here is an example with many constructors:
\<close>

    codatatype 'a process =
      Fail
    | Skip (cont: "'a process")
    | Action (prefix: 'a) (cont: "'a process")
    | Choice (left: "'a process") (right: "'a process")

text \<open>
\noindent
Notice that the @{const cont} selector is associated with both @{const Skip}
and @{const Action}.
\<close>


subsubsection \<open>Mutual Corecursion
  \label{sssec:codatatype-mutual-corecursion}\<close>

text \<open>
\noindent
The example below introduces a pair of \emph{mutually corecursive} types:
\<close>

    codatatype even_enat = Even_EZero | Even_ESucc odd_enat
    and odd_enat = Odd_ESucc even_enat


subsubsection \<open>Nested Corecursion
  \label{sssec:codatatype-nested-corecursion}\<close>

text \<open>
\noindent
The next examples feature \emph{nested corecursion}:
\<close>

    codatatype 'a tree\<^sub>i\<^sub>i = Node\<^sub>i\<^sub>i (lbl\<^sub>i\<^sub>i: 'a) (sub\<^sub>i\<^sub>i: "'a tree\<^sub>i\<^sub>i llist")

text \<open>\blankline\<close>

    codatatype 'a tree\<^sub>i\<^sub>s = Node\<^sub>i\<^sub>s (lbl\<^sub>i\<^sub>s: 'a) (sub\<^sub>i\<^sub>s: "'a tree\<^sub>i\<^sub>s fset")

text \<open>\blankline\<close>

    codatatype 'a sm = SM (accept: bool) (trans: "'a \<Rightarrow> 'a sm")


subsection \<open>Command Syntax
  \label{ssec:codatatype-command-syntax}\<close>

subsubsection \<open>\keyw{codatatype}
  \label{sssec:codatatype}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "codatatype"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command codatatype} target? @{syntax dt_options}? @{syntax dt_spec}
\<close>}

\medskip

\noindent
Definitions of codatatypes have almost exactly the same syntax as for datatypes
(Section~\ref{ssec:datatype-command-syntax}). The @{text "discs_sels"} option
is superfluous because discriminators and selectors are always generated for
codatatypes.
\<close>


subsection \<open>Generated Constants
  \label{ssec:codatatype-generated-constants}\<close>

text \<open>
Given a codatatype @{text "('a\<^sub>1, \<dots>, 'a\<^sub>m) t"}
with $m > 0$ live type variables and $n$ constructors @{text "t.C\<^sub>1"},
\ldots, @{text "t.C\<^sub>n"}, the same auxiliary constants are generated as for
datatypes (Section~\ref{ssec:datatype-generated-constants}), except that the
recursor is replaced by a dual concept:

\medskip

\begin{tabular}{@ {}ll@ {}}
Corecursor: &
  @{text t.corec_t}
\end{tabular}
\<close>


subsection \<open>Generated Theorems
  \label{ssec:codatatype-generated-theorems}\<close>

text \<open>
The characteristic theorems generated by @{command codatatype} are grouped in
three broad categories:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The \emph{free constructor theorems}
(Section~\ref{sssec:free-constructor-theorems}) are properties of the
constructors and destructors that can be derived for any freely generated type.

\item The \emph{functorial theorems}
(Section~\ref{sssec:functorial-theorems}) are properties of datatypes related to
their BNF nature.

\item The \emph{coinductive theorems} (Section~\ref{sssec:coinductive-theorems})
are properties of datatypes related to their coinductive nature.
\end{itemize}

\noindent
The first two categories are exactly as for datatypes.
\<close>


subsubsection \<open>Coinductive Theorems
  \label{sssec:coinductive-theorems}\<close>

text \<open>
The coinductive theorems are listed below for @{typ "'a llist"}:

\begin{indentblock}
\begin{description}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t."}\hthm{coinduct} @{text "[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t."}\hthm{coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n, coinduct t]"}\rm:
\end{tabular}] ~ \\
@{thm llist.coinduct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t."}\hthm{coinduct_strong} @{text "[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t."}\hthm{coinduct_strong} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
@{thm llist.coinduct_strong[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t."}\hthm{rel_coinduct} @{text "[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t."}\hthm{rel_coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n, coinduct pred]"}\rm:
\end{tabular}] ~ \\
@{thm llist.rel_coinduct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{coinduct} @{text "[case_names t\<^sub>1 \<dots> t\<^sub>m, case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"} \\
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{coinduct_strong} @{text "[case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{coinduct_strong} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"}\rm: \\
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{rel_coinduct} @{text "[case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{rel_coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"}\rm: \\
\end{tabular}] ~ \\
Given $m > 1$ mutually corecursive codatatypes, these coinduction rules can be
used to prove $m$ properties simultaneously.

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{set_induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n,"} \\
  \phantom{@{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{set_induct} @{text "["}}@{text "induct set: set\<^sub>j_t\<^sub>1, \<dots>, induct set: set\<^sub>j_t\<^sub>m]"}\rm: \\
\end{tabular}] ~ \\
@{thm llist.set_induct[no_vars]} \\
If $m = 1$, the attribute @{text "[consumes 1]"} is generated as well.

\item[@{text "t."}\hthm{corec}\rm:] ~ \\
@{thm llist.corec(1)[no_vars]} \\
@{thm llist.corec(2)[no_vars]}

\item[@{text "t."}\hthm{corec_code} @{text "[code]"}\rm:] ~ \\
@{thm llist.corec_code[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "t."}\hthm{corec_disc}\rm:] ~ \\
@{thm llist.corec_disc(1)[no_vars]} \\
@{thm llist.corec_disc(2)[no_vars]}

\item[@{text "t."}\hthm{corec_disc_iff} @{text "[simp]"}\rm:] ~ \\
@{thm llist.corec_disc_iff(1)[no_vars]} \\
@{thm llist.corec_disc_iff(2)[no_vars]}

\item[@{text "t."}\hthm{corec_sel} @{text "[simp]"}\rm:] ~ \\
@{thm llist.corec_sel(1)[no_vars]} \\
@{thm llist.corec_sel(2)[no_vars]}

\item[@{text "t."}\hthm{map_o_corec}\rm:] ~ \\
@{thm llist.map_o_corec[no_vars]}

\item[@{text "t."}\hthm{corec_transfer} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm llist.corec_transfer[no_vars]} \\
The @{text "[transfer_rule]"} attribute is set by the @{text transfer} plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\end{description}
\end{indentblock}

\noindent
For convenience, @{command codatatype} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{simps}] = @{text t.inject} @{text t.distinct} @{text t.case} @{text t.corec_disc_iff} @{text t.corec_sel} \\
@{text t.map} @{text t.rel_inject} @{text t.rel_distinct} @{text t.set}

\end{description}
\end{indentblock}
\<close>


section \<open>Defining Primitively Corecursive Functions
  \label{sec:defining-primitively-corecursive-functions}\<close>

text \<open>
Corecursive functions can be specified using the @{command primcorec} and
\keyw{prim\-corec\-ursive} commands, which support primitive corecursion.
Other approaches include the more general \keyw{partial_function} command, the
\keyw{corec} and \keyw{corecursive} commands, and techniques based on domains
and topologies @{cite "lochbihler-hoelzl-2014"}. In this tutorial, the focus is
on @{command primcorec} and @{command primcorecursive}; \keyw{corec} and
\keyw{corecursive} are described in a separate tutorial
@{cite "isabelle-corec"}. More examples can be found in the directories
\<^dir>\<open>~~/src/HOL/Datatype_Examples\<close> and \<^dir>\<open>~~/src/HOL/Corec_Examples\<close>.

Whereas recursive functions consume datatypes one constructor at a time,
corecursive functions construct codatatypes one constructor at a time.
Partly reflecting a lack of agreement among proponents of coalgebraic methods,
Isabelle supports three competing syntaxes for specifying a function $f$:

\begin{itemize}
\setlength{\itemsep}{0pt}

\abovedisplayskip=.5\abovedisplayskip
\belowdisplayskip=.5\belowdisplayskip

\item The \emph{destructor view} specifies $f$ by implications of the form
\[@{text "\<dots> \<Longrightarrow> is_C\<^sub>j (f x\<^sub>1 \<dots> x\<^sub>n)"}\] and
equations of the form
\[@{text "un_C\<^sub>ji (f x\<^sub>1 \<dots> x\<^sub>n) = \<dots>"}\]
This style is popular in the coalgebraic literature.

\item The \emph{constructor view} specifies $f$ by equations of the form
\[@{text "\<dots> \<Longrightarrow> f x\<^sub>1 \<dots> x\<^sub>n = C\<^sub>j \<dots>"}\]
This style is often more concise than the previous one.

\item The \emph{code view} specifies $f$ by a single equation of the form
\[@{text "f x\<^sub>1 \<dots> x\<^sub>n = \<dots>"}\]
with restrictions on the format of the right-hand side. Lazy functional
programming languages such as Haskell support a generalized version of this
style.
\end{itemize}

All three styles are available as input syntax. Whichever syntax is chosen,
characteristic theorems for all three styles are generated.

%%% TODO: partial_function? E.g. for defining tail recursive function on lazy
%%% lists (cf. terminal0 in TLList.thy)
\<close>


subsection \<open>Introductory Examples
  \label{ssec:primcorec-introductory-examples}\<close>

text \<open>
Primitive corecursion is illustrated through concrete examples based on the
codatatypes defined in Section~\ref{ssec:codatatype-introductory-examples}. More
examples can be found in the directory \<^dir>\<open>~~/src/HOL/Datatype_Examples\<close>.
The code view is favored in the examples below. Sections
\ref{ssec:primrec-constructor-view} and \ref{ssec:primrec-destructor-view}
present the same examples expressed using the constructor and destructor views.
\<close>


subsubsection \<open>Simple Corecursion
  \label{sssec:primcorec-simple-corecursion}\<close>

text \<open>
Following the code view, corecursive calls are allowed on the right-hand side as
long as they occur under a constructor, which itself appears either directly to
the right of the equal sign or in a conditional expression:
\<close>

    primcorec (*<*)(transfer) (*>*)literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" where
      "literate g x = LCons x (literate g (g x))"

text \<open>\blankline\<close>

    primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      "siterate g x = SCons x (siterate g (g x))"

text \<open>
\noindent
The constructor ensures that progress is made---i.e., the function is
\emph{productive}. The above functions compute the infinite lazy list or stream
@{text "[x, g x, g (g x), \<dots>]"}. Productivity guarantees that prefixes
@{text "[x, g x, g (g x), \<dots>, (g ^^ k) x]"} of arbitrary finite length
@{text k} can be computed by unfolding the code equation a finite number of
times.

Corecursive functions construct codatatype values, but nothing prevents them
from also consuming such values. The following function drops every second
element in a stream:
\<close>

    primcorec every_snd :: "'a stream \<Rightarrow> 'a stream" where
      "every_snd s = SCons (shd s) (stl (stl s))"

text \<open>
\noindent
Constructs such as @{text "let"}--@{text "in"}, @{text
"if"}--@{text "then"}--@{text "else"}, and @{text "case"}--@{text "of"} may
appear around constructors that guard corecursive calls:
\<close>

    primcorec lapp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lapp xs ys =
         (case xs of
            LNil \<Rightarrow> ys
          | LCons x xs' \<Rightarrow> LCons x (lapp xs' ys))"

text \<open>
\noindent
For technical reasons, @{text "case"}--@{text "of"} is only supported for
case distinctions on (co)datatypes that provide discriminators and selectors.

Pattern matching is not supported by @{command primcorec}. Fortunately, it is
easy to generate pattern-maching equations using the @{command simps_of_case}
command provided by the theory \<^file>\<open>~~/src/HOL/Library/Simps_Case_Conv.thy\<close>.
\<close>

    simps_of_case lapp_simps: lapp.code

text \<open>
This generates the lemma collection @{thm [source] lapp_simps}:
%
\begin{gather*}
  @{thm lapp_simps(1)[no_vars]} \\
  @{thm lapp_simps(2)[no_vars]}
\end{gather*}
%
Corecursion is useful to specify not only functions but also infinite objects:
\<close>

    primcorec infty :: enat where
      "infty = ESucc infty"

text \<open>
\noindent
The example below constructs a pseudorandom process value. It takes a stream of
actions (@{text s}), a pseudorandom function generator (@{text f}), and a
pseudorandom seed (@{text n}):
\<close>

(*<*)
    context early
    begin
(*>*)
    primcorec
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "random_process s f n =
         (if n mod 4 = 0 then
            Fail
          else if n mod 4 = 1 then
            Skip (random_process s f (f n))
          else if n mod 4 = 2 then
            Action (shd s) (random_process (stl s) f (f n))
          else
            Choice (random_process (every_snd s) (f \<circ> f) (f n))
              (random_process (every_snd (stl s)) (f \<circ> f) (f (f n))))"
(*<*)
    end
(*>*)

text \<open>
\noindent
The main disadvantage of the code view is that the conditions are tested
sequentially. This is visible in the generated theorems. The constructor and
destructor views offer nonsequential alternatives.
\<close>


subsubsection \<open>Mutual Corecursion
  \label{sssec:primcorec-mutual-corecursion}\<close>

text \<open>
The syntax for mutually corecursive functions over mutually corecursive
datatypes is unsurprising:
\<close>

    primcorec
      even_infty :: even_enat and
      odd_infty :: odd_enat
    where
      "even_infty = Even_ESucc odd_infty"
    | "odd_infty = Odd_ESucc even_infty"


subsubsection \<open>Nested Corecursion
  \label{sssec:primcorec-nested-corecursion}\<close>

text \<open>
The next pair of examples generalize the @{const literate} and @{const siterate}
functions (Section~\ref{sssec:primcorec-nested-corecursion}) to possibly
infinite trees in which subnodes are organized either as a lazy list (@{text
tree\<^sub>i\<^sub>i}) or as a finite set (@{text tree\<^sub>i\<^sub>s}). They rely on the map functions of
the nesting type constructors to lift the corecursive calls:
\<close>

    primcorec iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "iterate\<^sub>i\<^sub>i g x = Node\<^sub>i\<^sub>i x (lmap (iterate\<^sub>i\<^sub>i g) (g x))"

text \<open>\blankline\<close>

    primcorec iterate\<^sub>i\<^sub>s :: "('a \<Rightarrow> 'a fset) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>s" where
      "iterate\<^sub>i\<^sub>s g x = Node\<^sub>i\<^sub>s x (fimage (iterate\<^sub>i\<^sub>s g) (g x))"

text \<open>
\noindent
Both examples follow the usual format for constructor arguments associated
with nested recursive occurrences of the datatype. Consider
@{const iterate\<^sub>i\<^sub>i}. The term @{term "g x"} constructs an @{typ "'a llist"}
value, which is turned into an @{typ "'a tree\<^sub>i\<^sub>i llist"} value using
@{const lmap}.

This format may sometimes feel artificial. The following function constructs
a tree with a single, infinite branch from a stream:
\<close>

    primcorec tree\<^sub>i\<^sub>i_of_stream :: "'a stream \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "tree\<^sub>i\<^sub>i_of_stream s =
         Node\<^sub>i\<^sub>i (shd s) (lmap tree\<^sub>i\<^sub>i_of_stream (LCons (stl s) LNil))"

text \<open>
\noindent
A more natural syntax, also supported by Isabelle, is to move corecursive calls
under constructors:
\<close>

    primcorec (*<*)(in late) (*>*)tree\<^sub>i\<^sub>i_of_stream :: "'a stream \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "tree\<^sub>i\<^sub>i_of_stream s =
         Node\<^sub>i\<^sub>i (shd s) (LCons (tree\<^sub>i\<^sub>i_of_stream (stl s)) LNil)"

text \<open>
The next example illustrates corecursion through functions, which is a bit
special. Deterministic finite automata (DFAs) are traditionally defined as
5-tuples @{text "(Q, \<Sigma>, \<delta>, q\<^sub>0, F)"}, where @{text Q} is a finite set of states,
@{text \<Sigma>} is a finite alphabet, @{text \<delta>} is a transition function, @{text q\<^sub>0}
is an initial state, and @{text F} is a set of final states. The following
function translates a DFA into a state machine:
\<close>

    primcorec (*<*)(in early) (*>*)sm_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> 'a sm" where
      "sm_of_dfa \<delta> F q = SM (q \<in> F) (sm_of_dfa \<delta> F \<circ> \<delta> q)"

text \<open>
\noindent
The map function for the function type (@{text \<Rightarrow>}) is composition
(@{text "op \<circ>"}). For convenience, corecursion through functions can
also be expressed using $\lambda$-abstractions and function application rather
than through composition. For example:
\<close>

    primcorec sm_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> 'a sm" where
      "sm_of_dfa \<delta> F q = SM (q \<in> F) (\<lambda>a. sm_of_dfa \<delta> F (\<delta> q a))"

text \<open>\blankline\<close>

    primcorec empty_sm :: "'a sm" where
      "empty_sm = SM False (\<lambda>_. empty_sm)"

text \<open>\blankline\<close>

    primcorec not_sm :: "'a sm \<Rightarrow> 'a sm" where
      "not_sm M = SM (\<not> accept M) (\<lambda>a. not_sm (trans M a))"

text \<open>\blankline\<close>

    primcorec or_sm :: "'a sm \<Rightarrow> 'a sm \<Rightarrow> 'a sm" where
      "or_sm M N =
         SM (accept M \<or> accept N) (\<lambda>a. or_sm (trans M a) (trans N a))"

text \<open>
\noindent
For recursion through curried $n$-ary functions, $n$ applications of
@{term "op \<circ>"} are necessary. The examples below illustrate the case where
$n = 2$:
\<close>

    codatatype ('a, 'b) sm2 =
      SM2 (accept2: bool) (trans2: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) sm2")

text \<open>\blankline\<close>

    primcorec
      (*<*)(in early) (*>*)sm2_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> ('a, 'b) sm2"
    where
      "sm2_of_dfa \<delta> F q = SM2 (q \<in> F) (op \<circ> (op \<circ> (sm2_of_dfa \<delta> F)) (\<delta> q))"

text \<open>\blankline\<close>

    primcorec
      sm2_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> ('a, 'b) sm2"
    where
      "sm2_of_dfa \<delta> F q = SM2 (q \<in> F) (\<lambda>a b. sm2_of_dfa \<delta> F (\<delta> q a b))"


subsubsection \<open>Nested-as-Mutual Corecursion
  \label{sssec:primcorec-nested-as-mutual-corecursion}\<close>

text \<open>
Just as it is possible to recurse over nested recursive datatypes as if they
were mutually recursive
(Section~\ref{sssec:primrec-nested-as-mutual-recursion}), it is possible to
pretend that nested codatatypes are mutually corecursive. For example:
\<close>

(*<*)
    context late
    begin
(*>*)
    primcorec
      iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" and
      iterates\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a llist \<Rightarrow> 'a tree\<^sub>i\<^sub>i llist"
    where
      "iterate\<^sub>i\<^sub>i g x = Node\<^sub>i\<^sub>i x (iterates\<^sub>i\<^sub>i g (g x))"
    | "iterates\<^sub>i\<^sub>i g xs =
         (case xs of
            LNil \<Rightarrow> LNil
          | LCons x xs' \<Rightarrow> LCons (iterate\<^sub>i\<^sub>i g x) (iterates\<^sub>i\<^sub>i g xs'))"

text \<open>
\noindent
Coinduction rules are generated as
@{thm [source] iterate\<^sub>i\<^sub>i.coinduct},
@{thm [source] iterates\<^sub>i\<^sub>i.coinduct}, and
@{thm [source] iterate\<^sub>i\<^sub>i_iterates\<^sub>i\<^sub>i.coinduct}
and analogously for @{text coinduct_strong}. These rules and the
underlying corecursors are generated dynamically and are kept in a cache
to speed up subsequent definitions.
\<close>

(*<*)
    end
(*>*)


subsubsection \<open>Constructor View
  \label{ssec:primrec-constructor-view}\<close>

(*<*)
    locale ctr_view
    begin
(*>*)

text \<open>
The constructor view is similar to the code view, but there is one separate
conditional equation per constructor rather than a single unconditional
equation. Examples that rely on a single constructor, such as @{const literate}
and @{const siterate}, are identical in both styles.

Here is an example where there is a difference:
\<close>

    primcorec lapp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lapp xs ys = LNil"
    | "_ \<Longrightarrow> lapp xs ys = LCons (lhd (if lnull xs then ys else xs))
         (if xs = LNil then ltl ys else lapp (ltl xs) ys)"

text \<open>
\noindent
With the constructor view, we must distinguish between the @{const LNil} and
the @{const LCons} case. The condition for @{const LCons} is
left implicit, as the negation of that for @{const LNil}.

For this example, the constructor view is slightly more involved than the
code equation. Recall the code view version presented in
Section~\ref{sssec:primcorec-simple-corecursion}.
% TODO: \[{thm code_view.lapp.code}\]
The constructor view requires us to analyze the second argument (@{term ys}).
The code equation generated from the constructor view also suffers from this.
% TODO: \[{thm lapp.code}\]

In contrast, the next example is arguably more naturally expressed in the
constructor view:
\<close>

    primcorec
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "n mod 4 = 0 \<Longrightarrow> random_process s f n = Fail"
    | "n mod 4 = 1 \<Longrightarrow>
         random_process s f n = Skip (random_process s f (f n))"
    | "n mod 4 = 2 \<Longrightarrow>
         random_process s f n = Action (shd s) (random_process (stl s) f (f n))"
    | "n mod 4 = 3 \<Longrightarrow>
         random_process s f n = Choice (random_process (every_snd s) f (f n))
           (random_process (every_snd (stl s)) f (f n))"
(*<*)
    end
(*>*)

text \<open>
\noindent
Since there is no sequentiality, we can apply the equation for @{const Choice}
without having first to discharge @{term "n mod (4::int) \<noteq> 0"},
@{term "n mod (4::int) \<noteq> 1"}, and
@{term "n mod (4::int) \<noteq> 2"}.
The price to pay for this elegance is that we must discharge exclusiveness proof
obligations, one for each pair of conditions
@{term "(n mod (4::int) = i, n mod (4::int) = j)"}
with @{term "i < j"}. If we prefer not to discharge any obligations, we can
enable the @{text "sequential"} option. This pushes the problem to the users of
the generated properties.
%Here are more examples to conclude:
\<close>


subsubsection \<open>Destructor View
  \label{ssec:primrec-destructor-view}\<close>

(*<*)
    locale dtr_view
    begin
(*>*)

text \<open>
The destructor view is in many respects dual to the constructor view. Conditions
determine which constructor to choose, and these conditions are interpreted
sequentially or not depending on the @{text "sequential"} option.
Consider the following examples:
\<close>

    primcorec literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" where
      "\<not> lnull (literate _ x)"
    | "lhd (literate _ x) = x"
    | "ltl (literate g x) = literate g (g x)"

text \<open>\blankline\<close>

    primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      "shd (siterate _ x) = x"
    | "stl (siterate g x) = siterate g (g x)"

text \<open>\blankline\<close>

    primcorec every_snd :: "'a stream \<Rightarrow> 'a stream" where
      "shd (every_snd s) = shd s"
    | "stl (every_snd s) = stl (stl s)"

text \<open>
\noindent
The first formula in the @{const literate} specification indicates which
constructor to choose. For @{const siterate} and @{const every_snd}, no such
formula is necessary, since the type has only one constructor. The last two
formulas are equations specifying the value of the result for the relevant
selectors. Corecursive calls appear directly to the right of the equal sign.
Their arguments are unrestricted.

The next example shows how to specify functions that rely on more than one
constructor:
\<close>

    primcorec lapp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lapp xs ys)"
    | "lhd (lapp xs ys) = lhd (if lnull xs then ys else xs)"
    | "ltl (lapp xs ys) = (if xs = LNil then ltl ys else lapp (ltl xs) ys)"

text \<open>
\noindent
For a codatatype with $n$ constructors, it is sufficient to specify $n - 1$
discriminator formulas. The command will then assume that the remaining
constructor should be taken otherwise. This can be made explicit by adding
\<close>

(*<*)
    end

    locale dtr_view2
    begin

    primcorec lapp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lapp xs ys)"
    | "lhd (lapp xs ys) = lhd (if lnull xs then ys else xs)"
    | "ltl (lapp xs ys) = (if xs = LNil then ltl ys else lapp (ltl xs) ys)" |
(*>*)
      "_ \<Longrightarrow> \<not> lnull (lapp xs ys)"

text \<open>
\noindent
to the specification. The generated selector theorems are conditional.

The next example illustrates how to cope with selectors defined for several
constructors:
\<close>

    primcorec
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "n mod 4 = 0 \<Longrightarrow> random_process s f n = Fail"
    | "n mod 4 = 1 \<Longrightarrow> is_Skip (random_process s f n)"
    | "n mod 4 = 2 \<Longrightarrow> is_Action (random_process s f n)"
    | "n mod 4 = 3 \<Longrightarrow> is_Choice (random_process s f n)"
    | "cont (random_process s f n) = random_process s f (f n)" of Skip
    | "prefix (random_process s f n) = shd s"
    | "cont (random_process s f n) = random_process (stl s) f (f n)" of Action
    | "left (random_process s f n) = random_process (every_snd s) f (f n)"
    | "right (random_process s f n) = random_process (every_snd (stl s)) f (f n)"

text \<open>
\noindent
Using the @{text "of"} keyword, different equations are specified for @{const
cont} depending on which constructor is selected.

Here are more examples to conclude:
\<close>

    primcorec
      even_infty :: even_enat and
      odd_infty :: odd_enat
    where
      "even_infty \<noteq> Even_EZero"
    | "un_Even_ESucc even_infty = odd_infty"
    | "un_Odd_ESucc odd_infty = even_infty"

text \<open>\blankline\<close>

    primcorec iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "lbl\<^sub>i\<^sub>i (iterate\<^sub>i\<^sub>i g x) = x"
    | "sub\<^sub>i\<^sub>i (iterate\<^sub>i\<^sub>i g x) = lmap (iterate\<^sub>i\<^sub>i g) (g x)"
(*<*)
    end
(*>*)


subsection \<open>Command Syntax
  \label{ssec:primcorec-command-syntax}\<close>

subsubsection \<open>\keyw{primcorec} and \keyw{primcorecursive}
  \label{sssec:primcorecursive-and-primcorec}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "primcorec"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def "primcorecursive"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  (@@{command primcorec} | @@{command primcorecursive}) target? \<newline>
    @{syntax pcr_options}? fixes @'where' (@{syntax pcr_formula} + '|')
  ;
  @{syntax_def pcr_options}: '(' ((@{syntax plugins} | 'sequential' | 'exhaustive' | 'transfer') + ',') ')'
  ;
  @{syntax_def pcr_formula}: thmdecl? prop (@'of' (term * ))?
\<close>}

\medskip

\noindent
The @{command primcorec} and @{command primcorecursive} commands introduce a set
of mutually corecursive functions over codatatypes.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{fixes} denotes a list of names with optional type signatures,
\synt{thmdecl} denotes an optional name for the formula that follows, and
\synt{prop} denotes a HOL proposition @{cite "isabelle-isar-ref"}.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text plugins} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). By default, all plugins are enabled.

\item
The @{text sequential} option indicates that the conditions in specifications
expressed using the constructor or destructor view are to be interpreted
sequentially.

\item
The @{text exhaustive} option indicates that the conditions in specifications
expressed using the constructor or destructor view cover all possible cases.
This generally gives rise to an additional proof obligation.

\item
The @{text transfer} option indicates that an unconditional transfer rule
should be generated and proved @{text "by transfer_prover"}. The
@{text "[transfer_rule]"} attribute is set on the generated theorem.
\end{itemize}

The @{command primcorec} command is an abbreviation for @{command
primcorecursive} with @{text "by auto?"} to discharge any emerging proof
obligations.

%%% TODO: elaborate on format of the propositions
%%% TODO: elaborate on mutual and nested-to-mutual
\<close>


subsection \<open>Generated Theorems
  \label{ssec:primcorec-generated-theorems}\<close>

text \<open>
The @{command primcorec} and @{command primcorecursive} commands generate the
following properties (listed for @{const literate}):

\begin{indentblock}
\begin{description}

\item[@{text "f."}\hthm{code} @{text "[code]"}\rm:] ~ \\
@{thm literate.code[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "f."}\hthm{ctr}\rm:] ~ \\
@{thm literate.ctr[no_vars]}

\item[@{text "f."}\hthm{disc} @{text "[simp, code]"}\rm:] ~ \\
@{thm literate.disc[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}). The @{text "[simp]"} attribute is set only
for functions for which @{text f.disc_iff} is not available.

\item[@{text "f."}\hthm{disc_iff} @{text "[simp]"}\rm:] ~ \\
@{thm literate.disc_iff[no_vars]} \\
This property is generated only for functions declared with the
@{text exhaustive} option or whose conditions are trivially exhaustive.

\item[@{text "f."}\hthm{sel} @{text "[simp, code]"}\rm:] ~ \\
@{thm literate.disc[no_vars]} \\
The @{text "[code]"} attribute is set by the @{text code} plugin
(Section~\ref{ssec:code-generator}).

\item[@{text "f."}\hthm{exclude}\rm:] ~ \\
These properties are missing for @{const literate} because no exclusiveness
proof obligations arose. In general, the properties correspond to the
discharged proof obligations.

\item[@{text "f."}\hthm{exhaust}\rm:] ~ \\
This property is missing for @{const literate} because no exhaustiveness
proof obligation arose. In general, the property correspond to the discharged
proof obligation.

\item[\begin{tabular}{@ {}l@ {}}
  @{text "f."}\hthm{coinduct} @{text "[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "f."}\hthm{coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
This coinduction rule is generated for nested-as-mutual corecursive functions
(Section~\ref{sssec:primcorec-nested-as-mutual-corecursion}).

\item[\begin{tabular}{@ {}l@ {}}
  @{text "f."}\hthm{coinduct_strong} @{text "[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "f."}\hthm{coinduct_strong} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
This coinduction rule is generated for nested-as-mutual corecursive functions
(Section~\ref{sssec:primcorec-nested-as-mutual-corecursion}).

\item[\begin{tabular}{@ {}l@ {}}
  @{text "f\<^sub>1_\<dots>_f\<^sub>m."}\hthm{coinduct} @{text "[case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "f."}\hthm{coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
This coinduction rule is generated for nested-as-mutual corecursive functions
(Section~\ref{sssec:primcorec-nested-as-mutual-corecursion}). Given $m > 1$
mutually corecursive functions, this rule can be used to prove $m$ properties
simultaneously.

\item[\begin{tabular}{@ {}l@ {}}
  @{text "f\<^sub>1_\<dots>_f\<^sub>m."}\hthm{coinduct_strong} @{text "[case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "f."}\hthm{coinduct_strong} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
This coinduction rule is generated for nested-as-mutual corecursive functions
(Section~\ref{sssec:primcorec-nested-as-mutual-corecursion}). Given $m > 1$
mutually corecursive functions, this rule can be used to prove $m$ properties
simultaneously.

\end{description}
\end{indentblock}

\noindent
For convenience, @{command primcorec} and @{command primcorecursive} also
provide the following collection:

\begin{indentblock}
\begin{description}

\item[@{text "f."}\hthm{simps}] = @{text f.disc_iff} (or @{text f.disc}) @{text t.sel}

\end{description}
\end{indentblock}
\<close>


(*
subsection \<open>Recursive Default Values for Selectors
  \label{ssec:primcorec-recursive-default-values-for-selectors}\<close>

text \<open>
partial_function to the rescue
\<close>
*)


section \<open>Registering Bounded Natural Functors
  \label{sec:registering-bounded-natural-functors}\<close>

text \<open>
The (co)datatype package can be set up to allow nested recursion through
arbitrary type constructors, as long as they adhere to the BNF requirements
and are registered as BNFs. It is also possible to declare a BNF abstractly
without specifying its internal structure.
\<close>


subsection \<open>Bounded Natural Functors
  \label{ssec:bounded-natural-functors}\<close>

text \<open>
Bounded natural functors (BNFs) are a semantic criterion for where
(co)re\-cur\-sion may appear on the right-hand side of an equation
@{cite "traytel-et-al-2012" and "blanchette-et-al-2015-wit"}.

An $n$-ary BNF is a type constructor equipped with a map function
(functorial action), $n$ set functions (natural transformations),
and an infinite cardinal bound that satisfy certain properties.
For example, @{typ "'a llist"} is a unary BNF.
Its predicator @{text "llist_all ::
  ('a \<Rightarrow> bool) \<Rightarrow>
  'a llist \<Rightarrow> bool"}
extends unary predicates over elements to unary predicates over
lazy lists.
Similarly, its relator @{text "llist_all2 ::
  ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
  'a llist \<Rightarrow> 'b llist \<Rightarrow> bool"}
extends binary predicates over elements to binary predicates over parallel
lazy lists. The cardinal bound limits the number of elements returned by the
set function; it may not depend on the cardinality of @{typ 'a}.

The type constructors introduced by @{command datatype} and
@{command codatatype} are automatically registered as BNFs. In addition, a
number of old-style datatypes and non-free types are preregistered.

Given an $n$-ary BNF, the $n$ type variables associated with set functions,
and on which the map function acts, are \emph{live}; any other variables are
\emph{dead}. Nested (co)recursion can only take place through live variables.
\<close>


subsection \<open>Introductory Examples
  \label{ssec:bnf-introductory-examples}\<close>

text \<open>
The example below shows how to register a type as a BNF using the @{command bnf}
command. Some of the proof obligations are best viewed with the theory
\<^file>\<open>~~/src/HOL/Library/Cardinal_Notations.thy\<close> imported.

The type is simply a copy of the function space @{typ "'d \<Rightarrow> 'a"}, where @{typ 'a}
is live and @{typ 'd} is dead. We introduce it together with its map function,
set function, predicator, and relator.
\<close>

    typedef ('d, 'a) fn = "UNIV :: ('d \<Rightarrow> 'a) set"
      by simp

text \<open>\blankline\<close>

    setup_lifting type_definition_fn

text \<open>\blankline\<close>

    lift_definition map_fn :: "('a \<Rightarrow> 'b) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn" is "op \<circ>" .
    lift_definition set_fn :: "('d, 'a) fn \<Rightarrow> 'a set" is range .

text \<open>\blankline\<close>

    lift_definition
      pred_fn :: "('a \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fn \<Rightarrow> bool"
    is
      "pred_fun (\<lambda>_. True)" .

    lift_definition
      rel_fn :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn \<Rightarrow> bool"
    is
      "rel_fun (op =)" .

text \<open>\blankline\<close>

    bnf "('d, 'a) fn"
      map: map_fn
      sets: set_fn
      bd: "natLeq +c |UNIV :: 'd set|"
      rel: rel_fn
      pred: pred_fn
    proof -
      show "map_fn id = id"
        by transfer auto
    next
      fix f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
      show "map_fn (g \<circ> f) = map_fn g \<circ> map_fn f"
        by transfer (auto simp add: comp_def)
    next
      fix F :: "('d, 'a) fn" and f g :: "'a \<Rightarrow> 'b"
      assume "\<And>x. x \<in> set_fn F \<Longrightarrow> f x = g x"
      then show "map_fn f F = map_fn g F"
        by transfer auto
    next
      fix f :: "'a \<Rightarrow> 'b"
      show "set_fn \<circ> map_fn f = op ` f \<circ> set_fn"
        by transfer (auto simp add: comp_def)
    next
      show "card_order (natLeq +c |UNIV :: 'd set| )"
        apply (rule card_order_csum)
        apply (rule natLeq_card_order)
        by (rule card_of_card_order_on)
    next
      show "cinfinite (natLeq +c |UNIV :: 'd set| )"
        apply (rule cinfinite_csum)
        apply (rule disjI1)
        by (rule natLeq_cinfinite)
    next
      fix F :: "('d, 'a) fn"
      have "|set_fn F| \<le>o |UNIV :: 'd set|" (is "_ \<le>o ?U")
        by transfer (rule card_of_image)
      also have "?U \<le>o natLeq +c ?U"
        by (rule ordLeq_csum2) (rule card_of_Card_order)
      finally show "|set_fn F| \<le>o natLeq +c |UNIV :: 'd set|" .
    next
      fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
      show "rel_fn R OO rel_fn S \<le> rel_fn (R OO S)"
        by (rule, transfer) (auto simp add: rel_fun_def)
    next
      fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
      show "rel_fn R = (\<lambda>x y. \<exists>z. set_fn z \<subseteq> {(x, y). R x y} \<and> map_fn fst z = x \<and> map_fn snd z = y)"
        unfolding fun_eq_iff relcompp.simps conversep.simps
        by transfer (force simp: rel_fun_def subset_iff)
    next
      fix P :: "'a \<Rightarrow> bool"
      show "pred_fn P = (\<lambda>x. Ball (set_fn x) P)"
        unfolding fun_eq_iff by transfer simp
    qed

text \<open>\blankline\<close>

    print_theorems
    print_bnfs

text \<open>
\noindent
Using \keyw{print_theorems} and @{command print_bnfs}, we can contemplate and
show the world what we have achieved.

This particular example does not need any nonemptiness witness, because the
one generated by default is good enough, but in general this would be
necessary. See \<^file>\<open>~~/src/HOL/Basic_BNFs.thy\<close>,
\<^file>\<open>~~/src/HOL/Library/Countable_Set_Type.thy\<close>,
\<^file>\<open>~~/src/HOL/Library/FSet.thy\<close>, and
\<^file>\<open>~~/src/HOL/Library/Multiset.thy\<close> for further examples of BNF
registration, some of which feature custom witnesses.

For many typedefs, lifting the BNF structure from the raw type to the abstract
type can be done uniformly. This is the task of the @{command lift_bnf} command.
Using @{command lift_bnf}, the above registration of @{typ "('d, 'a) fn"} as a
BNF becomes much shorter:
\<close>

(*<*)
    context early
    begin
(*>*)
    lift_bnf (*<*)(no_warn_wits) (*>*)('d, 'a) fn
      by auto
(*<*)
    end
(*>*)

text \<open>
For type copies (@{command typedef}s with @{term UNIV} as the representing set),
the proof obligations are so simple that they can be
discharged automatically, yielding another command, @{command copy_bnf}, which
does not emit any proof obligations:
\<close>

(*<*)
    context late
    begin
(*>*)
    copy_bnf ('d, 'a) fn
(*<*)
    end
(*>*)

text \<open>
Since record schemas are type copies, @{command copy_bnf} can be used to
register them as BNFs:
\<close>

    record 'a point =
      xval :: 'a
      yval :: 'a

text \<open>\blankline\<close>

    copy_bnf ('a, 'z) point_ext

text \<open>
In the general case, the proof obligations generated by @{command lift_bnf} are
simpler than the acual BNF properties. In particular, no cardinality reasoning
is required. Consider the following type of nonempty lists:
\<close>

    typedef 'a nonempty_list = "{xs :: 'a list. xs \<noteq> []}" by auto

text \<open>
The @{command lift_bnf} command requires us to prove that the set of nonempty lists
is closed under the map function and the zip function. The latter only
occurs implicitly in the goal, in form of the variable
@{term "zs :: ('a \<times> 'b) list"}.
\<close>

    lift_bnf (*<*)(no_warn_wits) (*>*)'a nonempty_list
    proof -
      fix f (*<*):: "'a \<Rightarrow> 'c"(*>*)and xs :: "'a list"
      assume "xs \<in> {xs. xs \<noteq> []}"
      then show "map f xs \<in> {xs. xs \<noteq> []}"
        by (cases xs(*<*) rule: list.exhaust(*>*)) auto
    next
      fix zs :: "('a \<times> 'b) list"
      assume "map fst zs \<in> {xs. xs \<noteq> []}" "map snd zs \<in> {xs. xs \<noteq> []}"
      then show "zs \<in> {xs. xs \<noteq> []}"
        by (cases zs (*<*)rule: list.exhaust(*>*)) auto
    qed

text \<open>
The next example declares a BNF axiomatically. This can be convenient for
reasoning abstractly about an arbitrary BNF. The @{command bnf_axiomatization}
command below introduces a type @{text "('a, 'b, 'c) F"}, three set constants,
a map function, a predicator, a relator, and a nonemptiness witness that depends only on
@{typ 'a}. The type @{text "'a \<Rightarrow> ('a, 'b, 'c) F"} of the witness can be read
as an implication: Given a witness for @{typ 'a}, we can construct a witness for
@{text "('a, 'b, 'c) F"}. The BNF properties are postulated as axioms.
\<close>

    bnf_axiomatization (setA: 'a, setB: 'b, setC: 'c) F
      [wits: "'a \<Rightarrow> ('a, 'b, 'c) F"]

text \<open>\blankline\<close>

    print_theorems
    print_bnfs


subsection \<open>Command Syntax
  \label{ssec:bnf-command-syntax}\<close>

subsubsection \<open>\keyw{bnf}
  \label{sssec:bnf}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "bnf"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  @@{command bnf} target? (name ':')? type \<newline>
    'map:' term ('sets:' (term +))? 'bd:' term \<newline>
    ('wits:' (term +))? ('rel:' term)? \<newline>
    ('pred:' term)? @{syntax plugins}?
\<close>}

\medskip

\noindent
The @{command bnf} command registers an existing type as a bounded natural
functor (BNF). The type must be equipped with an appropriate map function
(functorial action). In addition, custom set functions, predicators, relators, and
nonemptiness witnesses can be specified; otherwise, default versions are used.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{type} denotes a HOL type, and \synt{term} denotes a HOL term
@{cite "isabelle-isar-ref"}.

The @{syntax plugins} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). By default, all plugins are enabled.

%%% TODO: elaborate on proof obligations
\<close>

subsubsection \<open>\keyw{lift_bnf}
  \label{sssec:lift-bnf}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "lift_bnf"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  @@{command lift_bnf} target? lb_options? \<newline>
    @{syntax tyargs} name wit_terms?  \<newline>
    ('via' thm)? @{syntax map_rel_pred}?
  ;
  @{syntax_def lb_options}: '(' ((@{syntax plugins} | 'no_warn_wits') + ',') ')'
  ;
  @{syntax_def wit_terms}: '[' 'wits' ':' terms ']'
\<close>}
\medskip

\noindent
The @{command lift_bnf} command registers as a BNF an existing type (the
\emph{abstract type}) that was defined as a subtype of a BNF (the \emph{raw
type}) using the @{command typedef} command. To achieve this, it lifts the BNF
structure on the raw type to the abstract type following a @{term
type_definition} theorem. The theorem is usually inferred from the type, but can
also be explicitly supplied by means of the optional @{text via} clause. In
addition, custom names for the set functions, the map function, the predicator, and the relator,
as well as nonemptiness witnesses can be specified.

Nonemptiness witnesses are not lifted from the raw type's BNF, as this would be
incomplete. They must be given as terms (on the raw type) and proved to be
witnesses. The command warns about witness types that are present in the raw
type's BNF but not supplied by the user. The warning can be disabled by
specifying the @{text no_warn_wits} option.
\<close>

subsubsection \<open>\keyw{copy_bnf}
  \label{sssec:copy-bnf}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "copy_bnf"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command copy_bnf} target? ('(' @{syntax plugins} ')')? \<newline>
    @{syntax tyargs} name ('via' thm)? @{syntax map_rel_pred}?
\<close>}
\medskip

\noindent
The @{command copy_bnf} command performs the same lifting as @{command lift_bnf}
for type copies (@{command typedef}s with @{term UNIV} as the representing set),
without requiring the user to discharge any proof obligations or provide
nonemptiness witnesses.
\<close>

subsubsection \<open>\keyw{bnf_axiomatization}
  \label{sssec:bnf-axiomatization}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "bnf_axiomatization"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command bnf_axiomatization} target? ('(' @{syntax plugins} ')')? \<newline>
    @{syntax tyargs}? name @{syntax wit_types}? \<newline>
    mixfix? @{syntax map_rel_pred}?
  ;
  @{syntax_def wit_types}: '[' 'wits' ':' types ']'
\<close>}

\medskip

\noindent
The @{command bnf_axiomatization} command declares a new type and associated constants
(map, set, predicator, relator, and cardinal bound) and asserts the BNF properties for
these constants as axioms.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{name} denotes an identifier, \synt{typefree} denotes fixed type variable
(@{typ 'a}, @{typ 'b}, \ldots), \synt{mixfix} denotes the usual parenthesized
mixfix notation, and \synt{types} denotes a space-separated list of types
@{cite "isabelle-isar-ref"}.

The @{syntax plugins} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). By default, all plugins are enabled.

Type arguments are live by default; they can be marked as dead by entering
@{text dead} in front of the type variable (e.g., @{text "(dead 'a)"})
instead of an identifier for the corresponding set function. Witnesses can be
specified by their types. Otherwise, the syntax of @{command bnf_axiomatization}
is identical to the left-hand side of a @{command datatype} or
@{command codatatype} definition.

The command is useful to reason abstractly about BNFs. The axioms are safe
because there exist BNFs of arbitrary large arities. Applications must import
the \<^file>\<open>~~/src/HOL/Library/BNF_Axiomatization.thy\<close> theory
to use this functionality.
\<close>


subsubsection \<open>\keyw{print_bnfs}
  \label{sssec:print-bnfs}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "print_bnfs"} & : & @{text "local_theory \<rightarrow>"}
\end{matharray}

@{rail \<open>
  @@{command print_bnfs}
\<close>}
\<close>


section \<open>Deriving Destructors and Theorems for Free Constructors
  \label{sec:deriving-destructors-and-theorems-for-free-constructors}\<close>

text \<open>
The derivation of convenience theorems for types equipped with free constructors,
as performed internally by @{command datatype} and @{command codatatype},
is available as a stand-alone command called @{command free_constructors}.

%  * need for this is rare but may arise if you want e.g. to add destructors to
%    a type not introduced by ...
%
%  * @{command free_constructors}
%    * @{text plugins}, @{text discs_sels}
%    * hack to have both co and nonco view via locale (cf. ext nats)
\<close>


(*
subsection \<open>Introductory Example
  \label{ssec:ctors-introductory-example}\<close>
*)


subsection \<open>Command Syntax
  \label{ssec:ctors-command-syntax}\<close>

subsubsection \<open>\keyw{free_constructors}
  \label{sssec:free-constructors}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "free_constructors"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  @@{command free_constructors} target? @{syntax dt_options} \<newline>
    name 'for' (@{syntax fc_ctor} + '|') \<newline>
  (@'where' (prop + '|'))?
  ;
  @{syntax_def fc_ctor}: (name ':')? term (name * )
\<close>}

\medskip

\noindent
The @{command free_constructors} command generates destructor constants for
freely constructed types as well as properties about constructors and
destructors. It also registers the constants and theorems in a data structure
that is queried by various tools (e.g., \keyw{function}).

The syntactic entity \synt{target} can be used to specify a local context,
\synt{name} denotes an identifier, \synt{prop} denotes a HOL proposition, and
\synt{term} denotes a HOL term @{cite "isabelle-isar-ref"}.

The syntax resembles that of @{command datatype} and @{command codatatype}
definitions (Sections
\ref{ssec:datatype-command-syntax}~and~\ref{ssec:codatatype-command-syntax}).
A constructor is specified by an optional name for the discriminator, the
constructor itself (as a term), and a list of optional names for the selectors.

Section~\ref{ssec:datatype-generated-theorems} lists the generated theorems.
For bootstrapping reasons, the generally useful @{text "[fundef_cong]"}
attribute is not set on the generated @{text case_cong} theorem. It can be
added manually using \keyw{declare}.
\<close>


subsubsection \<open>\keyw{simps_of_case}
  \label{sssec:simps-of-case}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "simps_of_case"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command simps_of_case} target? (name ':')? \<newline>
    (thm + ) (@'splits' ':' (thm + ))?
\<close>}

\medskip

\noindent
The @{command simps_of_case} command provided by theory
\<^file>\<open>~~/src/HOL/Library/Simps_Case_Conv.thy\<close> converts a single equation with
a complex case expression on the right-hand side into a set of pattern-matching
equations. For example,
\<close>

(*<*)
    context late
    begin
(*>*)
    simps_of_case lapp_simps: lapp.code

text \<open>
\noindent
translates @{thm lapp.code[no_vars]} into
%
\begin{gather*}
  @{thm lapp_simps(1)[no_vars]} \\
  @{thm lapp_simps(2)[no_vars]}
\end{gather*}
\<close>


subsubsection \<open>\keyw{case_of_simps}
  \label{sssec:case-of-simps}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "case_of_simps"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command case_of_simps} target? (name ':')? \<newline>
    (thm + )
\<close>}

\medskip

\noindent
The \keyw{case_of_simps} command provided by theory
\<^file>\<open>~~/src/HOL/Library/Simps_Case_Conv.thy\<close> converts a set of
pattern-matching equations into single equation with a complex case expression
on the right-hand side (cf.\ @{command simps_of_case}). For example,
\<close>

    case_of_simps lapp_case: lapp_simps

text \<open>
\noindent
translates
%
\begin{gather*}
  @{thm lapp_simps(1)[no_vars]} \\
  @{thm lapp_simps(2)[no_vars]}
\end{gather*}
%
into @{thm lapp_case[no_vars]}.
\<close>
(*<*)
    end
(*>*)


(*
section \<open>Using the Standard ML Interface
  \label{sec:using-the-standard-ml-interface}\<close>

text \<open>
The package's programmatic interface.
\<close>
*)


section \<open>Selecting Plugins
  \label{sec:selecting-plugins}\<close>

text \<open>
Plugins extend the (co)datatype package to interoperate with other Isabelle
packages and tools, such as the code generator, Transfer, Lifting, and
Quickcheck. They can be enabled or disabled individually using the
@{syntax plugins} option to the commands @{command datatype},
@{command primrec}, @{command codatatype}, @{command primcorec},
@{command primcorecursive}, @{command bnf}, @{command bnf_axiomatization}, and
@{command free_constructors}. For example:
\<close>

    datatype (plugins del: code "quickcheck") color = Red | Black

text \<open>
Beyond the standard plugins, the \emph{Archive of Formal Proofs} includes a
\keyw{derive} command that derives class instances of datatypes
@{cite "sternagel-thiemann-2015"}.
\<close>

subsection \<open>Code Generator
  \label{ssec:code-generator}\<close>

text \<open>
The \hthm{code} plugin registers freely generated types, including
(co)datatypes, and (co)recursive functions for code generation. No distinction
is made between datatypes and codatatypes. This means that for target languages
with a strict evaluation strategy (e.g., Standard ML), programs that attempt to
produce infinite codatatype values will not terminate.

For types, the plugin derives the following properties:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{eq.refl} @{text "[code nbe]"}\rm:] ~ \\
@{thm list.eq.refl[no_vars]}

\item[@{text "t."}\hthm{eq.simps} @{text "[code]"}\rm:] ~ \\
@{thm list.eq.simps(1)[no_vars]} \\
@{thm list.eq.simps(2)[no_vars]} \\
@{thm list.eq.simps(3)[no_vars]} \\
@{thm list.eq.simps(4)[no_vars]} \\
@{thm list.eq.simps(5)[no_vars]} \\
@{thm list.eq.simps(6)[no_vars]}

\end{description}
\end{indentblock}

In addition, the plugin sets the @{text "[code]"} attribute on a number of
properties of freely generated types and of (co)recursive functions, as
documented in Sections \ref{ssec:datatype-generated-theorems},
\ref{ssec:primrec-generated-theorems}, \ref{ssec:codatatype-generated-theorems},
and~\ref{ssec:primcorec-generated-theorems}.
\<close>


subsection \<open>Size
  \label{ssec:size}\<close>

text \<open>
For each datatype @{text t}, the \hthm{size} plugin generates a generic size
function @{text "t.size_t"} as well as a specific instance
@{text "size :: t \<Rightarrow> nat"} belonging to the @{text size} type class. The
\keyw{fun} command relies on @{const size} to prove termination of recursive
functions on datatypes.

The plugin derives the following properties:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{size} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.size(1)[no_vars]} \\
@{thm list.size(2)[no_vars]} \\
@{thm list.size(3)[no_vars]} \\
@{thm list.size(4)[no_vars]}

\item[@{text "t."}\hthm{size_gen}\rm:] ~ \\
@{thm list.size_gen(1)[no_vars]} \\
@{thm list.size_gen(2)[no_vars]}

\item[@{text "t."}\hthm{size_gen_o_map}\rm:] ~ \\
@{thm list.size_gen_o_map[no_vars]}

\item[@{text "t."}\hthm{size_neq}\rm:] ~ \\
This property is missing for @{typ "'a list"}. If the @{term size} function
always evaluates to a non-zero value, this theorem has the form
@{prop "\<not> size x = 0"}.

\end{description}
\end{indentblock}

The @{text "t.size"} and @{text "t.size_t"} functions generated for datatypes
defined by nested recursion through a datatype @{text u} depend on
@{text "u.size_u"}.

If the recursion is through a non-datatype @{text u} with type arguments
@{text "'a\<^sub>1, \<dots>, 'a\<^sub>m"}, by default @{text u} values are given a size of 0. This
can be improved upon by registering a custom size function of type
@{text "('a\<^sub>1 \<Rightarrow> nat) \<Rightarrow> \<dots> \<Rightarrow> ('a\<^sub>m \<Rightarrow> nat) \<Rightarrow> u \<Rightarrow> nat"} using
the ML function @{ML BNF_LFP_Size.register_size} or
@{ML BNF_LFP_Size.register_size_global}. See theory
\<^file>\<open>~~/src/HOL/Library/Multiset.thy\<close> for an example.
\<close>


subsection \<open>Transfer
  \label{ssec:transfer}\<close>

text \<open>
For each (co)datatype with live type arguments and each manually registered BNF,
the \hthm{transfer} plugin generates a predicator @{text "t.pred_t"} and
properties that guide the Transfer tool.

For types with at least one live type argument and \emph{no dead type
arguments}, the plugin derives the following properties:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{Domainp_rel} @{text "[relator_domain]"}\rm:] ~ \\
@{thm list.Domainp_rel[no_vars]}

\item[@{text "t."}\hthm{left_total_rel} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.left_total_rel[no_vars]}

\item[@{text "t."}\hthm{left_unique_rel} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.left_unique_rel[no_vars]}

\item[@{text "t."}\hthm{right_total_rel} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.right_total_rel[no_vars]}

\item[@{text "t."}\hthm{right_unique_rel} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.right_unique_rel[no_vars]}

\item[@{text "t."}\hthm{bi_total_rel} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.bi_total_rel[no_vars]}

\item[@{text "t."}\hthm{bi_unique_rel} @{text "[transfer_rule]"}\rm:] ~ \\
@{thm list.bi_unique_rel[no_vars]}

\end{description}
\end{indentblock}

For (co)datatypes with at least one live type argument, the plugin sets the
@{text "[transfer_rule]"} attribute on the following (co)datatypes properties:
@{text "t.case_"}\allowbreak @{text "transfer"},
@{text "t.sel_"}\allowbreak @{text "transfer"},
@{text "t.ctr_"}\allowbreak @{text "transfer"},
@{text "t.disc_"}\allowbreak @{text "transfer"},
@{text "t.rec_"}\allowbreak @{text "transfer"}, and
@{text "t.corec_"}\allowbreak @{text "transfer"}.
For (co)datatypes that further have \emph{no dead type arguments}, the plugin
sets @{text "[transfer_rule]"} on
@{text "t.set_"}\allowbreak @{text "transfer"},
@{text "t.map_"}\allowbreak @{text "transfer"}, and
@{text "t.rel_"}\allowbreak @{text "transfer"}.

For @{command primrec}, @{command primcorec}, and @{command primcorecursive},
the plugin implements the generation of the @{text "f.transfer"} property,
conditioned by the @{text transfer} option, and sets the
@{text "[transfer_rule]"} attribute on these.
\<close>


subsection \<open>Lifting
  \label{ssec:lifting}\<close>

text \<open>
For each (co)datatype and each manually registered BNF with at least one live
type argument \emph{and no dead type arguments}, the \hthm{lifting} plugin
generates properties and attributes that guide the Lifting tool.

The plugin derives the following property:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{Quotient} @{text "[quot_map]"}\rm:] ~ \\
@{thm list.Quotient[no_vars]}

\end{description}
\end{indentblock}

In addition, the plugin sets the @{text "[relator_eq]"} attribute on a
variant of the @{text t.rel_eq_onp} property, the @{text "[relator_mono]"}
attribute on @{text t.rel_mono}, and the @{text "[relator_distr]"} attribute
on @{text t.rel_compp}.
\<close>


subsection \<open>Quickcheck
  \label{ssec:quickcheck}\<close>

text \<open>
The integration of datatypes with Quickcheck is accomplished by the
\hthm{quick\-check} plugin. It combines a number of subplugins that instantiate
specific type classes. The subplugins can be enabled or disabled individually.
They are listed below:

\begin{indentblock}
\hthm{quickcheck_random} \\
\hthm{quickcheck_exhaustive} \\
\hthm{quickcheck_bounded_forall} \\
\hthm{quickcheck_full_exhaustive} \\
\hthm{quickcheck_narrowing}
\end{indentblock}
\<close>


subsection \<open>Program Extraction
  \label{ssec:program-extraction}\<close>

text \<open>
The \hthm{extraction} plugin provides realizers for induction and case analysis,
to enable program extraction from proofs involving datatypes. This functionality
is only available with full proof objects, i.e., with the \emph{HOL-Proofs}
session.
\<close>


section \<open>Known Bugs and Limitations
  \label{sec:known-bugs-and-limitations}\<close>

text \<open>
This section lists the known bugs and limitations of the (co)datatype package at
the time of this writing.

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
\emph{Defining mutually (co)recursive (co)datatypes can be slow.} Fortunately,
it is always possible to recast mutual specifications to nested ones, which are
processed more efficiently.

\item
\emph{Locally fixed types and terms cannot be used in type specifications.}
The limitation on types can be circumvented by adding type arguments to the local
(co)datatypes to abstract over the locally fixed types.

\item
\emph{The \emph{\keyw{primcorec}} command does not allow user-specified names and
attributes next to the entered formulas.} The less convenient syntax, using the
\keyw{lemmas} command, is available as an alternative.

\item
\emph{The \emph{\keyw{primcorec}} command does not allow corecursion under
@{text "case"}--@{text "of"} for datatypes that are defined without
discriminators and selectors.}

\item
\emph{There is no way to use an overloaded constant from a syntactic type
class, such as @{text 0}, as a constructor.}

\item
\emph{There is no way to register the same type as both a datatype and a
codatatype.} This affects types such as the extended natural numbers, for which
both views would make sense (for a different set of constructors).

\item
\emph{The names of variables are often suboptimal in the properties generated by
the package.}

\item
\emph{The compatibility layer sometimes produces induction principles with a
slightly different ordering of the premises than the old package.}

\end{enumerate}
\<close>


text \<open>
\section*{Acknowledgment}

Tobias Nipkow and Makarius Wenzel encouraged us to implement the new
(co)datatype package. Andreas Lochbihler provided lots of comments on earlier
versions of the package, especially on the coinductive part. Brian Huffman
suggested major simplifications to the internal constructions. Ond\v{r}ej
Kun\v{c}ar implemented the @{text transfer} and @{text lifting} plugins.
Christian Sternagel and Ren\'e Thiemann ported the \keyw{derive} command
from the \emph{Archive of Formal Proofs} to the new datatypes. Gerwin Klein and
Lars Noschinski implemented the @{command simps_of_case} and @{command
case_of_simps} commands. Florian Haftmann, Christian Urban, and Makarius
Wenzel provided general advice on Isabelle and package writing. Stefan Milius
and Lutz Schr\"oder found an elegant proof that eliminated one of the BNF
proof obligations. Mamoun Filali-Amine, Gerwin Klein, Andreas Lochbihler,
Tobias Nipkow, and Christian Sternagel suggested many textual improvements to
this tutorial.
\<close>

end
