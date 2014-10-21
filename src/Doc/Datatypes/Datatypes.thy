(*  Title:      Doc/Datatypes/Datatypes.thy
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
  "~~/src/HOL/Library/BNF_Axiomatization"
  "~~/src/HOL/Library/Cardinal_Notations"
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/Simps_Case_Conv"
begin

section {* Introduction
  \label{sec:introduction} *}

text {*
The 2013 edition of Isabelle introduced a definitional package for freely
generated datatypes and codatatypes. This package replaces the earlier
implementation due to Berghofer and Wenzel @{cite "Berghofer-Wenzel:1999:TPHOL"}.
Perhaps the main advantage of the new package is that it supports recursion
through a large class of non-datatypes, such as finite sets:
*}

    datatype 'a tree\<^sub>f\<^sub>s = Node\<^sub>f\<^sub>s (lbl\<^sub>f\<^sub>s: 'a) (sub\<^sub>f\<^sub>s: "'a tree\<^sub>f\<^sub>s fset")

text {*
\noindent
Another strong point is the support for local definitions:
*}

    context linorder
    begin
    datatype flag = Less | Eq | Greater
    end

text {*
\noindent
Furthermore, the package provides a lot of convenience, including automatically
generated discriminators, selectors, and relators as well as a wealth of
properties about them.

In addition to inductive datatypes, the package supports coinductive
datatypes, or \emph{codatatypes}, which allow infinite values. For example, the
following command introduces the type of lazy lists, which comprises both finite
and infinite values:
*}

(*<*)
    locale early
    locale late
(*>*)
    codatatype (*<*)(in early) (*>*)'a llist = LNil | LCons 'a "'a llist"

text {*
\noindent
Mixed inductive--coinductive recursion is possible via nesting. Compare the
following four Rose tree examples:
*}

    datatype (*<*)(in early) (*>*)'a tree\<^sub>f\<^sub>f = Node\<^sub>f\<^sub>f 'a "'a tree\<^sub>f\<^sub>f list"
    datatype (*<*)(in early) (*>*)'a tree\<^sub>f\<^sub>i = Node\<^sub>f\<^sub>i 'a "'a tree\<^sub>f\<^sub>i llist"
    codatatype (*<*)(in early) (*>*)'a tree\<^sub>i\<^sub>f = Node\<^sub>i\<^sub>f 'a "'a tree\<^sub>i\<^sub>f list"
    codatatype (*<*)(in early) (*>*)'a tree\<^sub>i\<^sub>i = Node\<^sub>i\<^sub>i 'a "'a tree\<^sub>i\<^sub>i llist"

text {*
The first two tree types allow only paths of finite length, whereas the last two
allow infinite paths. Orthogonally, the nodes in the first and third types have
finitely many direct subtrees, whereas those of the second and fourth may have
infinite branching.

The package is part of @{theory Main}. Additional functionality is provided by
the theory @{theory BNF_Axiomatization}, located in the directory
\verb|~~/src/HOL/Library|.

The package, like its predecessor, fully adheres to the LCF philosophy
@{cite mgordon79}: The characteristic theorems associated with the specified
(co)datatypes are derived rather than introduced axiomatically.%
\footnote{However, some of the
internal constructions and most of the internal proof obligations are omitted
if the @{text quick_and_dirty} option is enabled.}
The package is described in a number of papers
@{cite "traytel-et-al-2012" and "blanchette-et-al-wit" and
  "blanchette-et-al-2014-impl" and "panny-et-al-2014"}.
The central notion is that of a \emph{bounded natural functor} (BNF)---a
well-behaved type constructor for which nested (co)recursion is supported.

This tutorial is organized as follows:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item Section \ref{sec:defining-datatypes}, ``Defining Datatypes,''
describes how to specify datatypes using the @{command datatype} command.

\item Section \ref{sec:defining-recursive-functions}, ``Defining Recursive
Functions,'' describes how to specify recursive functions using
@{command primrec}.

\item Section \ref{sec:defining-codatatypes}, ``Defining Codatatypes,''
describes how to specify codatatypes using the @{command codatatype} command.

\item Section \ref{sec:defining-corecursive-functions}, ``Defining Corecursive
Functions,'' describes how to specify corecursive functions using the
@{command primcorec} and @{command primcorecursive} commands.

\item Section \ref{sec:introducing-bounded-natural-functors}, ``Introducing
Bounded Natural Functors,'' explains how to use the @{command bnf} command
to register arbitrary type constructors as BNFs.

\item Section
\ref{sec:deriving-destructors-and-theorems-for-free-constructors},
``Deriving Destructors and Theorems for Free Constructors,'' explains how to
use the command @{command free_constructors} to derive destructor constants
and theorems for freely generated types, as performed internally by
@{command datatype} and @{command codatatype}.

%\item Section \ref{sec:using-the-standard-ml-interface}, ``Using the Standard
ML Interface,'' %describes the package's programmatic interface.

\item Section \ref{sec:controlling-plugins}, ``Controlling Plugins,''
is concerned with the package's interoperability with other Isabelle packages
and tools, such as the code generator, Transfer, Lifting, and Quickcheck.

\item Section \ref{sec:known-bugs-and-limitations}, ``Known Bugs and
Limitations,'' concludes with known open issues at the time of writing.
\end{itemize}


\newbox\boxA
\setbox\boxA=\hbox{\texttt{NOSPAM}}

\newcommand\authoremaili{\texttt{blan{\color{white}NOSPAM}\kern-\wd\boxA{}chette@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailii{\texttt{desh{\color{white}NOSPAM}\kern-\wd\boxA{}arna@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailiii{\texttt{lore{\color{white}NOSPAM}\kern-\wd\boxA{}nz.panny@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailiv{\texttt{pope{\color{white}NOSPAM}\kern-\wd\boxA{}scua@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailv{\texttt{tray{\color{white}NOSPAM}\kern-\wd\boxA{}tel@\allowbreak
in.\allowbreak tum.\allowbreak de}}

Comments and bug reports concerning either the package or this tutorial should
be directed to the authors at \authoremaili, \authoremailii, \authoremailiii,
\authoremailiv, and \authoremailv.
*}


section {* Defining Datatypes
  \label{sec:defining-datatypes} *}

text {*
Datatypes can be specified using the @{command datatype} command.
*}


subsection {* Introductory Examples
  \label{ssec:datatype-introductory-examples} *}

text {*
Datatypes are illustrated through concrete examples featuring different flavors
of recursion. More examples can be found in the directory
\verb|~~/src/HOL/|\allowbreak\verb|BNF/Examples|.
*}


subsubsection {* Nonrecursive Types
  \label{sssec:datatype-nonrecursive-types} *}

text {*
Datatypes are introduced by specifying the desired names and argument types for
their constructors. \emph{Enumeration} types are the simplest form of datatype.
All their constructors are nullary:
*}

    datatype trool = Truue | Faalse | Perhaaps

text {*
\noindent
Here, @{const Truue}, @{const Faalse}, and @{const Perhaaps} have the type @{typ trool}.

Polymorphic types are possible, such as the following option type, modeled after
its homologue from the @{theory Option} theory:
*}

(*<*)
    hide_const None Some map_option
    hide_type option
(*>*)
    datatype 'a option = None | Some 'a

text {*
\noindent
The constructors are @{text "None :: 'a option"} and
@{text "Some :: 'a \<Rightarrow> 'a option"}.

The next example has three type parameters:
*}

    datatype ('a, 'b, 'c) triple = Triple 'a 'b 'c

text {*
\noindent
The constructor is
@{text "Triple :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> ('a, 'b, 'c) triple"}.
Unlike in Standard ML, curried constructors are supported. The uncurried variant
is also possible:
*}

    datatype ('a, 'b, 'c) triple\<^sub>u = Triple\<^sub>u "'a * 'b * 'c"

text {*
\noindent
Occurrences of nonatomic types on the right-hand side of the equal sign must be
enclosed in double quotes, as is customary in Isabelle.
*}


subsubsection {* Simple Recursion
  \label{sssec:datatype-simple-recursion} *}

text {*
Natural numbers are the simplest example of a recursive type:
*}

    datatype nat = Zero | Succ nat

text {*
\noindent
Lists were shown in the introduction. Terminated lists are a variant that
stores a value of type @{typ 'b} at the very end:
*}

    datatype (*<*)(in early) (*>*)('a, 'b) tlist = TNil 'b | TCons 'a "('a, 'b) tlist"


subsubsection {* Mutual Recursion
  \label{sssec:datatype-mutual-recursion} *}

text {*
\emph{Mutually recursive} types are introduced simultaneously and may refer to
each other. The example below introduces a pair of types for even and odd
natural numbers:
*}

    datatype even_nat = Even_Zero | Even_Succ odd_nat
    and odd_nat = Odd_Succ even_nat

text {*
\noindent
Arithmetic expressions are defined via terms, terms via factors, and factors via
expressions:
*}

    datatype ('a, 'b) exp =
      Term "('a, 'b) trm" | Sum "('a, 'b) trm" "('a, 'b) exp"
    and ('a, 'b) trm =
      Factor "('a, 'b) fct" | Prod "('a, 'b) fct" "('a, 'b) trm"
    and ('a, 'b) fct =
      Const 'a | Var 'b | Expr "('a, 'b) exp"


subsubsection {* Nested Recursion
  \label{sssec:datatype-nested-recursion} *}

text {*
\emph{Nested recursion} occurs when recursive occurrences of a type appear under
a type constructor. The introduction showed some examples of trees with nesting
through lists. A more complex example, that reuses our @{type option} type,
follows:
*}

    datatype 'a btree =
      BNode 'a "'a btree option" "'a btree option"

text {*
\noindent
Not all nestings are admissible. For example, this command will fail:
*}

    datatype 'a wrong = W1 | W2 (*<*)'a
    typ (*>*)"'a wrong \<Rightarrow> 'a"

text {*
\noindent
The issue is that the function arrow @{text "\<Rightarrow>"} allows recursion
only through its right-hand side. This issue is inherited by polymorphic
datatypes defined in terms of~@{text "\<Rightarrow>"}:
*}

    datatype ('a, 'b) fun_copy = Fun "'a \<Rightarrow> 'b"
    datatype 'a also_wrong = W1 | W2 (*<*)'a
    typ (*>*)"('a also_wrong, 'a) fun_copy"

text {*
\noindent
The following definition of @{typ 'a}-branching trees is legal:
*}

    datatype 'a ftree = FTLeaf 'a | FTNode "'a \<Rightarrow> 'a ftree"

text {*
\noindent
And so is the definition of hereditarily finite sets:
*}

    datatype hfset = HFSet "hfset fset"

text {*
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
Section~\ref{sec:introducing-bounded-natural-functors} explains how to
register arbitrary type constructors as BNFs.

Here is another example that fails:
*}

    datatype 'a pow_list = PNil 'a (*<*)'a
    datatype 'a pow_list' = PNil' 'a (*>*)| PCons "('a * 'a) pow_list"

text {*
\noindent
This attempted definition features a different flavor of nesting, where the
recursive call in the type specification occurs around (rather than inside)
another type constructor.
*}


subsubsection {* Auxiliary Constants and Properties
  \label{sssec:datatype-auxiliary-constants-and-properties} *}

text {*
The @{command datatype} command introduces various constants in addition to
the constructors. With each datatype are associated set functions, a map
function, a relator, discriminators, and selectors, all of which can be given
custom names. In the example below, the familiar names @{text null}, @{text hd},
@{text tl}, @{text set}, @{text map}, and @{text list_all2}, override the
default names @{text is_Nil}, @{text un_Cons1}, @{text un_Cons2},
@{text set_list}, @{text map_list}, and @{text rel_list}:
*}

(*<*)
    no_translations
      "[x, xs]" == "x # [xs]"
      "[x]" == "x # []"

    no_notation
      Nil ("[]") and
      Cons (infixr "#" 65)

    hide_type list
    hide_const Nil Cons case_list hd tl set map list_all2 rec_list size_list pred_list

    context early begin
(*>*)
    datatype (set: 'a) list =
      null: Nil
    | Cons (hd: 'a) (tl: "'a list")
    for
      map: map
      rel: list_all2
    where
      "tl Nil = Nil"

text {*
\noindent
The types of the constants that appear in the specification are listed below.

\medskip

\begin{tabular}{@ {}ll@ {}}
Constructors: &
  @{text "Nil \<Colon> 'a list"} \\
&
  @{text "Cons \<Colon> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"} \\
Discriminator: &
  @{text "null \<Colon> 'a list \<Rightarrow> bool"} \\
Selectors: &
  @{text "hd \<Colon> 'a list \<Rightarrow> 'a"} \\
&
  @{text "tl \<Colon> 'a list \<Rightarrow> 'a list"} \\
Set function: &
  @{text "set \<Colon> 'a list \<Rightarrow> 'a set"} \\
Map function: &
  @{text "map \<Colon> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"} \\
Relator: &
  @{text "list_all2 \<Colon> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"}
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
Here, it is used to ensure that the tail of the empty list is itself (instead of
being left unspecified).

Because @{const Nil} is nullary, it is also possible to use
@{term "\<lambda>xs. xs = Nil"} as a discriminator. This is the default behavior
if we omit the identifier @{const null} and the associated colon. Some users
argue against this, because the mixture of constructors and selectors in the
characteristic theorems can lead Isabelle's automation to switch between the
constructor and the destructor view in surprising ways.

The usual mixfix syntax annotations are available for both types and
constructors. For example:
*}

(*<*)
    end
(*>*)
    datatype ('a, 'b) prod (infixr "*" 20) = Pair 'a 'b

text {* \blankline *}

    datatype (set: 'a) list =
      null: Nil ("[]")
    | Cons (hd: 'a) (tl: "'a list") (infixr "#" 65)
    for
      map: map
      rel: list_all2

text {*
\noindent
Incidentally, this is how the traditional syntax can be set up:
*}

    syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]")

text {* \blankline *}

    translations
      "[x, xs]" == "x # [xs]"
      "[x]" == "x # []"


subsection {* Command Syntax
  \label{ssec:datatype-command-syntax} *}

subsubsection {* \keyw{datatype}
  \label{sssec:datatype-new} *}

text {*
\begin{matharray}{rcl}
  @{command_def "datatype"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command datatype} target? @{syntax dt_options}? \<newline>
    (@{syntax dt_name} '=' (@{syntax dt_ctor} + '|') \<newline>
     @{syntax map_rel}? (@'where' (prop + '|'))? + @'and')
  ;
  @{syntax_def plugins}: 'plugins' ('only' | 'del') ':' (name +)
  ;
  @{syntax_def dt_options}: '(' ((@{syntax plugins} | 'discs_sels') + ',') ')'
  ;
  @{syntax_def map_rel}: @'for' ((('map' | 'rel') ':' name) +)
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
The @{text "plugins"} option indicates which plugins should be enabled
(@{text only}) or disabled (@{text del}). Some plugin names are defined
as indirection to a group of sub-plugins (notably @{text "quickcheck"}
based on @{text quickcheck_random}, @{text quickcheck_exhaustive}, \dots).
By default, all plugins are enabled.

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
can be supplied at the front to override the default, which is
@{text "\<lambda>x. x = C\<^sub>j"} for nullary constructors and
@{text t.is_C\<^sub>j} otherwise.

@{rail \<open>
  @{syntax_def dt_ctor_arg}: type | '(' name ':' type ')'
\<close>}

\medskip

\noindent
The syntactic entity \synt{type} denotes a HOL type @{cite "isabelle-isar-ref"}.

In addition to the type of a constructor argument, it is possible to specify a
name for the corresponding selector to override the default name
(@{text un_C\<^sub>ji}). The same selector names can be reused for several
constructors as long as they share the same type.
*}


subsubsection {* \keyw{datatype_compat}
  \label{sssec:datatype-compat} *}

text {*
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
*}

    datatype_compat even_nat odd_nat

text {* \blankline *}

    ML {* Old_Datatype_Data.get_info @{theory} @{type_name even_nat} *}

text {*
The syntactic entity \synt{name} denotes an identifier @{cite "isabelle-isar-ref"}.

The command can be useful because the old datatype package provides some
functionality that is not yet replicated in the new package.

A few remarks concern nested recursive datatypes:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The old-style, nested-as-mutual induction rule and recursor theorems are
generated under their usual names but with ``@{text "compat_"}'' prefixed
(e.g., @{text compat_tree.induct}, @{text compat_tree.inducts}, and
@{text compat_tree.rec}).

\item All types through which recursion takes place must be new-style datatypes
or the function type. In principle, it should be possible to support old-style
datatypes as well, but this has not been implemented yet (and there is currently
no way to register old-style datatypes as new-style datatypes).
\end{itemize}
*}


subsection {* Generated Constants
  \label{ssec:datatype-generated-constants} *}

text {*
Given a datatype @{text "('a\<^sub>1, \<dots>, 'a\<^sub>m) t"}
with $m > 0$ live type variables and $n$ constructors
@{text "t.C\<^sub>1"}, \ldots, @{text "t.C\<^sub>n"}, the
following auxiliary constants are introduced:

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
In addition, some of the plugins introduce their own constants
(Section~\ref{sec:controlling-plugins}). The case combinator, discriminators,
and selectors are collectively called \emph{destructors}. The prefix
``@{text "t."}'' is an optional component of the names and is normally hidden.
*}


subsection {* Generated Theorems
  \label{ssec:datatype-generated-theorems} *}

text {*
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
The full list of named theorems can be obtained as usual by entering the
command \keyw{print_theorems} immediately after the datatype definition.
This list includes theorems produced by plugins
(Section~\ref{sec:controlling-plugins}), but normally excludes low-level
theorems that reveal internal constructions. To make these accessible, add
the line
*}

    declare [[bnf_note_all]]
(*<*)
    declare [[bnf_note_all = false]]
(*>*)

text {*
\noindent
to the top of the theory file.
*}


subsubsection {* Free Constructor Theorems
  \label{sssec:free-constructor-theorems} *}

(*<*)
    consts nonnull :: 'a
(*>*)

text {*
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
(The @{text "[code]"} attribute is set by the @{text code} plugin,
Section~\ref{ssec:code-generator}.)

\item[@{text "t."}\hthm{case_cong} @{text "[fundef_cong]"}\rm:] ~ \\
@{thm list.case_cong[no_vars]}

\item[@{text "t."}\hthm{case_cong_weak} @{text "[cong]"}\rm:] ~ \\
@{thm list.case_cong_weak[no_vars]}

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
(The @{text "[code]"} attribute is set by the @{text code} plugin,
Section~\ref{ssec:code-generator}.)

\item[@{text "t."}\hthm{collapse} @{text "[simp]"}\rm:] ~ \\
@{thm list.collapse(1)[no_vars]} \\
@{thm list.collapse(2)[no_vars]} \\
(The @{text "[simp]"} attribute is exceptionally omitted for datatypes equipped
with a single nullary constructor, because a property of the form
@{prop "x = C"} is not suitable as a simplification rule.)

\item[@{text "t."}\hthm{distinct_disc} @{text "[dest]"}\rm:] ~ \\
These properties are missing for @{typ "'a list"} because there is only one
proper discriminator. Had the datatype been introduced with a second
discriminator called @{const nonnull}, they would have read thusly: \\[\jot]
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

\end{description}
\end{indentblock}

\noindent
In addition, equational versions of @{text t.disc} are registered with the
@{text "[code]"} attribute. (The @{text "[code]"} attribute is set by the
@{text code} plugin, Section~\ref{ssec:code-generator}.)
*}


subsubsection {* Functorial Theorems
  \label{sssec:functorial-theorems} *}

text {*
The functorial theorems are partitioned in two subgroups. The first subgroup
consists of properties involving the constructors or the destructors and either
a set function, the map function, or the relator:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{case_transfer}\rm:] ~ \\
@{thm list.case_transfer[no_vars]}

\item[@{text "t."}\hthm{sel_transfer}\rm:] ~ \\
This property is missing for @{typ "'a list"} because there is no common
selector to all constructors.

\item[@{text "t."}\hthm{ctr_transfer}\rm:] ~ \\
@{thm list.ctr_transfer(1)[no_vars]} \\
@{thm list.ctr_transfer(2)[no_vars]}

\item[@{text "t."}\hthm{disc_transfer}\rm:] ~ \\
@{thm list.disc_transfer(1)[no_vars]} \\
@{thm list.disc_transfer(2)[no_vars]}

\item[@{text "t."}\hthm{set} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.set(1)[no_vars]} \\
@{thm list.set(2)[no_vars]} \\
(The @{text "[code]"} attribute is set by the @{text code} plugin,
Section~\ref{ssec:code-generator}.)

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
(The @{text "[code]"} attribute is set by the @{text code} plugin,
Section~\ref{ssec:code-generator}.)

\item[@{text "t."}\hthm{map_disc_iff} @{text "[simp]"}\rm:] ~ \\
@{thm list.map_disc_iff[no_vars]}

\item[@{text "t."}\hthm{map_sel}\rm:] ~ \\
@{thm list.map_sel[no_vars]}

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
rel_distinct} are registered with the @{text "[code]"} attribute. (The
@{text "[code]"} attribute is set by the @{text code} plugin,
Section~\ref{ssec:code-generator}.)

The second subgroup consists of more abstract properties of the set functions,
the map function, and the relator:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{inj_map}\rm:] ~ \\
@{thm list.inj_map[no_vars]}

\item[@{text "t."}\hthm{inj_map_strong}\rm:] ~ \\
@{thm list.inj_map_strong[no_vars]}

\item[@{text "t."}\hthm{set_map}\rm:] ~ \\
@{thm list.set_map[no_vars]}

\item[@{text "t."}\hthm{set_transfer}\rm:] ~ \\
@{thm list.set_transfer[no_vars]}

\item[@{text "t."}\hthm{map_cong0}\rm:] ~ \\
@{thm list.map_cong0[no_vars]}

\item[@{text "t."}\hthm{map_cong} @{text "[fundef_cong]"}\rm:] ~ \\
@{thm list.map_cong[no_vars]}

\item[@{text "t."}\hthm{map_cong_simp}\rm:] ~ \\
@{thm list.map_cong_simp[no_vars]}

\item[@{text "t."}\hthm{map_id}\rm:] ~ \\
@{thm list.map_id[no_vars]}

\item[@{text "t."}\hthm{map_id0}\rm:] ~ \\
@{thm list.map_id0[no_vars]}

\item[@{text "t."}\hthm{map_ident}\rm:] ~ \\
@{thm list.map_ident[no_vars]}

\item[@{text "t."}\hthm{map_transfer}\rm:] ~ \\
@{thm list.map_transfer[no_vars]}

\item[@{text "t."}\hthm{rel_compp} @{text "[relator_distr]"}\rm:] ~ \\
@{thm list.rel_compp[no_vars]} \\
(The @{text "[relator_distr]"} attribute is set by the @{text lifting} plugin,
Section~\ref{ssec:lifting}.)

\item[@{text "t."}\hthm{rel_conversep}\rm:] ~ \\
@{thm list.rel_conversep[no_vars]}

\item[@{text "t."}\hthm{rel_eq}\rm:] ~ \\
@{thm list.rel_eq[no_vars]}

\item[@{text "t."}\hthm{rel_flip}\rm:] ~ \\
@{thm list.rel_flip[no_vars]}

\item[@{text "t."}\hthm{rel_map}\rm:] ~ \\
@{thm list.rel_map(1)[no_vars]} \\
@{thm list.rel_map(2)[no_vars]}

\item[@{text "t."}\hthm{rel_mono} @{text "[mono, relator_mono]"}\rm:] ~ \\
@{thm list.rel_mono[no_vars]} \\
(The @{text "[relator_mono]"} attribute is set by the @{text lifting} plugin,
Section~\ref{ssec:lifting}.)

\item[@{text "t."}\hthm{rel_transfer}\rm:] ~ \\
@{thm list.rel_transfer[no_vars]}

\end{description}
\end{indentblock}
*}


subsubsection {* Inductive Theorems
  \label{sssec:inductive-theorems} *}

text {*
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
(The @{text "[code]"} attribute is set by the @{text code} plugin,
Section~\ref{ssec:code-generator}.)

\item[@{text "t."}\hthm{rec_o_map}\rm:] ~ \\
@{thm list.rec_o_map[no_vars]}

\item[@{text "t."}\hthm{rec_transfer}\rm:] ~ \\
@{thm list.rec_transfer[no_vars]}

\end{description}
\end{indentblock}

\noindent
For convenience, @{command datatype} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{simps} = @{text t.inject} @{text t.distinct} @{text t.case} @{text t.rec} @{text t.map} @{text t.rel_inject}] ~ \\
@{text t.rel_distinct} @{text t.set}

\end{description}
\end{indentblock}
*}


subsection {* Compatibility Issues
  \label{ssec:datatype-compatibility-issues} *}

text {*
The command @{command datatype} has been designed to be highly compatible
with the old command (which is now called \keyw{old_datatype}), to ease
migration. There are nonetheless a few incompatibilities that may arise when
porting:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{The Standard ML interfaces are different.} Tools and extensions
written to call the old ML interfaces will need to be adapted to the new
interfaces. If possible, it is recommended to register new-style datatypes as
old-style datatypes using the @{command datatype_compat} command.

\item \emph{The recursor @{text rec_t} has a different signature for nested
recursive datatypes.} In the old package, nested recursion through non-functions
was internally reduced to mutual recursion. This reduction was visible in the
type of the recursor, used by \keyw{primrec}. Recursion through functions was
handled specially. In the new package, nested recursion (for functions and
non-functions) is handled in a more modular fashion. The old-style recursor can
be generated on demand using @{command primrec} if the recursion is via
new-style datatypes, as explained in
Section~\ref{sssec:primrec-nested-as-mutual-recursion}.

\item \emph{Accordingly, the induction rule is different for nested recursive
datatypes.} Again, the old-style induction rule can be generated on demand using
@{command primrec} if the recursion is via new-style datatypes, as explained in
Section~\ref{sssec:primrec-nested-as-mutual-recursion}. For recursion through
functions, the old-style induction rule can be obtained by applying the
@{text "[unfolded all_mem_range]"} attribute on @{text t.induct}.

\item \emph{The @{const size} function has a slightly different definition.}
The new function returns @{text 1} instead of @{text 0} for some nonrecursive
constructors. This departure from the old behavior made it possible to implement
@{const size} in terms of the generic function @{text "t.size_t"}.
Moreover, the new function considers nested occurrences of a value, in the nested
recursive case. The old behavior can be obtained by disabling the @{text size}
plugin (Section~\ref{sec:controlling-plugins}) and instantiating the
@{text size} type class manually.

\item \emph{The internal constructions are completely different.} Proof texts
that unfold the definition of constants introduced by \keyw{old_datatype} will
be difficult to port.

\item \emph{Some constants and theorems have different names.}
For non-mutually recursive datatypes,
the alias @{text t.inducts} for @{text t.induct} is no longer generated.
For $m > 1$ mutually recursive datatypes,
@{text "rec_t\<^sub>1_\<dots>_t\<^sub>m_i"} has been renamed
@{text "rec_t\<^sub>i"} for each @{text "i \<in> {1, \<dots>, t}"},
@{text "t\<^sub>1_\<dots>_t\<^sub>m.inducts(i)"} has been renamed
@{text "t\<^sub>i.induct"} for each @{text "i \<in> {1, \<dots>, t}"}, and the
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

In the other direction, there is currently no way to register old-style
datatypes as new-style datatypes. If the goal is to define new-style datatypes
with nested recursion through old-style datatypes, the old-style
datatypes can be registered as a BNF
(Section~\ref{sec:introducing-bounded-natural-functors}). If the goal is
to derive discriminators and selectors, this can be achieved using
@{command free_constructors}
(Section~\ref{sec:deriving-destructors-and-theorems-for-free-constructors}).
*}


section {* Defining Recursive Functions
  \label{sec:defining-recursive-functions} *}

text {*
Recursive functions over datatypes can be specified using the @{command primrec}
command, which supports primitive recursion, or using the more general
\keyw{fun} and \keyw{function} commands. Here, the focus is on
@{command primrec}; the other two commands are described in a separate
tutorial @{cite "isabelle-function"}.

%%% TODO: partial_function
*}


subsection {* Introductory Examples
  \label{ssec:primrec-introductory-examples} *}

text {*
Primitive recursion is illustrated through concrete examples based on the
datatypes defined in Section~\ref{ssec:datatype-introductory-examples}. More
examples can be found in the directory \verb|~~/src/HOL/Datatype_Examples|.
*}


subsubsection {* Nonrecursive Types
  \label{sssec:primrec-nonrecursive-types} *}

text {*
Primitive recursion removes one layer of constructors on the left-hand side in
each equation. For example:
*}

    primrec bool_of_trool :: "trool \<Rightarrow> bool" where
      "bool_of_trool Faalse \<longleftrightarrow> False" |
      "bool_of_trool Truue \<longleftrightarrow> True"

text {* \blankline *}

    primrec the_list :: "'a option \<Rightarrow> 'a list" where
      "the_list None = []" |
      "the_list (Some a) = [a]"

text {* \blankline *}

    primrec the_default :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
      "the_default d None = d" |
      "the_default _ (Some a) = a"

text {* \blankline *}

    primrec mirrror :: "('a, 'b, 'c) triple \<Rightarrow> ('c, 'b, 'a) triple" where
      "mirrror (Triple a b c) = Triple c b a"

text {*
\noindent
The equations can be specified in any order, and it is acceptable to leave out
some cases, which are then unspecified. Pattern matching on the left-hand side
is restricted to a single datatype, which must correspond to the same argument
in all equations.
*}


subsubsection {* Simple Recursion
  \label{sssec:primrec-simple-recursion} *}

text {*
For simple recursive types, recursive calls on a constructor argument are
allowed on the right-hand side:
*}

    primrec replicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
      "replicate Zero _ = []" |
      "replicate (Succ n) x = x # replicate n x"

text {* \blankline *}

    primrec at :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
      "at (x # xs) j =
         (case j of
            Zero \<Rightarrow> x
          | Succ j' \<Rightarrow> at xs j')"

text {* \blankline *}

    primrec (*<*)(in early) (*>*)tfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) tlist \<Rightarrow> 'b" where
      "tfold _ (TNil y) = y" |
      "tfold f (TCons x xs) = f x (tfold f xs)"

text {*
\noindent
Pattern matching is only available for the argument on which the recursion takes
place. Fortunately, it is easy to generate pattern-maching equations using the
\keyw{simps_of_case} command provided by the theory
\verb|~~/src/HOL/|\allowbreak\verb|Library/|\allowbreak\verb|Simps_Case_Conv|.
*}

    simps_of_case at_simps: at.simps

text {*
This generates the lemma collection @{thm [source] at_simps}:
%
\[@{thm at_simps(1)[no_vars]}
  \qquad @{thm at_simps(2)[no_vars]}\]
%
The next example is defined using \keyw{fun} to escape the syntactic
restrictions imposed on primitively recursive functions. The
@{command datatype_compat} command is needed to register new-style datatypes
for use with \keyw{fun} and \keyw{function}
(Section~\ref{sssec:datatype-compat}):
*}

    datatype_compat nat

text {* \blankline *}

    fun at_least_two :: "nat \<Rightarrow> bool" where
      "at_least_two (Succ (Succ _)) \<longleftrightarrow> True" |
      "at_least_two _ \<longleftrightarrow> False"


subsubsection {* Mutual Recursion
  \label{sssec:primrec-mutual-recursion} *}

text {*
The syntax for mutually recursive functions over mutually recursive datatypes
is straightforward:
*}

    primrec
      nat_of_even_nat :: "even_nat \<Rightarrow> nat" and
      nat_of_odd_nat :: "odd_nat \<Rightarrow> nat"
    where
      "nat_of_even_nat Even_Zero = Zero" |
      "nat_of_even_nat (Even_Succ n) = Succ (nat_of_odd_nat n)" |
      "nat_of_odd_nat (Odd_Succ n) = Succ (nat_of_even_nat n)"

text {* \blankline *}

    primrec
      eval\<^sub>e :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) exp \<Rightarrow> int" and
      eval\<^sub>t :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) trm \<Rightarrow> int" and
      eval\<^sub>f :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) fct \<Rightarrow> int"
    where
      "eval\<^sub>e \<gamma> \<xi> (Term t) = eval\<^sub>t \<gamma> \<xi> t" |
      "eval\<^sub>e \<gamma> \<xi> (Sum t e) = eval\<^sub>t \<gamma> \<xi> t + eval\<^sub>e \<gamma> \<xi> e" |
      "eval\<^sub>t \<gamma> \<xi> (Factor f) = eval\<^sub>f \<gamma> \<xi> f" |
      "eval\<^sub>t \<gamma> \<xi> (Prod f t) = eval\<^sub>f \<gamma> \<xi> f + eval\<^sub>t \<gamma> \<xi> t" |
      "eval\<^sub>f \<gamma> _ (Const a) = \<gamma> a" |
      "eval\<^sub>f _ \<xi> (Var b) = \<xi> b" |
      "eval\<^sub>f \<gamma> \<xi> (Expr e) = eval\<^sub>e \<gamma> \<xi> e"

text {*
\noindent
Mutual recursion is possible within a single type, using \keyw{fun}:
*}

    fun
      even :: "nat \<Rightarrow> bool" and
      odd :: "nat \<Rightarrow> bool"
    where
      "even Zero = True" |
      "even (Succ n) = odd n" |
      "odd Zero = False" |
      "odd (Succ n) = even n"


subsubsection {* Nested Recursion
  \label{sssec:primrec-nested-recursion} *}

text {*
In a departure from the old datatype package, nested recursion is normally
handled via the map functions of the nesting type constructors. For example,
recursive calls are lifted to lists using @{const map}:
*}

(*<*)
    datatype 'a tree\<^sub>f\<^sub>f = Node\<^sub>f\<^sub>f (lbl\<^sub>f\<^sub>f: 'a) (sub\<^sub>f\<^sub>f: "'a tree\<^sub>f\<^sub>f list")
(*>*)
    primrec at\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f \<Rightarrow> nat list \<Rightarrow> 'a" where
      "at\<^sub>f\<^sub>f (Node\<^sub>f\<^sub>f a ts) js =
         (case js of
            [] \<Rightarrow> a
          | j # js' \<Rightarrow> at (map (\<lambda>t. at\<^sub>f\<^sub>f t js') ts) j)"

text {*
\noindent
The next example features recursion through the @{text option} type. Although
@{text option} is not a new-style datatype, it is registered as a BNF with the
map function @{const map_option}:
*}

    primrec (*<*)(in early) (*>*)sum_btree :: "('a\<Colon>{zero,plus}) btree \<Rightarrow> 'a" where
      "sum_btree (BNode a lt rt) =
         a + the_default 0 (map_option sum_btree lt) +
           the_default 0 (map_option sum_btree rt)"

text {*
\noindent
The same principle applies for arbitrary type constructors through which
recursion is possible. Notably, the map function for the function type
(@{text \<Rightarrow>}) is simply composition (@{text "op \<circ>"}):
*}

    primrec (*<*)(in early) (*>*)relabel_ft :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
      "relabel_ft f (FTLeaf x) = FTLeaf (f x)" |
      "relabel_ft f (FTNode g) = FTNode (relabel_ft f \<circ> g)"

text {*
\noindent
For convenience, recursion through functions can also be expressed using
$\lambda$-abstractions and function application rather than through composition.
For example:
*}

    primrec relabel_ft :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
      "relabel_ft f (FTLeaf x) = FTLeaf (f x)" |
      "relabel_ft f (FTNode g) = FTNode (\<lambda>x. relabel_ft f (g x))"

text {* \blankline *}

    primrec subtree_ft :: "'a \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
      "subtree_ft x (FTNode g) = g x"

text {*
\noindent
For recursion through curried $n$-ary functions, $n$ applications of
@{term "op \<circ>"} are necessary. The examples below illustrate the case where
$n = 2$:
*}

    datatype 'a ftree2 = FTLeaf2 'a | FTNode2 "'a \<Rightarrow> 'a \<Rightarrow> 'a ftree2"

text {* \blankline *}

    primrec (*<*)(in early) (*>*)relabel_ft2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree2 \<Rightarrow> 'a ftree2" where
      "relabel_ft2 f (FTLeaf2 x) = FTLeaf2 (f x)" |
      "relabel_ft2 f (FTNode2 g) = FTNode2 (op \<circ> (op \<circ> (relabel_ft2 f)) g)"

text {* \blankline *}

    primrec relabel_ft2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree2 \<Rightarrow> 'a ftree2" where
      "relabel_ft2 f (FTLeaf2 x) = FTLeaf2 (f x)" |
      "relabel_ft2 f (FTNode2 g) = FTNode2 (\<lambda>x y. relabel_ft2 f (g x y))"

text {* \blankline *}

    primrec subtree_ft2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a ftree2 \<Rightarrow> 'a ftree2" where
      "subtree_ft2 x y (FTNode2 g) = g x y"


subsubsection {* Nested-as-Mutual Recursion
  \label{sssec:primrec-nested-as-mutual-recursion} *}

(*<*)
    locale n2m begin
(*>*)

text {*
For compatibility with the old package, but also because it is sometimes
convenient in its own right, it is possible to treat nested recursive datatypes
as mutually recursive ones if the recursion takes place though new-style
datatypes. For example:
*}

    primrec
      at\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f \<Rightarrow> nat list \<Rightarrow> 'a" and
      ats\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a"
    where
      "at\<^sub>f\<^sub>f (Node\<^sub>f\<^sub>f a ts) js =
         (case js of
            [] \<Rightarrow> a
          | j # js' \<Rightarrow> ats\<^sub>f\<^sub>f ts j js')" |
      "ats\<^sub>f\<^sub>f (t # ts) j =
         (case j of
            Zero \<Rightarrow> at\<^sub>f\<^sub>f t
          | Succ j' \<Rightarrow> ats\<^sub>f\<^sub>f ts j')"

text {*
\noindent
Appropriate induction rules are generated as
@{thm [source] at\<^sub>f\<^sub>f.induct},
@{thm [source] ats\<^sub>f\<^sub>f.induct}, and
@{thm [source] at\<^sub>f\<^sub>f_ats\<^sub>f\<^sub>f.induct}. The
induction rules and the underlying recursors are generated on a per-need basis
and are kept in a cache to speed up subsequent definitions.

Here is a second example:
*}

    primrec
      sum_btree :: "('a\<Colon>{zero,plus}) btree \<Rightarrow> 'a" and
      sum_btree_option :: "'a btree option \<Rightarrow> 'a"
    where
      "sum_btree (BNode a lt rt) =
         a + sum_btree_option lt + sum_btree_option rt" |
      "sum_btree_option None = 0" |
      "sum_btree_option (Some t) = sum_btree t"

text {*
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
*}
(*<*)
    end
(*>*)


subsection {* Command Syntax
  \label{ssec:primrec-command-syntax} *}

subsubsection {* \keyw{primrec}
  \label{sssec:primrec-new} *}

text {*
\begin{matharray}{rcl}
  @{command_def "primrec"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command primrec} target? @{syntax pr_option}? fixes \<newline>
  @'where' (@{syntax pr_equation} + '|')
  ;
  @{syntax_def pr_option}: '(' 'nonexhaustive' ')'
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

The optional target is optionally followed by the following option:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text "nonexhaustive"} option indicates that the functions are not
necessarily specified for all constructors. It can be used to suppress the
warning that is normally emitted when some constructors are missing.
\end{itemize}

%%% TODO: elaborate on format of the equations
%%% TODO: elaborate on mutual and nested-to-mutual
*}


(*
subsection {* Generated Theorems
  \label{ssec:primrec-generated-theorems} *}

text {*
%  * synthesized nonrecursive definition
%  * user specification is rederived from it, exactly as entered
%
%  * induct
%    * mutualized
%    * without some needless induction hypotheses if not used
%  * rec
%    * mutualized
*}
*)


subsection {* Recursive Default Values for Selectors
  \label{ssec:primrec-recursive-default-values-for-selectors} *}

text {*
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
Introduce a fully unspecified constant @{text "un_D\<^sub>0 \<Colon> 'a"} using
@{keyword consts}.

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
*}

(*<*)
    hide_const termi
(*>*)
    consts termi\<^sub>0 :: 'a

text {* \blankline *}

    datatype ('a, 'b) tlist =
      TNil (termi: 'b)
    | TCons (thd: 'a) (ttl: "('a, 'b) tlist")
    where
      "ttl (TNil y) = TNil y"
    | "termi (TCons _ xs) = termi\<^sub>0 xs"

text {* \blankline *}

    overloading
      termi\<^sub>0 \<equiv> "termi\<^sub>0 \<Colon> ('a, 'b) tlist \<Rightarrow> 'b"
    begin
    primrec termi\<^sub>0 :: "('a, 'b) tlist \<Rightarrow> 'b" where
      "termi\<^sub>0 (TNil y) = y" |
      "termi\<^sub>0 (TCons x xs) = termi\<^sub>0 xs"
    end

text {* \blankline *}

    lemma termi_TCons[simp]: "termi (TCons x xs) = termi xs"
    by (cases xs) auto


subsection {* Compatibility Issues
  \label{ssec:primrec-compatibility-issues} *}

text {*
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
*}


section {* Defining Codatatypes
  \label{sec:defining-codatatypes} *}

text {*
Codatatypes can be specified using the @{command codatatype} command. The
command is first illustrated through concrete examples featuring different
flavors of corecursion. More examples can be found in the directory
\verb|~~/src/HOL/|\allowbreak\verb|BNF/Examples|. The
\emph{Archive of Formal Proofs} also includes some useful codatatypes, notably
for lazy lists @{cite "lochbihler-2010"}.
*}


subsection {* Introductory Examples
  \label{ssec:codatatype-introductory-examples} *}

subsubsection {* Simple Corecursion
  \label{sssec:codatatype-simple-corecursion} *}

text {*
Non-corecursive codatatypes coincide with the corresponding datatypes, so they
are rarely used in practice. \emph{Corecursive codatatypes} have the same syntax
as recursive datatypes, except for the command name. For example, here is the
definition of lazy lists:
*}

    codatatype (lset: 'a) llist =
      lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a llist")
    for
      map: lmap
      rel: llist_all2
    where
      "ltl LNil = LNil"

text {*
\noindent
Lazy lists can be infinite, such as @{text "LCons 0 (LCons 0 (\<dots>))"} and
@{text "LCons 0 (LCons 1 (LCons 2 (\<dots>)))"}. Here is a related type, that of
infinite streams:
*}

    codatatype (sset: 'a) stream =
      SCons (shd: 'a) (stl: "'a stream")
    for
      map: smap
      rel: stream_all2

text {*
\noindent
Another interesting type that can
be defined as a codatatype is that of the extended natural numbers:
*}

    codatatype enat = EZero | ESucc enat

text {*
\noindent
This type has exactly one infinite element, @{text "ESucc (ESucc (ESucc (\<dots>)))"},
that represents $\infty$. In addition, it has finite values of the form
@{text "ESucc (\<dots> (ESucc EZero)\<dots>)"}.

Here is an example with many constructors:
*}

    codatatype 'a process =
      Fail
    | Skip (cont: "'a process")
    | Action (prefix: 'a) (cont: "'a process")
    | Choice (left: "'a process") (right: "'a process")

text {*
\noindent
Notice that the @{const cont} selector is associated with both @{const Skip}
and @{const Action}.
*}


subsubsection {* Mutual Corecursion
  \label{sssec:codatatype-mutual-corecursion} *}

text {*
\noindent
The example below introduces a pair of \emph{mutually corecursive} types:
*}

    codatatype even_enat = Even_EZero | Even_ESucc odd_enat
    and odd_enat = Odd_ESucc even_enat


subsubsection {* Nested Corecursion
  \label{sssec:codatatype-nested-corecursion} *}

text {*
\noindent
The next examples feature \emph{nested corecursion}:
*}

    codatatype 'a tree\<^sub>i\<^sub>i = Node\<^sub>i\<^sub>i (lbl\<^sub>i\<^sub>i: 'a) (sub\<^sub>i\<^sub>i: "'a tree\<^sub>i\<^sub>i llist")

text {* \blankline *}

    codatatype 'a tree\<^sub>i\<^sub>s = Node\<^sub>i\<^sub>s (lbl\<^sub>i\<^sub>s: 'a) (sub\<^sub>i\<^sub>s: "'a tree\<^sub>i\<^sub>s fset")

text {* \blankline *}

    codatatype 'a sm = SM (accept: bool) (trans: "'a \<Rightarrow> 'a sm")


subsection {* Command Syntax
  \label{ssec:codatatype-command-syntax} *}

subsubsection {* \keyw{codatatype}
  \label{sssec:codatatype} *}

text {*
\begin{matharray}{rcl}
  @{command_def "codatatype"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command codatatype} target? \<newline>
    (@{syntax dt_name} '=' (@{syntax dt_ctor} + '|') + @'and')
\<close>}

\medskip

\noindent
Definitions of codatatypes have almost exactly the same syntax as for datatypes
(Section~\ref{ssec:datatype-command-syntax}). The @{text "discs_sels"} option
is superfluous because discriminators and selectors are always generated for
codatatypes.
*}


subsection {* Generated Constants
  \label{ssec:codatatype-generated-constants} *}

text {*
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
*}


subsection {* Generated Theorems
  \label{ssec:codatatype-generated-theorems} *}

text {*
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
*}


subsubsection {* Coinductive Theorems
  \label{sssec:coinductive-theorems} *}

text {*
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
(The @{text "[code]"} attribute is set by the @{text code} plugin,
Section~\ref{ssec:code-generator}.)

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

\item[@{text "t."}\hthm{corec_transfer}\rm:] ~ \\
@{thm llist.corec_transfer[no_vars]}

\end{description}
\end{indentblock}

\noindent
For convenience, @{command codatatype} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{simps} = @{text t.inject} @{text t.distinct} @{text t.case} @{text t.corec_disc_iff}] @{text t.corec_sel} ~ \\
@{text t.map} @{text t.rel_inject} @{text t.rel_distinct} @{text t.set}

\end{description}
\end{indentblock}
*}


section {* Defining Corecursive Functions
  \label{sec:defining-corecursive-functions} *}

text {*
Corecursive functions can be specified using the @{command primcorec} and
\keyw{prim\-corec\-ursive} commands, which support primitive corecursion, or
using the more general \keyw{partial_function} command. Here, the focus is on
the first two. More examples can be found in the directory
\verb|~~/src/HOL/Datatype_Examples|.

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
*}


subsection {* Introductory Examples
  \label{ssec:primcorec-introductory-examples} *}

text {*
Primitive corecursion is illustrated through concrete examples based on the
codatatypes defined in Section~\ref{ssec:codatatype-introductory-examples}. More
examples can be found in the directory \verb|~~/src/HOL/Datatype_Examples|. The
code view is favored in the examples below. Sections
\ref{ssec:primrec-constructor-view} and \ref{ssec:primrec-destructor-view}
present the same examples expressed using the constructor and destructor views.
*}


subsubsection {* Simple Corecursion
  \label{sssec:primcorec-simple-corecursion} *}

text {*
Following the code view, corecursive calls are allowed on the right-hand side as
long as they occur under a constructor, which itself appears either directly to
the right of the equal sign or in a conditional expression:
*}

    primcorec literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" where
      "literate g x = LCons x (literate g (g x))"

text {* \blankline *}

    primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      "siterate g x = SCons x (siterate g (g x))"

text {*
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
*}

    primcorec every_snd :: "'a stream \<Rightarrow> 'a stream" where
      "every_snd s = SCons (shd s) (stl (stl s))"

text {*
\noindent
Constructs such as @{text "let"}--@{text "in"}, @{text
"if"}--@{text "then"}--@{text "else"}, and @{text "case"}--@{text "of"} may
appear around constructors that guard corecursive calls:
*}

    primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lappend xs ys =
         (case xs of
            LNil \<Rightarrow> ys
          | LCons x xs' \<Rightarrow> LCons x (lappend xs' ys))"

text {*
\noindent
Pattern matching is not supported by @{command primcorec}. Fortunately, it is
easy to generate pattern-maching equations using the \keyw{simps_of_case}
command provided by the theory \verb|~~/src/HOL/Library/Simps_Case_Conv|.
*}

    simps_of_case lappend_simps: lappend.code

text {*
This generates the lemma collection @{thm [source] lappend_simps}:
%
\begin{gather*%
}
  @{thm lappend_simps(1)[no_vars]} \\
  @{thm lappend_simps(2)[no_vars]}
\end{gather*%
}
%
Corecursion is useful to specify not only functions but also infinite objects:
*}

    primcorec infty :: enat where
      "infty = ESucc infty"

text {*
\noindent
The example below constructs a pseudorandom process value. It takes a stream of
actions (@{text s}), a pseudorandom function generator (@{text f}), and a
pseudorandom seed (@{text n}):
*}

    primcorec(*<*) (in early)(*>*)
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

text {*
\noindent
The main disadvantage of the code view is that the conditions are tested
sequentially. This is visible in the generated theorems. The constructor and
destructor views offer nonsequential alternatives.
*}


subsubsection {* Mutual Corecursion
  \label{sssec:primcorec-mutual-corecursion} *}

text {*
The syntax for mutually corecursive functions over mutually corecursive
datatypes is unsurprising:
*}

    primcorec
      even_infty :: even_enat and
      odd_infty :: odd_enat
    where
      "even_infty = Even_ESucc odd_infty" |
      "odd_infty = Odd_ESucc even_infty"


subsubsection {* Nested Corecursion
  \label{sssec:primcorec-nested-corecursion} *}

text {*
The next pair of examples generalize the @{const literate} and @{const siterate}
functions (Section~\ref{sssec:primcorec-nested-corecursion}) to possibly
infinite trees in which subnodes are organized either as a lazy list (@{text
tree\<^sub>i\<^sub>i}) or as a finite set (@{text tree\<^sub>i\<^sub>s}). They rely on the map functions of
the nesting type constructors to lift the corecursive calls:
*}

    primcorec iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "iterate\<^sub>i\<^sub>i g x = Node\<^sub>i\<^sub>i x (lmap (iterate\<^sub>i\<^sub>i g) (g x))"

text {* \blankline *}

    primcorec iterate\<^sub>i\<^sub>s :: "('a \<Rightarrow> 'a fset) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>s" where
      "iterate\<^sub>i\<^sub>s g x = Node\<^sub>i\<^sub>s x (fimage (iterate\<^sub>i\<^sub>s g) (g x))"

text {*
\noindent
Both examples follow the usual format for constructor arguments associated
with nested recursive occurrences of the datatype. Consider
@{const iterate\<^sub>i\<^sub>i}. The term @{term "g x"} constructs an @{typ "'a llist"}
value, which is turned into an @{typ "'a tree\<^sub>i\<^sub>i llist"} value using
@{const lmap}.

This format may sometimes feel artificial. The following function constructs
a tree with a single, infinite branch from a stream:
*}

    primcorec tree\<^sub>i\<^sub>i_of_stream :: "'a stream \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "tree\<^sub>i\<^sub>i_of_stream s =
         Node\<^sub>i\<^sub>i (shd s) (lmap tree\<^sub>i\<^sub>i_of_stream (LCons (stl s) LNil))"

text {*
\noindent
A more natural syntax, also supported by Isabelle, is to move corecursive calls
under constructors:
*}

    primcorec (*<*)(in late) (*>*)tree\<^sub>i\<^sub>i_of_stream :: "'a stream \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "tree\<^sub>i\<^sub>i_of_stream s =
         Node\<^sub>i\<^sub>i (shd s) (LCons (tree\<^sub>i\<^sub>i_of_stream (stl s)) LNil)"

text {*
The next example illustrates corecursion through functions, which is a bit
special. Deterministic finite automata (DFAs) are traditionally defined as
5-tuples @{text "(Q, \<Sigma>, \<delta>, q\<^sub>0, F)"}, where @{text Q} is a finite set of states,
@{text \<Sigma>} is a finite alphabet, @{text \<delta>} is a transition function, @{text q\<^sub>0}
is an initial state, and @{text F} is a set of final states. The following
function translates a DFA into a state machine:
*}

    primcorec (*<*)(in early) (*>*)sm_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> 'a sm" where
      "sm_of_dfa \<delta> F q = SM (q \<in> F) (sm_of_dfa \<delta> F \<circ> \<delta> q)"

text {*
\noindent
The map function for the function type (@{text \<Rightarrow>}) is composition
(@{text "op \<circ>"}). For convenience, corecursion through functions can
also be expressed using $\lambda$-abstractions and function application rather
than through composition. For example:
*}

    primcorec sm_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> 'a sm" where
      "sm_of_dfa \<delta> F q = SM (q \<in> F) (\<lambda>a. sm_of_dfa \<delta> F (\<delta> q a))"

text {* \blankline *}

    primcorec empty_sm :: "'a sm" where
      "empty_sm = SM False (\<lambda>_. empty_sm)"

text {* \blankline *}

    primcorec not_sm :: "'a sm \<Rightarrow> 'a sm" where
      "not_sm M = SM (\<not> accept M) (\<lambda>a. not_sm (trans M a))"

text {* \blankline *}

    primcorec or_sm :: "'a sm \<Rightarrow> 'a sm \<Rightarrow> 'a sm" where
      "or_sm M N =
         SM (accept M \<or> accept N) (\<lambda>a. or_sm (trans M a) (trans N a))"

text {*
\noindent
For recursion through curried $n$-ary functions, $n$ applications of
@{term "op \<circ>"} are necessary. The examples below illustrate the case where
$n = 2$:
*}

    codatatype ('a, 'b) sm2 =
      SM2 (accept2: bool) (trans2: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) sm2")

text {* \blankline *}

    primcorec
      (*<*)(in early) (*>*)sm2_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> ('a, 'b) sm2"
    where
      "sm2_of_dfa \<delta> F q = SM2 (q \<in> F) (op \<circ> (op \<circ> (sm2_of_dfa \<delta> F)) (\<delta> q))"

text {* \blankline *}

    primcorec
      sm2_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> ('a, 'b) sm2"
    where
      "sm2_of_dfa \<delta> F q = SM2 (q \<in> F) (\<lambda>a b. sm2_of_dfa \<delta> F (\<delta> q a b))"


subsubsection {* Nested-as-Mutual Corecursion
  \label{sssec:primcorec-nested-as-mutual-corecursion} *}

text {*
Just as it is possible to recurse over nested recursive datatypes as if they
were mutually recursive
(Section~\ref{sssec:primrec-nested-as-mutual-recursion}), it is possible to
pretend that nested codatatypes are mutually corecursive. For example:
*}

(*<*)
    context late
    begin
(*>*)
    primcorec
      iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" and
      iterates\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a llist \<Rightarrow> 'a tree\<^sub>i\<^sub>i llist"
    where
      "iterate\<^sub>i\<^sub>i g x = Node\<^sub>i\<^sub>i x (iterates\<^sub>i\<^sub>i g (g x))" |
      "iterates\<^sub>i\<^sub>i g xs =
         (case xs of
            LNil \<Rightarrow> LNil
          | LCons x xs' \<Rightarrow> LCons (iterate\<^sub>i\<^sub>i g x) (iterates\<^sub>i\<^sub>i g xs'))"

text {*
\noindent
Coinduction rules are generated as
@{thm [source] iterate\<^sub>i\<^sub>i.coinduct},
@{thm [source] iterates\<^sub>i\<^sub>i.coinduct}, and
@{thm [source] iterate\<^sub>i\<^sub>i_iterates\<^sub>i\<^sub>i.coinduct}
and analogously for @{text coinduct_strong}. These rules and the
underlying corecursors are generated on a per-need basis and are kept in a cache
to speed up subsequent definitions.
*}

(*<*)
    end
(*>*)


subsubsection {* Constructor View
  \label{ssec:primrec-constructor-view} *}

(*<*)
    locale ctr_view
    begin
(*>*)

text {*
The constructor view is similar to the code view, but there is one separate
conditional equation per constructor rather than a single unconditional
equation. Examples that rely on a single constructor, such as @{const literate}
and @{const siterate}, are identical in both styles.

Here is an example where there is a difference:
*}

    primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lappend xs ys = LNil" |
      "_ \<Longrightarrow> lappend xs ys = LCons (lhd (if lnull xs then ys else xs))
         (if xs = LNil then ltl ys else lappend (ltl xs) ys)"

text {*
\noindent
With the constructor view, we must distinguish between the @{const LNil} and
the @{const LCons} case. The condition for @{const LCons} is
left implicit, as the negation of that for @{const LNil}.

For this example, the constructor view is slighlty more involved than the
code equation. Recall the code view version presented in
Section~\ref{sssec:primcorec-simple-corecursion}.
% TODO: \[{thm code_view.lappend.code}\]
The constructor view requires us to analyze the second argument (@{term ys}).
The code equation generated from the constructor view also suffers from this.
% TODO: \[{thm lappend.code}\]

In contrast, the next example is arguably more naturally expressed in the
constructor view:
*}

    primcorec
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "n mod 4 = 0 \<Longrightarrow> random_process s f n = Fail" |
      "n mod 4 = 1 \<Longrightarrow>
         random_process s f n = Skip (random_process s f (f n))" |
      "n mod 4 = 2 \<Longrightarrow>
         random_process s f n = Action (shd s) (random_process (stl s) f (f n))" |
      "n mod 4 = 3 \<Longrightarrow>
         random_process s f n = Choice (random_process (every_snd s) f (f n))
           (random_process (every_snd (stl s)) f (f n))"
(*<*)
    end
(*>*)

text {*
\noindent
Since there is no sequentiality, we can apply the equation for @{const Choice}
without having first to discharge @{term "n mod (4\<Colon>int) \<noteq> 0"},
@{term "n mod (4\<Colon>int) \<noteq> 1"}, and
@{term "n mod (4\<Colon>int) \<noteq> 2"}.
The price to pay for this elegance is that we must discharge exclusivity proof
obligations, one for each pair of conditions
@{term "(n mod (4\<Colon>int) = i, n mod (4\<Colon>int) = j)"}
with @{term "i < j"}. If we prefer not to discharge any obligations, we can
enable the @{text "sequential"} option. This pushes the problem to the users of
the generated properties.
%Here are more examples to conclude:
*}


subsubsection {* Destructor View
  \label{ssec:primrec-destructor-view} *}

(*<*)
    locale dtr_view
    begin
(*>*)

text {*
The destructor view is in many respects dual to the constructor view. Conditions
determine which constructor to choose, and these conditions are interpreted
sequentially or not depending on the @{text "sequential"} option.
Consider the following examples:
*}

    primcorec literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" where
      "\<not> lnull (literate _ x)" |
      "lhd (literate _ x) = x" |
      "ltl (literate g x) = literate g (g x)"

text {* \blankline *}

    primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      "shd (siterate _ x) = x" |
      "stl (siterate g x) = siterate g (g x)"

text {* \blankline *}

    primcorec every_snd :: "'a stream \<Rightarrow> 'a stream" where
      "shd (every_snd s) = shd s" |
      "stl (every_snd s) = stl (stl s)"

text {*
\noindent
The first formula in the @{const literate} specification indicates which
constructor to choose. For @{const siterate} and @{const every_snd}, no such
formula is necessary, since the type has only one constructor. The last two
formulas are equations specifying the value of the result for the relevant
selectors. Corecursive calls appear directly to the right of the equal sign.
Their arguments are unrestricted.

The next example shows how to specify functions that rely on more than one
constructor:
*}

    primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)" |
      "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)" |
      "ltl (lappend xs ys) = (if xs = LNil then ltl ys else lappend (ltl xs) ys)"

text {*
\noindent
For a codatatype with $n$ constructors, it is sufficient to specify $n - 1$
discriminator formulas. The command will then assume that the remaining
constructor should be taken otherwise. This can be made explicit by adding
*}

(*<*)
    end

    locale dtr_view2
    begin

    primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)" |
      "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)" |
      "ltl (lappend xs ys) = (if xs = LNil then ltl ys else lappend (ltl xs) ys)" |
(*>*)
      "_ \<Longrightarrow> \<not> lnull (lappend xs ys)"

text {*
\noindent
to the specification. The generated selector theorems are conditional.

The next example illustrates how to cope with selectors defined for several
constructors:
*}

    primcorec
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "n mod 4 = 0 \<Longrightarrow> random_process s f n = Fail" |
      "n mod 4 = 1 \<Longrightarrow> is_Skip (random_process s f n)" |
      "n mod 4 = 2 \<Longrightarrow> is_Action (random_process s f n)" |
      "n mod 4 = 3 \<Longrightarrow> is_Choice (random_process s f n)" |
      "cont (random_process s f n) = random_process s f (f n)" of Skip |
      "prefix (random_process s f n) = shd s" |
      "cont (random_process s f n) = random_process (stl s) f (f n)" of Action |
      "left (random_process s f n) = random_process (every_snd s) f (f n)" |
      "right (random_process s f n) = random_process (every_snd (stl s)) f (f n)"

text {*
\noindent
Using the @{text "of"} keyword, different equations are specified for @{const
cont} depending on which constructor is selected.

Here are more examples to conclude:
*}

    primcorec
      even_infty :: even_enat and
      odd_infty :: odd_enat
    where
      "even_infty \<noteq> Even_EZero" |
      "un_Even_ESucc even_infty = odd_infty" |
      "un_Odd_ESucc odd_infty = even_infty"

text {* \blankline *}

    primcorec iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "lbl\<^sub>i\<^sub>i (iterate\<^sub>i\<^sub>i g x) = x" |
      "sub\<^sub>i\<^sub>i (iterate\<^sub>i\<^sub>i g x) = lmap (iterate\<^sub>i\<^sub>i g) (g x)"
(*<*)
    end
(*>*)


subsection {* Command Syntax
  \label{ssec:primcorec-command-syntax} *}

subsubsection {* \keyw{primcorec} and \keyw{primcorecursive}
  \label{sssec:primcorecursive-and-primcorec} *}

text {*
\begin{matharray}{rcl}
  @{command_def "primcorec"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def "primcorecursive"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  (@@{command primcorec} | @@{command primcorecursive}) target? \<newline>
    @{syntax pcr_option}? fixes @'where' (@{syntax pcr_formula} + '|')
  ;
  @{syntax_def pcr_option}: '(' ('sequential' | 'exhaustive') ')'
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

The optional target is optionally followed by one or both of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text "sequential"} option indicates that the conditions in specifications
expressed using the constructor or destructor view are to be interpreted
sequentially.

\item
The @{text "exhaustive"} option indicates that the conditions in specifications
expressed using the constructor or destructor view cover all possible cases.
\end{itemize}

The @{command primcorec} command is an abbreviation for @{command
primcorecursive} with @{text "by auto?"} to discharge any emerging proof
obligations.

%%% TODO: elaborate on format of the propositions
%%% TODO: elaborate on mutual and nested-to-mutual
*}


(*
subsection {* Generated Theorems
  \label{ssec:primcorec-generated-theorems} *}
*)


(*
subsection {* Recursive Default Values for Selectors
  \label{ssec:primcorec-recursive-default-values-for-selectors} *}

text {*
partial_function to the rescue
*}
*)


section {* Introducing Bounded Natural Functors
  \label{sec:introducing-bounded-natural-functors} *}

text {*
The (co)datatype package can be set up to allow nested recursion through
arbitrary type constructors, as long as they adhere to the BNF requirements
and are registered as BNFs. It is also possible to declare a BNF abstractly
without specifying its internal structure.
*}


subsection {* Bounded Natural Functors
  \label{ssec:bounded-natural-functors} *}

text {*
Bounded natural functors (BNFs) are a semantic criterion for where
(co)re\-cur\-sion may appear on the right-hand side of an equation
@{cite "traytel-et-al-2012" and "blanchette-et-al-wit"}.

An $n$-ary BNF is a type constructor equipped with a map function
(functorial action), $n$ set functions (natural transformations),
and an infinite cardinal bound that satisfy certain properties.
For example, @{typ "'a llist"} is a unary BNF.
Its relator @{text "llist_all2 \<Colon>
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
*}


subsection {* Introductory Examples
  \label{ssec:bnf-introductory-examples} *}

text {*
The example below shows how to register a type as a BNF using the @{command bnf}
command. Some of the proof obligations are best viewed with the theory
@{theory Cardinal_Notations}, located in \verb|~~/src/HOL/Library|,
imported.

The type is simply a copy of the function space @{typ "'d \<Rightarrow> 'a"}, where @{typ 'a}
is live and @{typ 'd} is dead. We introduce it together with its map function,
set function, and relator.
*}

    typedef ('d, 'a) fn = "UNIV \<Colon> ('d \<Rightarrow> 'a) set"
    by simp

    text {* \blankline *}

    setup_lifting type_definition_fn

text {* \blankline *}

    lift_definition map_fn :: "('a \<Rightarrow> 'b) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn" is "op \<circ>" .
    lift_definition set_fn :: "('d, 'a) fn \<Rightarrow> 'a set" is range .

text {* \blankline *}

    lift_definition
      rel_fn :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn \<Rightarrow> bool"
    is
      "rel_fun (op =)" .

text {* \blankline *}

    bnf "('d, 'a) fn"
      map: map_fn
      sets: set_fn
      bd: "natLeq +c |UNIV :: 'd set|"
      rel: rel_fn
    proof -
      show "map_fn id = id"
        by transfer auto
    next
      fix F G show "map_fn (G \<circ> F) = map_fn G \<circ> map_fn F"
        by transfer (auto simp add: comp_def)
    next
      fix F f g
      assume "\<And>x. x \<in> set_fn F \<Longrightarrow> f x = g x"
      thus "map_fn f F = map_fn g F"
        by transfer auto
    next
      fix f show "set_fn \<circ> map_fn f = op ` f \<circ> set_fn"
        by transfer (auto simp add: comp_def)
    next
      show "card_order (natLeq +c |UNIV \<Colon> 'd set| )"
        apply (rule card_order_csum)
        apply (rule natLeq_card_order)
        by (rule card_of_card_order_on)
    next
      show "cinfinite (natLeq +c |UNIV \<Colon> 'd set| )"
        apply (rule cinfinite_csum)
        apply (rule disjI1)
        by (rule natLeq_cinfinite)
    next
      fix F :: "('d, 'a) fn"
      have "|set_fn F| \<le>o |UNIV \<Colon> 'd set|" (is "_ \<le>o ?U")
        by transfer (rule card_of_image)
      also have "?U \<le>o natLeq +c ?U"
        by (rule ordLeq_csum2) (rule card_of_Card_order)
      finally show "|set_fn F| \<le>o natLeq +c |UNIV \<Colon> 'd set|" .
    next
      fix R S
      show "rel_fn R OO rel_fn S \<le> rel_fn (R OO S)"
        by (rule, transfer) (auto simp add: rel_fun_def)
    next
      fix R
      show "rel_fn R =
            (BNF_Def.Grp {x. set_fn x \<subseteq> Collect (split R)} (map_fn fst))\<inverse>\<inverse> OO
             BNF_Def.Grp {x. set_fn x \<subseteq> Collect (split R)} (map_fn snd)"
        unfolding Grp_def fun_eq_iff relcompp.simps conversep.simps
        apply transfer
        unfolding rel_fun_def subset_iff image_iff
        by auto (force, metis pair_collapse)
    qed

text {* \blankline *}

    print_theorems
    print_bnfs

text {*
\noindent
Using \keyw{print_theorems} and @{keyword print_bnfs}, we can contemplate and
show the world what we have achieved.

This particular example does not need any nonemptiness witness, because the
one generated by default is good enough, but in general this would be
necessary. See \verb|~~/src/HOL/Basic_BNFs.thy|,
\verb|~~/src/HOL/Library/FSet.thy|, and \verb|~~/src/HOL/Library/Multiset.thy|
for further examples of BNF registration, some of which feature custom
witnesses.

The next example declares a BNF axiomatically. This can be convenient for
reasoning abstractly about an arbitrary BNF. The @{command bnf_axiomatization}
command below introduces a type @{text "('a, 'b, 'c) F"}, three set constants,
a map function, a relator, and a nonemptiness witness that depends only on
@{typ 'a}. (The type @{text "'a \<Rightarrow> ('a, 'b, 'c) F"} of
the witness can be read as an implication: If we have a witness for @{typ 'a},
we can construct a witness for @{text "('a, 'b, 'c) F"}.) The BNF
properties are postulated as axioms.
*}

    bnf_axiomatization (setA: 'a, setB: 'b, setC: 'c) F
      [wits: "'a \<Rightarrow> ('a, 'b, 'c) F"]

text {* \blankline *}

    print_theorems
    print_bnfs


subsection {* Command Syntax
  \label{ssec:bnf-command-syntax} *}

subsubsection {* \keyw{bnf}
  \label{sssec:bnf} *}

text {*
\begin{matharray}{rcl}
  @{command_def "bnf"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail \<open>
  @@{command bnf} target? (name ':')? type \<newline>
    'map:' term ('sets:' (term +))? 'bd:' term \<newline>
    ('wits:' (term +))? ('rel:' term)? \<newline>
    @{syntax plugins}?
\<close>}

\medskip

\noindent
The @{command bnf} command registers an existing type as a bounded natural
functor (BNF). The type must be equipped with an appropriate map function
(functorial action). In addition, custom set functions, relators, and
nonemptiness witnesses can be specified; otherwise, default versions are used.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{type} denotes a HOL type, and \synt{term} denotes a HOL term
@{cite "isabelle-isar-ref"}.

%%% TODO: elaborate on proof obligations
*}


subsubsection {* \keyw{bnf_axiomatization}
  \label{sssec:bnf-axiomatization} *}

text {*
\begin{matharray}{rcl}
  @{command_def "bnf_axiomatization"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command bnf_axiomatization} target? @{syntax plugins}? \<newline>
    @{syntax tyargs}? name @{syntax wit_types}? \<newline>
    mixfix? @{syntax map_rel}?
  ;
  @{syntax_def wit_types}: '[' 'wits' ':' types ']'
\<close>}

\medskip

\noindent
The @{command bnf_axiomatization} command declares a new type and associated constants
(map, set, relator, and cardinal bound) and asserts the BNF properties for
these constants as axioms.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{name} denotes an identifier, \synt{typefree} denotes fixed type variable
(@{typ 'a}, @{typ 'b}, \ldots), and \synt{mixfix} denotes the usual
parenthesized mixfix notation @{cite "isabelle-isar-ref"}.

Type arguments are live by default; they can be marked as dead by entering
@{text dead} in front of the type variable (e.g., @{text "(dead 'a)"})
instead of an identifier for the corresponding set function. Witnesses can be
specified by their types. Otherwise, the syntax of @{command bnf_axiomatization}
is identical to the left-hand side of a @{command datatype} or
@{command codatatype} definition.

The command is useful to reason abstractly about BNFs. The axioms are safe
because there exist BNFs of arbitrary large arities. Applications must import
the theory @{theory BNF_Axiomatization}, located in the directory
\verb|~~/src/|\allowbreak\verb|HOL/Library|, to use this functionality.
*}


subsubsection {* \keyw{print_bnfs}
  \label{sssec:print-bnfs} *}

text {*
\begin{matharray}{rcl}
  @{command_def "print_bnfs"} & : & @{text "local_theory \<rightarrow>"}
\end{matharray}

@{rail \<open>
  @@{command print_bnfs}
\<close>}
*}


section {* Deriving Destructors and Theorems for Free Constructors
  \label{sec:deriving-destructors-and-theorems-for-free-constructors} *}

text {*
The derivation of convenience theorems for types equipped with free constructors,
as performed internally by @{command datatype} and @{command codatatype},
is available as a stand-alone command called @{command free_constructors}.

%  * need for this is rare but may arise if you want e.g. to add destructors to
%    a type not introduced by ...
%
%  * @{command free_constructors}
%    * @{text plugins}, @{text discs_sels}
%    * hack to have both co and nonco view via locale (cf. ext nats)
*}


(*
subsection {* Introductory Example
  \label{ssec:ctors-introductory-example} *}
*)


subsection {* Command Syntax
  \label{ssec:ctors-command-syntax} *}

subsubsection {* \keyw{free_constructors}
  \label{sssec:free-constructors} *}

text {*
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
*}


(*
section {* Using the Standard ML Interface
  \label{sec:using-the-standard-ml-interface} *}

text {*
The package's programmatic interface.
*}
*)


section {* Controlling Plugins
  \label{sec:controlling-plugins} *}

text {*
Plugins extend the (co)datatype package to interoperate with other Isabelle
packages and tools, such as the code generator, Transfer, Lifting, and
Quickcheck. They can be enabled or disabled individually using the
@{syntax plugins} option to the commands @{command datatype},
@{command codatatype}, @{command free_constructors}, @{command bnf}, and
@{command bnf_axiomatization}.
For example:
*}

    datatype (plugins del: code "quickcheck") color = Red | Black


subsection {* Code Generator
  \label{ssec:code-generator} *}

text {*
The \hthm{code} plugin registers (co)datatypes and other freely generated types
for code generation. No distinction is made between datatypes and codatatypes.
This means that for target languages with a strict evaluation strategy (e.g.,
Standard ML), programs that attempt to produce infinite codatatype values will
not terminate.

The plugin derives the following properties:

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
properties of (co)datatypes and other freely generated types, as documented in
Sections \ref{ssec:datatype-generated-theorems} and
\ref{ssec:codatatype-generated-theorems}.
*}


subsection {* Size
  \label{ssec:size} *}

text {*
For each datatype, the \hthm{size} plugin generates a generic size
function @{text "t.size_t"} as well as a specific instance
@{text "size \<Colon> t \<Rightarrow> bool"} belonging to the @{text size} type
class. The \keyw{fun} command relies on @{const size} to prove termination of
recursive functions on datatypes.

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

\item[@{text "t."}\hthm{size_o_map}\rm:] ~ \\
@{thm list.size_o_map[no_vars]}

\end{description}
\end{indentblock}
*}


subsection {* Transfer
  \label{ssec:transfer} *}

text {*
For each (co)datatype with live type arguments and each manually registered BNF,
the \hthm{transfer} plugin generates a predicator @{text "t.pred_t"} and
properties that guide the Transfer tool.

The plugin derives the following properties:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{Domainp_rel} @{text "[relator_domain]"}\rm:] ~ \\
@{thm list.Domainp_rel[no_vars]}

\item[@{text "t."}\hthm{pred_inject} @{text "[simp]"}\rm:] ~ \\
@{thm list.pred_inject(1)[no_vars]} \\
@{thm list.pred_inject(2)[no_vars]}

\item[@{text "t."}\hthm{rel_eq_onp}\rm:] ~ \\
@{thm list.rel_eq_onp[no_vars]}

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
*}


subsection {* Lifting
  \label{ssec:lifting} *}

text {*
For each (co)datatype with live type arguments and each manually registered BNF,
the \hthm{lifting} plugin generates properties and attributes that guide the
Lifting tool.

The plugin derives the following property:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{Quotient} @{text "[quot_map]"}\rm:] ~ \\
@{thm list.Quotient[no_vars]}

\end{description}
\end{indentblock}

In addition, the plugin sets the @{text "[relator_eq_onp]"} attribute on a
variant of the @{text t.rel_eq_onp} property generated by the @{text lifting}
plugin, the @{text "[relator_mono]"} attribute on @{text t.rel_mono}, and the
@{text "[relator_distr]"} attribute on @{text t.rel_compp}.
*}


subsection {* Quickcheck
  \label{ssec:quickcheck} *}

text {*
The integration of datatypes with Quickcheck is accomplished by a number of
plugins that instantiate specific type classes. The plugins are listed below:

\begin{indentblock}
\hthm{quickcheck_random} \\
\hthm{quickcheck_exhaustive} \\
\hthm{quickcheck_bounded_forall} \\
\hthm{quickcheck_full_exhaustive} \\
\hthm{quickcheck_narrowing}
\end{indentblock}
*}


subsection {* Program Extraction
  \label{ssec:program-extraction} *}

text {*
The \hthm{extraction} plugin provides realizers for induction and case analysis,
to enable program extraction from proofs involving datatypes. This functionality
is only available with full proof objects, i.e., with the \emph{HOL-Proofs}
session.
*}


section {* Known Bugs and Limitations
  \label{sec:known-bugs-and-limitations} *}

text {*
This section lists the known bugs and limitations in the (co)datatype package at
the time of this writing. Many of them are expected to be addressed in future
releases.

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
\emph{Defining mutually (co)recursive (co)datatypes is slow.} Fortunately,
it is always possible to recast mutual specifications to nested ones, which are
processed more efficiently.

\item
\emph{Locally fixed types cannot be used in (co)datatype specifications.}
This limitation can be circumvented by adding type arguments to the local
(co)datatypes to abstract over the locally fixed types.

\item
\emph{The \emph{\keyw{primcorec}} command does not allow user-specified names and
attributes next to the entered formulas.} The less convenient syntax, using the
\keyw{lemmas} command, is available as an alternative.

\item
\emph{There is no way to use an overloaded constant from a syntactic type
class, such as @{text 0}, as a constructor.}

\item
\emph{There is no way to register the same type as both a datatype and a
codatatype.} This affects types such as the extended natural numbers, for which
both views would make sense (for a different set of constructors).

\item
\emph{The \emph{\keyw{derive}} command from the \emph{Archive of Formal Proofs}
has not yet been fully ported to the new-style datatypes.} Specimens featuring
nested recursion require the use of @{command datatype_compat}
(Section~\ref{sssec:datatype-compat}).

\item
\emph{The names of variables are often suboptimal in the properties generated by
the package.}

\end{enumerate}
*}


text {*
\section*{Acknowledgment}

Tobias Nipkow and Makarius Wenzel encouraged us to implement the new
(co)datatype package. Andreas Lochbihler provided lots of comments on earlier
versions of the package, especially on the coinductive part. Brian Huffman
suggested major simplifications to the internal constructions. Ond\v{r}ej
Kun\v{c}ar implemented the @{text transfer} and @{text lifting} plugins.
Florian Haftmann and Christian Urban provided general advice on Isabelle and
package writing. Stefan Milius and Lutz Schr\"oder found an elegant proof that
eliminated one of the BNF proof obligations. Andreas Lochbihler and Christian
Sternagel suggested many textual improvements to this tutorial.
*}

end
