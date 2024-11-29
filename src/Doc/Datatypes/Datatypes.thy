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
  "HOL-Library.Countable"
  "HOL-Library.FSet"
  "HOL-Library.Simps_Case_Conv"
begin


(*<*)
unbundle cardinal_syntax
(*>*)

section \<open>Introduction
  \label{sec:introduction}\<close>

text \<open>
The 2013 edition of Isabelle introduced a definitional package for freely
generated datatypes and codatatypes. This package replaces the earlier
implementation due to Berghofer and Wenzel \<^cite>\<open>"Berghofer-Wenzel:1999:TPHOL"\<close>.
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

The package is part of \<^theory>\<open>Main\<close>. Additional functionality is provided by
the theory \<^file>\<open>~~/src/HOL/Library/BNF_Axiomatization.thy\<close>.

The package, like its predecessor, fully adheres to the LCF philosophy
\<^cite>\<open>mgordon79\<close>: The characteristic theorems associated with the specified
(co)datatypes are derived rather than introduced axiomatically.%
\footnote{However, some of the
internal constructions and most of the internal proof obligations are omitted
if the \<open>quick_and_dirty\<close> option is enabled.}
The package is described in a number of scientific papers
\<^cite>\<open>"traytel-et-al-2012" and "blanchette-et-al-2014-impl" and
"panny-et-al-2014" and "blanchette-et-al-2015-wit"\<close>.
The central notion is that of a \emph{bounded natural functor} (BNF)---a
well-behaved type constructor for which nested (co)recursion is supported.

This tutorial is organized as follows:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item Section \ref{sec:defining-datatypes}, ``Defining Datatypes,''
describes how to specify datatypes using the @{command datatype} command.

\item Section \ref{sec:defining-primitively-recursive-functions}, ``Defining
Primitively Recursive Functions,'' describes how to specify functions
using @{command primrec}. (A separate tutorial \<^cite>\<open>"isabelle-function"\<close>
describes the more powerful \keyw{fun} and \keyw{function} commands.)

\item Section \ref{sec:defining-codatatypes}, ``Defining Codatatypes,''
describes how to specify codatatypes using the @{command codatatype} command.

\item Section \ref{sec:defining-primitively-corecursive-functions},
``Defining Primitively Corecursive Functions,'' describes how to specify
functions using the @{command primcorec} and
@{command primcorecursive} commands. (A separate tutorial
\<^cite>\<open>"isabelle-corec"\<close> describes the more powerful \keyw{corec} and
\keyw{corecursive} commands.)

\item Section \ref{sec:registering-bounded-natural-functors}, ``Registering
Bounded Natural Functors,'' explains how to use the @{command bnf} command
to register arbitrary type constructors as BNFs.

\item Section
\ref{sec:deriving-destructors-and-constructor-theorems},
``Deriving Destructors and Constructor Theorems,'' explains how to
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
\<^const>\<open>Truue\<close>, \<^const>\<open>Faalse\<close>, and \<^const>\<open>Perhaaps\<close> have the type \<^typ>\<open>trool\<close>.

Polymorphic types are possible, such as the following option type, modeled after
its homologue from the \<^theory>\<open>HOL.Option\<close> theory:
\<close>

(*<*)
    hide_const None Some map_option
    hide_type option
(*>*)
    datatype 'a option = None | Some 'a

text \<open>
\noindent
The constructors are \<open>None :: 'a option\<close> and
\<open>Some :: 'a \<Rightarrow> 'a option\<close>.

The next example has three type parameters:
\<close>

    datatype ('a, 'b, 'c) triple = Triple 'a 'b 'c

text \<open>
\noindent
The constructor is
\<open>Triple :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> ('a, 'b, 'c) triple\<close>.
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
stores a value of type \<^typ>\<open>'b\<close> at the very end:
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
through lists. A more complex example, that reuses our \<^type>\<open>option\<close> type,
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
The issue is that the function arrow \<open>\<Rightarrow>\<close> allows recursion
only through its right-hand side. This issue is inherited by polymorphic
datatypes defined in terms of~\<open>\<Rightarrow>\<close>:
\<close>

    datatype ('a, 'b) fun_copy = Fun "'a \<Rightarrow> 'b"
    datatype 'a also_wrong = W1 | W2 (*<*)'a
    typ (*>*)"('a also_wrong, 'a) fun_copy"

text \<open>
\noindent
The following definition of \<^typ>\<open>'a\<close>-branching trees is legal:
\<close>

    datatype 'a ftree = FTLeaf 'a | FTNode "'a \<Rightarrow> 'a ftree"

text \<open>
\noindent
And so is the definition of hereditarily finite sets:
\<close>

    datatype hfset = HFSet "hfset fset"

text \<open>
\noindent
In general, type constructors \<open>('a\<^sub>1, \<dots>, 'a\<^sub>m) t\<close>
allow recursion on a subset of their type arguments \<open>'a\<^sub>1\<close>, \ldots,
\<open>'a\<^sub>m\<close>. These type arguments are called \emph{live}; the remaining
type arguments are called \emph{dead}. In \<^typ>\<open>'a \<Rightarrow> 'b\<close> and
\<^typ>\<open>('a, 'b) fun_copy\<close>, the type variable \<^typ>\<open>'a\<close> is dead and
\<^typ>\<open>'b\<close> is live.

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
custom names. In the example below, the familiar names \<open>null\<close>, \<open>hd\<close>,
\<open>tl\<close>, \<open>set\<close>, \<open>map\<close>, and \<open>list_all2\<close> override the
default names \<open>is_Nil\<close>, \<open>un_Cons1\<close>, \<open>un_Cons2\<close>,
\<open>set_list\<close>, \<open>map_list\<close>, and \<open>rel_list\<close>:
\<close>

(*<*)
    no_translations
      "[x, xs]" == "x # [xs]"
      "[x]" == "x # []"

    unbundle no list_syntax
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
  \<open>Nil :: 'a list\<close> \\
&
  \<open>Cons :: 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> \\
Discriminator: &
  \<open>null :: 'a list \<Rightarrow> bool\<close> \\
Selectors: &
  \<open>hd :: 'a list \<Rightarrow> 'a\<close> \\
&
  \<open>tl :: 'a list \<Rightarrow> 'a list\<close> \\
Set function: &
  \<open>set :: 'a list \<Rightarrow> 'a set\<close> \\
Map function: &
  \<open>map :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list\<close> \\
Relator: &
  \<open>list_all2 :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool\<close>
\end{tabular}

\medskip

The discriminator \<^const>\<open>null\<close> and the selectors \<^const>\<open>hd\<close> and \<^const>\<open>tl\<close>
are characterized by the following conditional equations:
%
\[@{thm list.collapse(1)[of xs, no_vars]}
  \qquad @{thm list.collapse(2)[of xs, no_vars]}\]
%
For two-constructor datatypes, a single discriminator constant is sufficient.
The discriminator associated with \<^const>\<open>Cons\<close> is simply
\<^term>\<open>\<lambda>xs. \<not> null xs\<close>.

The \keyw{where} clause at the end of the command specifies a default value for
selectors applied to constructors on which they are not a priori specified.
In the example, it is used to ensure that the tail of the empty list is itself
(instead of being left unspecified).

Because \<^const>\<open>Nil\<close> is nullary, it is also possible to use
\<^term>\<open>\<lambda>xs. xs = Nil\<close> as a discriminator. This is the default behavior
if we omit the identifier \<^const>\<open>null\<close> and the associated colon. Some users
argue against this, because the mixture of constructors and selectors in the
characteristic theorems can lead Isabelle's automation to switch between the
constructor and the destructor view in surprising ways.

The usual mixfix syntax annotations are available for both types and
constructors. For example:
\<close>

(*<*)
    end
(*>*)
    datatype ('a, 'b) prod (infixr \<open>*\<close> 20) = Pair 'a 'b

text \<open>\blankline\<close>

    datatype (set: 'a) list =
      null: Nil (\<open>[]\<close>)
    | Cons (hd: 'a) (tl: "'a list") (infixr \<open>#\<close> 65)
    for
      map: map
      rel: list_all2
      pred: list_all

text \<open>
\noindent
Incidentally, this is how the traditional syntax can be set up:
\<close>
(*<*)
unbundle no list_enumeration_syntax
(*>*)
    syntax "_list" :: "args \<Rightarrow> 'a list" (\<open>[(_)]\<close>)

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
  @{command_def "datatype"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
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
\<close>

\medskip

\noindent
The @{command datatype} command introduces a set of mutually recursive
datatypes specified by their constructors.

The syntactic entity \synt{target} can be used to specify a local
context (e.g., \<open>(in linorder)\<close> \<^cite>\<open>"isabelle-isar-ref"\<close>),
and \synt{prop} denotes a HOL proposition.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The \<open>plugins\<close> option indicates which plugins should be enabled
(\<open>only\<close>) or disabled (\<open>del\<close>). By default, all plugins are enabled.

\item
The \<open>discs_sels\<close> option indicates that discriminators and selectors
should be generated. The option is implicitly enabled if names are specified for
discriminators or selectors.
\end{itemize}

The optional \keyw{where} clause specifies default values for selectors.
Each proposition must be an equation of the form
\<open>un_D (C \<dots>) = \<dots>\<close>, where \<open>C\<close> is a constructor and
\<open>un_D\<close> is a selector.

The left-hand sides of the datatype equations specify the name of the type to
define, its type parameters, and additional information:

\<^rail>\<open>
  @{syntax_def dt_name}: @{syntax tyargs}? name mixfix?
  ;
  @{syntax_def tyargs}: typefree | '(' (('dead' | name ':')? typefree + ',') ')'
\<close>

\medskip

\noindent
The syntactic entity \synt{name} denotes an identifier, \synt{mixfix} denotes
the usual parenthesized mixfix notation, and \synt{typefree} denotes fixed type
variable (\<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close>, \ldots) \<^cite>\<open>"isabelle-isar-ref"\<close>.

The optional names preceding the type variables allow to override the default
names of the set functions (\<open>set\<^sub>1_t\<close>, \ldots, \<open>set\<^sub>m_t\<close>). Type
arguments can be marked as dead by entering \<open>dead\<close> in front of the
type variable (e.g., \<open>(dead 'a)\<close>); otherwise, they are live or dead
(and a set function is generated or not) depending on where they occur in the
right-hand sides of the definition. Declaring a type argument as dead can speed
up the type definition but will prevent any later (co)recursion through that
type argument.

Inside a mutually recursive specification, all defined datatypes must
mention exactly the same type variables in the same order.

\<^rail>\<open>
  @{syntax_def dt_ctor}: (name ':')? name (@{syntax dt_ctor_arg} * ) mixfix?
\<close>

\medskip

\noindent
The main constituents of a constructor specification are the name of the
constructor and the list of its argument types. An optional discriminator name
can be supplied at the front. If discriminators are enabled (cf.\ the
\<open>discs_sels\<close> option) but no name is supplied, the default is
\<open>\<lambda>x. x = C\<^sub>j\<close> for nullary constructors and
\<open>t.is_C\<^sub>j\<close> otherwise.

\<^rail>\<open>
  @{syntax_def dt_ctor_arg}: type | '(' name ':' type ')'
\<close>

\medskip

\noindent
The syntactic entity \synt{type} denotes a HOL type \<^cite>\<open>"isabelle-isar-ref"\<close>.

In addition to the type of a constructor argument, it is possible to specify a
name for the corresponding selector. The same selector name can be reused for
arguments to several constructors as long as the arguments share the same type.
If selectors are enabled (cf.\ the \<open>discs_sels\<close> option) but no name is
supplied, the default name is \<open>un_C\<^sub>ji\<close>.
\<close>


subsubsection \<open>\keyw{datatype_compat}
  \label{sssec:datatype-compat}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "datatype_compat"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
  @@{command datatype_compat} (name +)
\<close>

\medskip

\noindent
The @{command datatype_compat} command registers new-style datatypes as
old-style datatypes and invokes the old-style plugins. For example:
\<close>

    datatype_compat even_nat odd_nat

text \<open>\blankline\<close>

    ML \<open>Old_Datatype_Data.get_info \<^theory> \<^type_name>\<open>even_nat\<close>\<close>

text \<open>
The syntactic entity \synt{name} denotes an identifier \<^cite>\<open>"isabelle-isar-ref"\<close>.

The command is sometimes useful when migrating from the old datatype package to
the new one.

A few remarks concern nested recursive datatypes:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The old-style, nested-as-mutual induction rule and recursor theorems are
generated under their usual names but with ``\<open>compat_\<close>'' prefixed
(e.g., \<open>compat_tree.induct\<close>, \<open>compat_tree.inducts\<close>, and
\<open>compat_tree.rec\<close>). These theorems should be identical to the ones
generated by the old datatype package, \emph{up to the order of the
premises}---meaning that the subgoals generated by the \<open>induct\<close> or
\<open>induction\<close> method may be in a different order than before.

\item All types through which recursion takes place must be new-style datatypes
or the function type.
\end{itemize}
\<close>


subsection \<open>Generated Constants
  \label{ssec:datatype-generated-constants}\<close>

text \<open>
Given a datatype \<open>('a\<^sub>1, \<dots>, 'a\<^sub>m) t\<close> with $m$ live type variables
and $n$ constructors \<open>t.C\<^sub>1\<close>, \ldots, \<open>t.C\<^sub>n\<close>, the following
auxiliary constants are introduced:

\medskip

\begin{tabular}{@ {}ll@ {}}
Case combinator: &
  \<open>t.case_t\<close> (rendered using the familiar \<open>case\<close>--\<open>of\<close> syntax) \\
Discriminators: &
  \<open>t.is_C\<^sub>1\<close>$, \ldots, $\<open>t.is_C\<^sub>n\<close> \\
Selectors: &
  \<open>t.un_C\<^sub>11\<close>$, \ldots, $\<open>t.un_C\<^sub>1k\<^sub>1\<close> \\
& \quad\vdots \\
& \<open>t.un_C\<^sub>n1\<close>$, \ldots, $\<open>t.un_C\<^sub>nk\<^sub>n\<close> \\
Set functions: &
  \<open>t.set\<^sub>1_t\<close>, \ldots, \<open>t.set\<^sub>m_t\<close> \\
Map function: &
  \<open>t.map_t\<close> \\
Relator: &
  \<open>t.rel_t\<close> \\
Recursor: &
  \<open>t.rec_t\<close>
\end{tabular}

\medskip

\noindent
The discriminators and selectors are generated only if the \<open>discs_sels\<close>
option is enabled or if names are specified for discriminators or selectors.
The set functions, map function, predicator, and relator are generated only if $m > 0$.

In addition, some of the plugins introduce their own constants
(Section~\ref{sec:selecting-plugins}). The case combinator, discriminators,
and selectors are collectively called \emph{destructors}. The prefix
``\<open>t.\<close>'' is an optional component of the names and is normally hidden.
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
for \<^typ>\<open>'a list\<close>:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{inject} \<open>[iff, induct_simp]\<close>\rm:] ~ \\
@{thm list.inject[no_vars]}

\item[\<open>t.\<close>\hthm{distinct} \<open>[simp, induct_simp]\<close>\rm:] ~ \\
@{thm list.distinct(1)[no_vars]} \\
@{thm list.distinct(2)[no_vars]}

\item[\<open>t.\<close>\hthm{exhaust} \<open>[cases t, case_names C\<^sub>1 \<dots> C\<^sub>n]\<close>\rm:] ~ \\
@{thm list.exhaust[no_vars]}

\item[\<open>t.\<close>\hthm{nchotomy}\rm:] ~ \\
@{thm list.nchotomy[no_vars]}

\end{description}
\end{indentblock}

\noindent
In addition, these nameless theorems are registered as safe elimination rules:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{distinct {\upshape[}THEN notE}\<open>, elim!\<close>\hthm{\upshape]}\rm:] ~ \\
@{thm list.distinct(1)[THEN notE, elim!, no_vars]} \\
@{thm list.distinct(2)[THEN notE, elim!, no_vars]}

\end{description}
\end{indentblock}

\noindent
The next subgroup is concerned with the case combinator:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{case} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm list.case(1)[no_vars]} \\
@{thm list.case(2)[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>t.\<close>\hthm{case_cong} \<open>[fundef_cong]\<close>\rm:] ~ \\
@{thm list.case_cong[no_vars]}

\item[\<open>t.\<close>\hthm{case_cong_weak} \<open>[cong]\<close>\rm:] ~ \\
@{thm list.case_cong_weak[no_vars]}

\item[\<open>t.\<close>\hthm{case_distrib}\rm:] ~ \\
@{thm list.case_distrib[no_vars]}

\item[\<open>t.\<close>\hthm{split}\rm:] ~ \\
@{thm list.split[no_vars]}

\item[\<open>t.\<close>\hthm{split_asm}\rm:] ~ \\
@{thm list.split_asm[no_vars]}

\item[\<open>t.\<close>\hthm{splits} = \<open>split split_asm\<close>]

\end{description}
\end{indentblock}

\noindent
The third subgroup revolves around discriminators and selectors:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{disc} \<open>[simp]\<close>\rm:] ~ \\
@{thm list.disc(1)[no_vars]} \\
@{thm list.disc(2)[no_vars]}

\item[\<open>t.\<close>\hthm{discI}\rm:] ~ \\
@{thm list.discI(1)[no_vars]} \\
@{thm list.discI(2)[no_vars]}

\item[\<open>t.\<close>\hthm{sel} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm list.sel(1)[no_vars]} \\
@{thm list.sel(2)[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>t.\<close>\hthm{collapse} \<open>[simp]\<close>\rm:] ~ \\
@{thm list.collapse(1)[no_vars]} \\
@{thm list.collapse(2)[no_vars]} \\
The \<open>[simp]\<close> attribute is exceptionally omitted for datatypes equipped
with a single nullary constructor, because a property of the form
\<^prop>\<open>x = C\<close> is not suitable as a simplification rule.

\item[\<open>t.\<close>\hthm{distinct_disc} \<open>[dest]\<close>\rm:] ~ \\
These properties are missing for \<^typ>\<open>'a list\<close> because there is only one
proper discriminator. If the datatype had been introduced with a second
discriminator called \<^const>\<open>nonnull\<close>, they would have read as follows: \\[\jot]
\<^prop>\<open>null list \<Longrightarrow> \<not> nonnull list\<close> \\
\<^prop>\<open>nonnull list \<Longrightarrow> \<not> null list\<close>

\item[\<open>t.\<close>\hthm{exhaust_disc} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n]\<close>\rm:] ~ \\
@{thm list.exhaust_disc[no_vars]}

\item[\<open>t.\<close>\hthm{exhaust_sel} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n]\<close>\rm:] ~ \\
@{thm list.exhaust_sel[no_vars]}

\item[\<open>t.\<close>\hthm{expand}\rm:] ~ \\
@{thm list.expand[no_vars]}

\item[\<open>t.\<close>\hthm{split_sel}\rm:] ~ \\
@{thm list.split_sel[no_vars]}

\item[\<open>t.\<close>\hthm{split_sel_asm}\rm:] ~ \\
@{thm list.split_sel_asm[no_vars]}

\item[\<open>t.\<close>\hthm{split_sels} = \<open>split_sel split_sel_asm\<close>]

\item[\<open>t.\<close>\hthm{case_eq_if}\rm:] ~ \\
@{thm list.case_eq_if[no_vars]}

\item[\<open>t.\<close>\hthm{disc_eq_case}\rm:] ~ \\
@{thm list.disc_eq_case(1)[no_vars]} \\
@{thm list.disc_eq_case(2)[no_vars]}

\end{description}
\end{indentblock}

\noindent
In addition, equational versions of \<open>t.disc\<close> are registered with the
\<open>[code]\<close> attribute. The \<open>[code]\<close> attribute is set by the
\<open>code\<close> plugin (Section~\ref{ssec:code-generator}).
\<close>


subsubsection \<open>Functorial Theorems
  \label{sssec:functorial-theorems}\<close>

text \<open>
The functorial theorems are generated for type constructors with at least
one live type argument (e.g., \<^typ>\<open>'a list\<close>). They are partitioned in two
subgroups. The first subgroup consists of properties involving the
constructors or the destructors and either a set function, the map function,
the predicator, or the relator:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{case_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.case_transfer[no_vars]} \\
This property is generated by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}).
%The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
%(Section~\ref{ssec:transfer}).

\item[\<open>t.\<close>\hthm{sel_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
This property is missing for \<^typ>\<open>'a list\<close> because there is no common
selector to all constructors. \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}).

\item[\<open>t.\<close>\hthm{ctr_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.ctr_transfer(1)[no_vars]} \\
@{thm list.ctr_transfer(2)[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}) .

\item[\<open>t.\<close>\hthm{disc_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.disc_transfer(1)[no_vars]} \\
@{thm list.disc_transfer(2)[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}).

\item[\<open>t.\<close>\hthm{set} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm list.set(1)[no_vars]} \\
@{thm list.set(2)[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>t.\<close>\hthm{set_cases} \<open>[consumes 1, cases set: set\<^sub>i_t]\<close>\rm:] ~ \\
@{thm list.set_cases[no_vars]}

\item[\<open>t.\<close>\hthm{set_intros}\rm:] ~ \\
@{thm list.set_intros(1)[no_vars]} \\
@{thm list.set_intros(2)[no_vars]}

\item[\<open>t.\<close>\hthm{set_sel}\rm:] ~ \\
@{thm list.set_sel[no_vars]}

\item[\<open>t.\<close>\hthm{map} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm list.map(1)[no_vars]} \\
@{thm list.map(2)[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>t.\<close>\hthm{map_disc_iff} \<open>[simp]\<close>\rm:] ~ \\
@{thm list.map_disc_iff[no_vars]}

\item[\<open>t.\<close>\hthm{map_sel}\rm:] ~ \\
@{thm list.map_sel[no_vars]}

\item[\<open>t.\<close>\hthm{pred_inject} \<open>[simp]\<close>\rm:] ~ \\
@{thm list.pred_inject(1)[no_vars]} \\
@{thm list.pred_inject(2)[no_vars]}

\item[\<open>t.\<close>\hthm{rel_inject} \<open>[simp]\<close>\rm:] ~ \\
@{thm list.rel_inject(1)[no_vars]} \\
@{thm list.rel_inject(2)[no_vars]}

\item[\<open>t.\<close>\hthm{rel_distinct} \<open>[simp]\<close>\rm:] ~ \\
@{thm list.rel_distinct(1)[no_vars]} \\
@{thm list.rel_distinct(2)[no_vars]}

\item[\<open>t.\<close>\hthm{rel_intros}\rm:] ~ \\
@{thm list.rel_intros(1)[no_vars]} \\
@{thm list.rel_intros(2)[no_vars]}

\item[\<open>t.\<close>\hthm{rel_cases} \<open>[consumes 1, case_names t\<^sub>1 \<dots> t\<^sub>m, cases pred]\<close>\rm:] ~ \\
@{thm list.rel_cases[no_vars]}

\item[\<open>t.\<close>\hthm{rel_sel}\rm:] ~ \\
@{thm list.rel_sel[no_vars]}

\end{description}
\end{indentblock}

\noindent
In addition, equational versions of \<open>t.rel_inject\<close> and \<open>rel_distinct\<close> are registered with the \<open>[code]\<close> attribute. The
\<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

The second subgroup consists of more abstract properties of the set functions,
the map function, the predicator, and the relator:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{inj_map}\rm:] ~ \\
@{thm list.inj_map[no_vars]}

\item[\<open>t.\<close>\hthm{inj_map_strong}\rm:] ~ \\
@{thm list.inj_map_strong[no_vars]}

\item[\<open>t.\<close>\hthm{map_comp}\rm:] ~ \\
@{thm list.map_comp[no_vars]}

\item[\<open>t.\<close>\hthm{map_cong0}\rm:] ~ \\
@{thm list.map_cong0[no_vars]}

\item[\<open>t.\<close>\hthm{map_cong} \<open>[fundef_cong]\<close>\rm:] ~ \\
@{thm list.map_cong[no_vars]}

\item[\<open>t.\<close>\hthm{map_cong_pred}\rm:] ~ \\
@{thm list.map_cong_pred[no_vars]}

\item[\<open>t.\<close>\hthm{map_cong_simp}\rm:] ~ \\
@{thm list.map_cong_simp[no_vars]}

\item[\<open>t.\<close>\hthm{map_id0}\rm:] ~ \\
@{thm list.map_id0[no_vars]}

\item[\<open>t.\<close>\hthm{map_id}\rm:] ~ \\
@{thm list.map_id[no_vars]}

\item[\<open>t.\<close>\hthm{map_ident}\rm:] ~ \\
@{thm list.map_ident[no_vars]}

\item[\<open>t.\<close>\hthm{map_ident_strong}\rm:] ~ \\
@{thm list.map_ident_strong[no_vars]}

\item[\<open>t.\<close>\hthm{map_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.map_transfer[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\item[\<open>t.\<close>\hthm{pred_cong} \<open>[fundef_cong]\<close>\rm:] ~ \\
@{thm list.pred_cong[no_vars]}

\item[\<open>t.\<close>\hthm{pred_cong_simp}\rm:] ~ \\
@{thm list.pred_cong_simp[no_vars]}

\item[\<open>t.\<close>\hthm{pred_map}\rm:] ~ \\
@{thm list.pred_map[no_vars]}

\item[\<open>t.\<close>\hthm{pred_mono} \<open>[mono]\<close>\rm:] ~ \\
@{thm list.pred_mono[no_vars]}

\item[\<open>t.\<close>\hthm{pred_mono_strong}\rm:] ~ \\
@{thm list.pred_mono_strong[no_vars]}

\item[\<open>t.\<close>\hthm{pred_rel}\rm:] ~ \\
@{thm list.pred_rel[no_vars]}

\item[\<open>t.\<close>\hthm{pred_set}\rm:] ~ \\
@{thm list.pred_set[no_vars]}

\item[\<open>t.\<close>\hthm{pred_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.pred_transfer[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\item[\<open>t.\<close>\hthm{pred_True}\rm:] ~ \\
@{thm list.pred_True[no_vars]}

\item[\<open>t.\<close>\hthm{set_map}\rm:] ~ \\
@{thm list.set_map[no_vars]}

\item[\<open>t.\<close>\hthm{set_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.set_transfer[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\item[\<open>t.\<close>\hthm{rel_compp} \<open>[relator_distr]\<close>\rm:] ~ \\
@{thm list.rel_compp[no_vars]} \\
The \<open>[relator_distr]\<close> attribute is set by the \<open>lifting\<close> plugin
(Section~\ref{ssec:lifting}).

\item[\<open>t.\<close>\hthm{rel_conversep}\rm:] ~ \\
@{thm list.rel_conversep[no_vars]}

\item[\<open>t.\<close>\hthm{rel_eq}\rm:] ~ \\
@{thm list.rel_eq[no_vars]}

\item[\<open>t.\<close>\hthm{rel_eq_onp}\rm:] ~ \\
@{thm list.rel_eq_onp[no_vars]}

\item[\<open>t.\<close>\hthm{rel_flip}\rm:] ~ \\
@{thm list.rel_flip[no_vars]}

\item[\<open>t.\<close>\hthm{rel_map}\rm:] ~ \\
@{thm list.rel_map(1)[no_vars]} \\
@{thm list.rel_map(2)[no_vars]}

\item[\<open>t.\<close>\hthm{rel_mono} \<open>[mono, relator_mono]\<close>\rm:] ~ \\
@{thm list.rel_mono[no_vars]} \\
The \<open>[relator_mono]\<close> attribute is set by the \<open>lifting\<close> plugin
(Section~\ref{ssec:lifting}).

\item[\<open>t.\<close>\hthm{rel_mono_strong}\rm:] ~ \\
@{thm list.rel_mono_strong[no_vars]}

\item[\<open>t.\<close>\hthm{rel_cong} \<open>[fundef_cong]\<close>\rm:] ~ \\
@{thm list.rel_cong[no_vars]}

\item[\<open>t.\<close>\hthm{rel_cong_simp}\rm:] ~ \\
@{thm list.rel_cong_simp[no_vars]}

\item[\<open>t.\<close>\hthm{rel_refl}\rm:] ~ \\
@{thm list.rel_refl[no_vars]}

\item[\<open>t.\<close>\hthm{rel_refl_strong}\rm:] ~ \\
@{thm list.rel_refl_strong[no_vars]}

\item[\<open>t.\<close>\hthm{rel_reflp}\rm:] ~ \\
@{thm list.rel_reflp[no_vars]}

\item[\<open>t.\<close>\hthm{rel_symp}\rm:] ~ \\
@{thm list.rel_symp[no_vars]}

\item[\<open>t.\<close>\hthm{rel_transp}\rm:] ~ \\
@{thm list.rel_transp[no_vars]}

\item[\<open>t.\<close>\hthm{rel_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.rel_transfer[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
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

\item[\<open>t.\<close>\hthm{induct} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n, induct t]\<close>\rm:] ~ \\
@{thm list.induct[no_vars]}

\item[\<open>t.\<close>\hthm{rel_induct} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n, induct pred]\<close>\rm:] ~ \\
@{thm list.rel_induct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  \<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{induct} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n]\<close>\rm: \\
  \<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{rel_induct} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n]\<close>\rm: \\
\end{tabular}] ~ \\
Given $m > 1$ mutually recursive datatypes, this induction rule can be used to
prove $m$ properties simultaneously.

\item[\<open>t.\<close>\hthm{rec} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm list.rec(1)[no_vars]} \\
@{thm list.rec(2)[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>t.\<close>\hthm{rec_o_map}\rm:] ~ \\
@{thm list.rec_o_map[no_vars]}

\item[\<open>t.\<close>\hthm{rec_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.rec_transfer[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\end{description}
\end{indentblock}

\noindent
For convenience, @{command datatype} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{simps}] = \<open>t.inject\<close> \<open>t.distinct\<close> \<open>t.case\<close> \<open>t.rec\<close> \<open>t.map\<close> \<open>t.rel_inject\<close> \\
\<open>t.rel_distinct\<close> \<open>t.set\<close>

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


subsection \<open>Antiquotation
  \label{ssec:datatype-antiquotation}\<close>

subsubsection \<open>\textit{datatype}
  \label{sssec:datatype-datatype}\<close>

text \<open>
The \textit{datatype} antiquotation, written
\texttt{\char`\\\char`<\char`^}\verb|datatype>|\guilsinglleft\textit{t}\guilsinglright{}
or \texttt{@}\verb|{datatype| \textit{t}\verb|}|, where \textit{t} is a type
name, expands to \LaTeX{} code for the definition of the datatype, with each
constructor listed with its argument types. For example, if \textit{t} is
@{type option}:

\begin{quote}
\<^datatype>\<open>option\<close>
\end{quote}
\<close>


subsection \<open>Compatibility Issues
  \label{ssec:datatype-compatibility-issues}\<close>

text \<open>
The command @{command datatype} has been designed to be highly compatible with
the old, pre-Isabelle2015 command, to ease migration. There are nonetheless a
few incompatibilities that may arise when porting:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{The Standard ML interfaces are different.} Tools and extensions
written to call the old ML interfaces will need to be adapted to the new
interfaces. The \<open>BNF_LFP_Compat\<close> structure provides convenience functions
that simulate the old interfaces in terms of the new ones.

\item \emph{The recursor \<open>rec_t\<close> has a different signature for nested
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
induction rule can be obtained by applying the \<open>[unfolded
all_mem_range]\<close> attribute on \<open>t.induct\<close>.

\item \emph{The \<^const>\<open>size\<close> function has a slightly different definition.}
The new function returns \<open>1\<close> instead of \<open>0\<close> for some nonrecursive
constructors. This departure from the old behavior made it possible to implement
\<^const>\<open>size\<close> in terms of the generic function \<open>t.size_t\<close>. Moreover,
the new function considers nested occurrences of a value, in the nested
recursive case. The old behavior can be obtained by disabling the \<open>size\<close>
plugin (Section~\ref{sec:selecting-plugins}) and instantiating the
\<open>size\<close> type class manually.

\item \emph{The internal constructions are completely different.} Proof texts
that unfold the definition of constants introduced by the old command will
be difficult to port.

\item \emph{Some constants and theorems have different names.}
For non-mutually recursive datatypes,
the alias \<open>t.inducts\<close> for \<open>t.induct\<close> is no longer generated.
For $m > 1$ mutually recursive datatypes,
\<open>rec_t\<^sub>1_\<dots>_t\<^sub>m_i\<close> has been renamed
\<open>rec_t\<^sub>i\<close> for each \<open>i \<in> {1, \<dots>, m}\<close>,
\<open>t\<^sub>1_\<dots>_t\<^sub>m.inducts(i)\<close> has been renamed
\<open>t\<^sub>i.induct\<close> for each \<open>i \<in> {1, \<dots>, m}\<close>, and the
collection \<open>t\<^sub>1_\<dots>_t\<^sub>m.size\<close> (generated by the
\<open>size\<close> plugin, Section~\ref{ssec:size}) has been divided into
\<open>t\<^sub>1.size\<close>, \ldots, \<open>t\<^sub>m.size\<close>.

\item \emph{The \<open>t.simps\<close> collection has been extended.}
Previously available theorems are available at the same index as before.

\item \emph{Variables in generated properties have different names.} This is
rarely an issue, except in proof texts that refer to variable names in the
\<open>[where \<dots>]\<close> attribute. The solution is to use the more robust
\<open>[of \<dots>]\<close> syntax.
\end{itemize}
\<close>


section \<open>Defining Primitively Recursive Functions
  \label{sec:defining-primitively-recursive-functions}\<close>

text \<open>
Recursive functions over datatypes can be specified using the @{command primrec}
command, which supports primitive recursion, or using the \keyw{fun},
\keyw{function}, and \keyw{partial_function} commands. In this tutorial, the
focus is on @{command primrec}; \keyw{fun} and \keyw{function} are described in
a separate tutorial \<^cite>\<open>"isabelle-function"\<close>.

Because it is restricted to primitive recursion, @{command primrec} is less
powerful than \keyw{fun} and \keyw{function}. However, there are primitively
recursive specifications (e.g., based on infinitely branching or mutually
recursive datatypes) for which \keyw{fun}'s termination check fails. It is also
good style to use the simpler @{command primrec} mechanism when it works, both
as an optimization and as documentation.
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
recursive calls are lifted to lists using \<^const>\<open>map\<close>:
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
The next example features recursion through the \<open>option\<close> type. Although
\<open>option\<close> is not a new-style datatype, it is registered as a BNF with the
map function \<^const>\<open>map_option\<close>:
\<close>

    primrec (*<*)(in early) (*>*)sum_btree :: "('a::{zero,plus}) btree \<Rightarrow> 'a" where
      "sum_btree (BNode a lt rt) =
         a + the_default 0 (map_option sum_btree lt) +
           the_default 0 (map_option sum_btree rt)"

text \<open>
\noindent
The same principle applies for arbitrary type constructors through which
recursion is possible. Notably, the map function for the function type
(\<open>\<Rightarrow>\<close>) is simply composition (\<open>(\<circ>)\<close>):
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
\<^term>\<open>(\<circ>)\<close> are necessary. The examples below illustrate the case where
$n = 2$:
\<close>

    datatype 'a ftree2 = FTLeaf2 'a | FTNode2 "'a \<Rightarrow> 'a \<Rightarrow> 'a ftree2"

text \<open>\blankline\<close>

    primrec (*<*)(in early) (*>*)relabel_ft2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree2 \<Rightarrow> 'a ftree2" where
      "relabel_ft2 f (FTLeaf2 x) = FTLeaf2 (f x)"
    | "relabel_ft2 f (FTNode2 g) = FTNode2 ((\<circ>) ((\<circ>) (relabel_ft2 f)) g)"

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
%    at or the_default, whereas \<^const>\<open>ats\<^sub>f\<^sub>f\<close> is much more specific
%
%  * but:
%     * is perhaps less intuitive, because it requires higher-order thinking
%     * may seem inefficient, and indeed with the code generator the
%       mutually recursive version might be nicer
%     * is somewhat indirect -- must apply a map first, then compute a result
%       (cannot mix)
%     * the auxiliary functions like \<^const>\<open>ats\<^sub>f\<^sub>f\<close> are sometimes useful in own right
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
  @{command_def "primrec"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
  @@{command primrec} target? @{syntax pr_options}? fixes \<newline>
  @'where' (@{syntax pr_equation} + '|')
  ;
  @{syntax_def pr_options}: '(' ((@{syntax plugins} | 'nonexhaustive' | 'transfer') + ',') ')'
  ;
  @{syntax_def pr_equation}: thmdecl? prop
\<close>

\medskip

\noindent
The @{command primrec} command introduces a set of mutually recursive functions
over datatypes.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{fixes} denotes a list of names with optional type signatures,
\synt{thmdecl} denotes an optional name for the formula that follows, and
\synt{prop} denotes a HOL proposition \<^cite>\<open>"isabelle-isar-ref"\<close>.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The \<open>plugins\<close> option indicates which plugins should be enabled
(\<open>only\<close>) or disabled (\<open>del\<close>). By default, all plugins are enabled.

\item
The \<open>nonexhaustive\<close> option indicates that the functions are not
necessarily specified for all constructors. It can be used to suppress the
warning that is normally emitted when some constructors are missing.

\item
The \<open>transfer\<close> option indicates that an unconditional transfer rule
should be generated and proved \<open>by transfer_prover\<close>. The
\<open>[transfer_rule]\<close> attribute is set on the generated theorem.
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
for \<^const>\<open>tfold\<close>):

\begin{indentblock}
\begin{description}

\item[\<open>f.\<close>\hthm{simps} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm tfold.simps(1)[no_vars]} \\
@{thm tfold.simps(2)[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>f.\<close>\hthm{transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm tfold.transfer[no_vars]} \\
This theorem is generated by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}) for functions declared with the \<open>transfer\<close>
option enabled.

\item[\<open>f.\<close>\hthm{induct} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n]\<close>\rm:] ~ \\
This induction rule is generated for nested-as-mutual recursive functions
(Section~\ref{sssec:primrec-nested-as-mutual-recursion}).

\item[\<open>f\<^sub>1_\<dots>_f\<^sub>m.\<close>\hthm{induct} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n]\<close>\rm:] ~ \\
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
A datatype selector \<open>un_D\<close> can have a default value for each constructor
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
Introduce a fully unspecified constant \<open>un_D\<^sub>0 :: 'a\<close> using
@{command consts}.

\item
Define the datatype, specifying \<open>un_D\<^sub>0\<close> as the selector's default
value.

\item
Define the behavior of \<open>un_D\<^sub>0\<close> on values of the newly introduced
datatype using the \keyw{overloading} command.

\item
Derive the desired equation on \<open>un_D\<close> from the characteristic equations
for \<open>un_D\<^sub>0\<close>.
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
designed to be highly compatible with that for old, pre-Isabelle2015 datatypes,
to ease migration. There is nonetheless at least one incompatibility that may
arise when porting to the new package:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{Some theorems have different names.}
For $m > 1$ mutually recursive functions,
\<open>f\<^sub>1_\<dots>_f\<^sub>m.simps\<close> has been broken down into separate
subcollections \<open>f\<^sub>i.simps\<close>.
\end{itemize}
\<close>


section \<open>Defining Codatatypes
  \label{sec:defining-codatatypes}\<close>

text \<open>
Codatatypes can be specified using the @{command codatatype} command. The
command is first illustrated through concrete examples featuring different
flavors of corecursion. More examples can be found in the directory
\<^dir>\<open>~~/src/HOL/Datatype_Examples\<close>. The \emph{Archive of Formal Proofs} also
includes some useful codatatypes, notably for lazy lists \<^cite>\<open>"lochbihler-2010"\<close>.
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
Lazy lists can be infinite, such as \<open>LCons 0 (LCons 0 (\<dots>))\<close> and
\<open>LCons 0 (LCons 1 (LCons 2 (\<dots>)))\<close>. Here is a related type, that of
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
This type has exactly one infinite element, \<open>ESucc (ESucc (ESucc (\<dots>)))\<close>,
that represents $\infty$. In addition, it has finite values of the form
\<open>ESucc (\<dots> (ESucc EZero)\<dots>)\<close>.

Here is an example with many constructors:
\<close>

    codatatype 'a process =
      Fail
    | Skip (cont: "'a process")
    | Action (prefix: 'a) (cont: "'a process")
    | Choice (left: "'a process") (right: "'a process")

text \<open>
\noindent
Notice that the \<^const>\<open>cont\<close> selector is associated with both \<^const>\<open>Skip\<close>
and \<^const>\<open>Action\<close>.
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
  @{command_def "codatatype"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
  @@{command codatatype} target? @{syntax dt_options}? @{syntax dt_spec}
\<close>

\medskip

\noindent
Definitions of codatatypes have almost exactly the same syntax as for datatypes
(Section~\ref{ssec:datatype-command-syntax}). The \<open>discs_sels\<close> option
is superfluous because discriminators and selectors are always generated for
codatatypes.
\<close>


subsection \<open>Generated Constants
  \label{ssec:codatatype-generated-constants}\<close>

text \<open>
Given a codatatype \<open>('a\<^sub>1, \<dots>, 'a\<^sub>m) t\<close>
with $m > 0$ live type variables and $n$ constructors \<open>t.C\<^sub>1\<close>,
\ldots, \<open>t.C\<^sub>n\<close>, the same auxiliary constants are generated as for
datatypes (Section~\ref{ssec:datatype-generated-constants}), except that the
recursor is replaced by a dual concept:

\medskip

\begin{tabular}{@ {}ll@ {}}
Corecursor: &
  \<open>t.corec_t\<close>
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
The coinductive theorems are listed below for \<^typ>\<open>'a llist\<close>:

\begin{indentblock}
\begin{description}

\item[\begin{tabular}{@ {}l@ {}}
  \<open>t.\<close>\hthm{coinduct} \<open>[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>t.\<close>\hthm{coinduct} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n, coinduct t]\<close>\rm:
\end{tabular}] ~ \\
@{thm llist.coinduct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  \<open>t.\<close>\hthm{coinduct_strong} \<open>[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>t.\<close>\hthm{coinduct_strong} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots> D\<^sub>n]\<close>\rm:
\end{tabular}] ~ \\
@{thm llist.coinduct_strong[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  \<open>t.\<close>\hthm{rel_coinduct} \<open>[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>t.\<close>\hthm{rel_coinduct} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n, coinduct pred]\<close>\rm:
\end{tabular}] ~ \\
@{thm llist.rel_coinduct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  \<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{coinduct} \<open>[case_names t\<^sub>1 \<dots> t\<^sub>m, case_conclusion D\<^sub>1 \<dots> D\<^sub>n]\<close> \\
  \<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{coinduct_strong} \<open>[case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{coinduct_strong} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots> D\<^sub>n]\<close>\rm: \\
  \<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{rel_coinduct} \<open>[case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{rel_coinduct} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots> D\<^sub>n]\<close>\rm: \\
\end{tabular}] ~ \\
Given $m > 1$ mutually corecursive codatatypes, these coinduction rules can be
used to prove $m$ properties simultaneously.

\item[\begin{tabular}{@ {}l@ {}}
  \<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{set_induct} \<open>[case_names C\<^sub>1 \<dots> C\<^sub>n,\<close> \\
  \phantom{\<open>t\<^sub>1_\<dots>_t\<^sub>m.\<close>\hthm{set_induct} \<open>[\<close>}\<open>induct set: set\<^sub>j_t\<^sub>1, \<dots>, induct set: set\<^sub>j_t\<^sub>m]\<close>\rm: \\
\end{tabular}] ~ \\
@{thm llist.set_induct[no_vars]} \\
If $m = 1$, the attribute \<open>[consumes 1]\<close> is generated as well.

\item[\<open>t.\<close>\hthm{corec}\rm:] ~ \\
@{thm llist.corec(1)[no_vars]} \\
@{thm llist.corec(2)[no_vars]}

\item[\<open>t.\<close>\hthm{corec_code} \<open>[code]\<close>\rm:] ~ \\
@{thm llist.corec_code[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>t.\<close>\hthm{corec_disc}\rm:] ~ \\
@{thm llist.corec_disc(1)[no_vars]} \\
@{thm llist.corec_disc(2)[no_vars]}

\item[\<open>t.\<close>\hthm{corec_disc_iff} \<open>[simp]\<close>\rm:] ~ \\
@{thm llist.corec_disc_iff(1)[no_vars]} \\
@{thm llist.corec_disc_iff(2)[no_vars]}

\item[\<open>t.\<close>\hthm{corec_sel} \<open>[simp]\<close>\rm:] ~ \\
@{thm llist.corec_sel(1)[no_vars]} \\
@{thm llist.corec_sel(2)[no_vars]}

\item[\<open>t.\<close>\hthm{map_o_corec}\rm:] ~ \\
@{thm llist.map_o_corec[no_vars]}

\item[\<open>t.\<close>\hthm{corec_transfer} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm llist.corec_transfer[no_vars]} \\
The \<open>[transfer_rule]\<close> attribute is set by the \<open>transfer\<close> plugin
(Section~\ref{ssec:transfer}) for type constructors with no dead type arguments.

\end{description}
\end{indentblock}

\noindent
For convenience, @{command codatatype} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{simps}] = \<open>t.inject\<close> \<open>t.distinct\<close> \<open>t.case\<close> \<open>t.corec_disc_iff\<close> \<open>t.corec_sel\<close> \\
\<open>t.map\<close> \<open>t.rel_inject\<close> \<open>t.rel_distinct\<close> \<open>t.set\<close>

\end{description}
\end{indentblock}
\<close>


subsection \<open>Antiquotation
  \label{ssec:codatatype-antiquotation}\<close>

subsubsection \<open>\textit{codatatype}
  \label{sssec:codatatype-codatatype}\<close>

text \<open>
The \textit{codatatype} antiquotation, written
\texttt{\char`\\\char`<\char`^}\verb|codatatype>|\guilsinglleft\textit{t}\guilsinglright{}
or \texttt{@}\verb|{codatatype| \textit{t}\verb|}|, where \textit{t} is a type
name, expands to \LaTeX{} code for the definition of the codatatype, with each
constructor listed with its argument types. For example, if \textit{t} is
@{type llist}:

\begin{quote}
\<^codatatype>\<open>llist\<close>
\end{quote}
\<close>


section \<open>Defining Primitively Corecursive Functions
  \label{sec:defining-primitively-corecursive-functions}\<close>

text \<open>
Corecursive functions can be specified using the @{command primcorec} and
\keyw{prim\-corec\-ursive} commands, which support primitive corecursion.
Other approaches include the more general \keyw{partial_function} command, the
\keyw{corec} and \keyw{corecursive} commands, and techniques based on domains
and topologies \<^cite>\<open>"lochbihler-hoelzl-2014"\<close>. In this tutorial, the focus is
on @{command primcorec} and @{command primcorecursive}; \keyw{corec} and
\keyw{corecursive} are described in a separate tutorial
\<^cite>\<open>"isabelle-corec"\<close>. More examples can be found in the directories
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
\[\<open>\<dots> \<Longrightarrow> is_C\<^sub>j (f x\<^sub>1 \<dots> x\<^sub>n)\<close>\] and
equations of the form
\[\<open>un_C\<^sub>ji (f x\<^sub>1 \<dots> x\<^sub>n) = \<dots>\<close>\]
This style is popular in the coalgebraic literature.

\item The \emph{constructor view} specifies $f$ by equations of the form
\[\<open>\<dots> \<Longrightarrow> f x\<^sub>1 \<dots> x\<^sub>n = C\<^sub>j \<dots>\<close>\]
This style is often more concise than the previous one.

\item The \emph{code view} specifies $f$ by a single equation of the form
\[\<open>f x\<^sub>1 \<dots> x\<^sub>n = \<dots>\<close>\]
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
\<open>[x, g x, g (g x), \<dots>]\<close>. Productivity guarantees that prefixes
\<open>[x, g x, g (g x), \<dots>, (g ^^ k) x]\<close> of arbitrary finite length
\<open>k\<close> can be computed by unfolding the code equation a finite number of
times.

Corecursive functions construct codatatype values, but nothing prevents them
from also consuming such values. The following function drops every second
element in a stream:
\<close>

    primcorec every_snd :: "'a stream \<Rightarrow> 'a stream" where
      "every_snd s = SCons (shd s) (every_snd (stl (stl s)))"

text \<open>
\noindent
Constructs such as \<open>let\<close>--\<open>in\<close>, \<open>if\<close>--\<open>then\<close>--\<open>else\<close>, and \<open>case\<close>--\<open>of\<close> may
appear around constructors that guard corecursive calls:
\<close>

    primcorec lapp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lapp xs ys =
         (case xs of
            LNil \<Rightarrow> ys
          | LCons x xs' \<Rightarrow> LCons x (lapp xs' ys))"

text \<open>
\noindent
For technical reasons, \<open>case\<close>--\<open>of\<close> is only supported for
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
actions (\<open>s\<close>), a pseudorandom function generator (\<open>f\<close>), and a
pseudorandom seed (\<open>n\<close>):
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
The next pair of examples generalize the \<^const>\<open>literate\<close> and \<^const>\<open>siterate\<close>
functions (Section~\ref{sssec:primcorec-nested-corecursion}) to possibly
infinite trees in which subnodes are organized either as a lazy list (\<open>tree\<^sub>i\<^sub>i\<close>) or as a finite set (\<open>tree\<^sub>i\<^sub>s\<close>). They rely on the map functions of
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
\<^const>\<open>iterate\<^sub>i\<^sub>i\<close>. The term \<^term>\<open>g x\<close> constructs an \<^typ>\<open>'a llist\<close>
value, which is turned into an \<^typ>\<open>'a tree\<^sub>i\<^sub>i llist\<close> value using
\<^const>\<open>lmap\<close>.

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
5-tuples \<open>(Q, \<Sigma>, \<delta>, q\<^sub>0, F)\<close>, where \<open>Q\<close> is a finite set of states,
\<open>\<Sigma>\<close> is a finite alphabet, \<open>\<delta>\<close> is a transition function, \<open>q\<^sub>0\<close>
is an initial state, and \<open>F\<close> is a set of final states. The following
function translates a DFA into a state machine:
\<close>

    primcorec (*<*)(in early) (*>*)sm_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> 'a sm" where
      "sm_of_dfa \<delta> F q = SM (q \<in> F) (sm_of_dfa \<delta> F \<circ> \<delta> q)"

text \<open>
\noindent
The map function for the function type (\<open>\<Rightarrow>\<close>) is composition
(\<open>(\<circ>)\<close>). For convenience, corecursion through functions can
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
\<^term>\<open>(\<circ>)\<close> are necessary. The examples below illustrate the case where
$n = 2$:
\<close>

    codatatype ('a, 'b) sm2 =
      SM2 (accept2: bool) (trans2: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) sm2")

text \<open>\blankline\<close>

    primcorec
      (*<*)(in early) (*>*)sm2_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> ('a, 'b) sm2"
    where
      "sm2_of_dfa \<delta> F q = SM2 (q \<in> F) ((\<circ>) ((\<circ>) (sm2_of_dfa \<delta> F)) (\<delta> q))"

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
and analogously for \<open>coinduct_strong\<close>. These rules and the
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
equation. Examples that rely on a single constructor, such as \<^const>\<open>literate\<close>
and \<^const>\<open>siterate\<close>, are identical in both styles.

Here is an example where there is a difference:
\<close>

    primcorec lapp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lapp xs ys = LNil"
    | "_ \<Longrightarrow> lapp xs ys = LCons (lhd (if lnull xs then ys else xs))
         (if xs = LNil then ltl ys else lapp (ltl xs) ys)"

text \<open>
\noindent
With the constructor view, we must distinguish between the \<^const>\<open>LNil\<close> and
the \<^const>\<open>LCons\<close> case. The condition for \<^const>\<open>LCons\<close> is
left implicit, as the negation of that for \<^const>\<open>LNil\<close>.

For this example, the constructor view is slightly more involved than the
code equation. Recall the code view version presented in
Section~\ref{sssec:primcorec-simple-corecursion}.
% TODO: \[{thm code_view.lapp.code}\]
The constructor view requires us to analyze the second argument (\<^term>\<open>ys\<close>).
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
Since there is no sequentiality, we can apply the equation for \<^const>\<open>Choice\<close>
without having first to discharge \<^term>\<open>n mod (4::int) \<noteq> 0\<close>,
\<^term>\<open>n mod (4::int) \<noteq> 1\<close>, and
\<^term>\<open>n mod (4::int) \<noteq> 2\<close>.
The price to pay for this elegance is that we must discharge exclusiveness proof
obligations, one for each pair of conditions
\<^term>\<open>(n mod (4::int) = i, n mod (4::int) = j)\<close>
with \<^term>\<open>i < j\<close>. If we prefer not to discharge any obligations, we can
enable the \<open>sequential\<close> option. This pushes the problem to the users of
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
sequentially or not depending on the \<open>sequential\<close> option.
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
    | "stl (every_snd s) = every_snd (stl (stl s))"

text \<open>
\noindent
The first formula in the \<^const>\<open>literate\<close> specification indicates which
constructor to choose. For \<^const>\<open>siterate\<close> and \<^const>\<open>every_snd\<close>, no such
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
Using the \<open>of\<close> keyword, different equations are specified for \<^const>\<open>cont\<close> depending on which constructor is selected.

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
  @{command_def "primcorec"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  @{command_def "primcorecursive"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close>
\end{matharray}

\<^rail>\<open>
  (@@{command primcorec} | @@{command primcorecursive}) target? \<newline>
    @{syntax pcr_options}? fixes @'where' (@{syntax pcr_formula} + '|')
  ;
  @{syntax_def pcr_options}: '(' ((@{syntax plugins} | 'sequential' | 'exhaustive' | 'transfer') + ',') ')'
  ;
  @{syntax_def pcr_formula}: thmdecl? prop (@'of' (term * ))?
\<close>

\medskip

\noindent
The @{command primcorec} and @{command primcorecursive} commands introduce a set
of mutually corecursive functions over codatatypes.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{fixes} denotes a list of names with optional type signatures,
\synt{thmdecl} denotes an optional name for the formula that follows, and
\synt{prop} denotes a HOL proposition \<^cite>\<open>"isabelle-isar-ref"\<close>.

The optional target is optionally followed by a combination of the following
options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The \<open>plugins\<close> option indicates which plugins should be enabled
(\<open>only\<close>) or disabled (\<open>del\<close>). By default, all plugins are enabled.

\item
The \<open>sequential\<close> option indicates that the conditions in specifications
expressed using the constructor or destructor view are to be interpreted
sequentially.

\item
The \<open>exhaustive\<close> option indicates that the conditions in specifications
expressed using the constructor or destructor view cover all possible cases.
This generally gives rise to an additional proof obligation.

\item
The \<open>transfer\<close> option indicates that an unconditional transfer rule
should be generated and proved \<open>by transfer_prover\<close>. The
\<open>[transfer_rule]\<close> attribute is set on the generated theorem.
\end{itemize}

The @{command primcorec} command is an abbreviation for @{command
primcorecursive} with \<open>by auto?\<close> to discharge any emerging proof
obligations.

%%% TODO: elaborate on format of the propositions
%%% TODO: elaborate on mutual and nested-to-mutual
\<close>


subsection \<open>Generated Theorems
  \label{ssec:primcorec-generated-theorems}\<close>

text \<open>
The @{command primcorec} and @{command primcorecursive} commands generate the
following properties (listed for \<^const>\<open>literate\<close>):

\begin{indentblock}
\begin{description}

\item[\<open>f.\<close>\hthm{code} \<open>[code]\<close>\rm:] ~ \\
@{thm literate.code[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>f.\<close>\hthm{ctr}\rm:] ~ \\
@{thm literate.ctr[no_vars]}

\item[\<open>f.\<close>\hthm{disc} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm literate.disc[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}). The \<open>[simp]\<close> attribute is set only
for functions for which \<open>f.disc_iff\<close> is not available.

\item[\<open>f.\<close>\hthm{disc_iff} \<open>[simp]\<close>\rm:] ~ \\
@{thm literate.disc_iff[no_vars]} \\
This property is generated only for functions declared with the
\<open>exhaustive\<close> option or whose conditions are trivially exhaustive.

\item[\<open>f.\<close>\hthm{sel} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm literate.disc[no_vars]} \\
The \<open>[code]\<close> attribute is set by the \<open>code\<close> plugin
(Section~\ref{ssec:code-generator}).

\item[\<open>f.\<close>\hthm{exclude}\rm:] ~ \\
These properties are missing for \<^const>\<open>literate\<close> because no exclusiveness
proof obligations arose. In general, the properties correspond to the
discharged proof obligations.

\item[\<open>f.\<close>\hthm{exhaust}\rm:] ~ \\
This property is missing for \<^const>\<open>literate\<close> because no exhaustiveness
proof obligation arose. In general, the property correspond to the discharged
proof obligation.

\item[\begin{tabular}{@ {}l@ {}}
  \<open>f.\<close>\hthm{coinduct} \<open>[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>f.\<close>\hthm{coinduct} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]\<close>\rm:
\end{tabular}] ~ \\
This coinduction rule is generated for nested-as-mutual corecursive functions
(Section~\ref{sssec:primcorec-nested-as-mutual-corecursion}).

\item[\begin{tabular}{@ {}l@ {}}
  \<open>f.\<close>\hthm{coinduct_strong} \<open>[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>f.\<close>\hthm{coinduct_strong} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]\<close>\rm:
\end{tabular}] ~ \\
This coinduction rule is generated for nested-as-mutual corecursive functions
(Section~\ref{sssec:primcorec-nested-as-mutual-corecursion}).

\item[\begin{tabular}{@ {}l@ {}}
  \<open>f\<^sub>1_\<dots>_f\<^sub>m.\<close>\hthm{coinduct} \<open>[case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>f.\<close>\hthm{coinduct} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]\<close>\rm:
\end{tabular}] ~ \\
This coinduction rule is generated for nested-as-mutual corecursive functions
(Section~\ref{sssec:primcorec-nested-as-mutual-corecursion}). Given $m > 1$
mutually corecursive functions, this rule can be used to prove $m$ properties
simultaneously.

\item[\begin{tabular}{@ {}l@ {}}
  \<open>f\<^sub>1_\<dots>_f\<^sub>m.\<close>\hthm{coinduct_strong} \<open>[case_names t\<^sub>1 \<dots> t\<^sub>m,\<close> \\
  \phantom{\<open>f.\<close>\hthm{coinduct_strong} \<open>[\<close>}\<open>case_conclusion D\<^sub>1 \<dots>
  D\<^sub>n]\<close>\rm:
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

\item[\<open>f.\<close>\hthm{simps}] = \<open>f.disc_iff\<close> (or \<open>f.disc\<close>) \<open>t.sel\<close>

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
\<^cite>\<open>"traytel-et-al-2012" and "blanchette-et-al-2015-wit"\<close>.

An $n$-ary BNF is a type constructor equipped with a map function
(functorial action), $n$ set functions (natural transformations),
and an infinite cardinal bound that satisfy certain properties.
For example, \<^typ>\<open>'a llist\<close> is a unary BNF.
Its predicator \<open>llist_all ::
  ('a \<Rightarrow> bool) \<Rightarrow>
  'a llist \<Rightarrow> bool\<close>
extends unary predicates over elements to unary predicates over
lazy lists.
Similarly, its relator \<open>llist_all2 ::
  ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
  'a llist \<Rightarrow> 'b llist \<Rightarrow> bool\<close>
extends binary predicates over elements to binary predicates over parallel
lazy lists. The cardinal bound limits the number of elements returned by the
set function; it may not depend on the cardinality of \<^typ>\<open>'a\<close>.

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
command. Some of the proof obligations are best viewed with the bundle
"cardinal_syntax" included.

The type is simply a copy of the function space \<^typ>\<open>'d \<Rightarrow> 'a\<close>, where \<^typ>\<open>'a\<close>
is live and \<^typ>\<open>'d\<close> is dead. We introduce it together with its map function,
set function, predicator, and relator.
\<close>

    typedef ('d, 'a) fn = "UNIV :: ('d \<Rightarrow> 'a) set"
      by simp

text \<open>\blankline\<close>

    setup_lifting type_definition_fn

text \<open>\blankline\<close>

    lift_definition map_fn :: "('a \<Rightarrow> 'b) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn" is "(\<circ>)" .
    lift_definition set_fn :: "('d, 'a) fn \<Rightarrow> 'a set" is range .

text \<open>\blankline\<close>

    lift_definition
      pred_fn :: "('a \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fn \<Rightarrow> bool"
    is
      "pred_fun (\<lambda>_. True)" .

    lift_definition
      rel_fn :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn \<Rightarrow> bool"
    is
      "rel_fun (=)" .

text \<open>\blankline\<close>

    bnf "('d, 'a) fn"
      map: map_fn
      sets: set_fn
      bd: "natLeq +c card_suc |UNIV :: 'd set|"
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
      show "set_fn \<circ> map_fn f = (`) f \<circ> set_fn"
        by transfer (auto simp add: comp_def)
    next
      show "card_order (natLeq +c card_suc |UNIV :: 'd set| )"
        by (rule card_order_bd_fun)
    next
      show "cinfinite (natLeq +c card_suc |UNIV :: 'd set| )"
        by (rule Cinfinite_bd_fun[THEN conjunct1])
    next
      show "regularCard (natLeq +c card_suc |UNIV :: 'd set| )"
        by (rule regularCard_bd_fun)
    next
      fix F :: "('d, 'a) fn"
      have "|set_fn F| \<le>o |UNIV :: 'd set|" (is "_ \<le>o ?U")
        by transfer (rule card_of_image)
      also have "?U <o card_suc ?U"
        by (simp add: card_of_card_order_on card_suc_greater)
      also have "card_suc ?U \<le>o natLeq +c card_suc ?U"
        using Card_order_card_suc card_of_card_order_on ordLeq_csum2 by blast
      finally show "|set_fn F| <o natLeq +c card_suc |UNIV :: 'd set|" .
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

For many typedefs and quotient types, lifting the BNF structure from the raw typ
to the abstract type can be done uniformly. This is the task of the @{command lift_bnf}
command. Using @{command lift_bnf}, the above registration of \<^typ>\<open>('d, 'a) fn\<close> as a
BNF becomes much shorter:
\<close>

(*<*)
    context early
    begin
(*>*)
    lift_bnf (*<*)(no_warn_wits) (*>*)('d, 'a) fn
      by force+
(*<*)
    end
(*>*)

text \<open>
For type copies (@{command typedef}s with \<^term>\<open>UNIV\<close> as the representing set),
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

    copy_bnf (*<*)(no_warn_transfer) (*>*)('a, 'z) point_ext

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
\<^term>\<open>zs :: ('a \<times> 'b) list\<close>.
\<close>

    lift_bnf (*<*)(no_warn_wits,no_warn_transfer) (*>*)'a nonempty_list
    proof -
      fix f (*<*):: "'a \<Rightarrow> 'c"(*>*)and xs :: "'a list"
      assume "xs \<in> {xs. xs \<noteq> []}"
      then show "map f xs \<in> {xs. xs \<noteq> []}"
        by (cases xs(*<*) rule: list.exhaust(*>*)) auto
    next
      fix zs :: "('a \<times> 'b) list"
      assume "map fst zs \<in> {xs. xs \<noteq> []}" "map snd zs \<in> {xs. xs \<noteq> []}"
      then show "\<exists>zs'\<in>{xs. xs \<noteq> []}.
            set zs' \<subseteq> set zs \<and>
            map fst zs' = map fst zs \<and>
            map snd zs' = map snd zs"
        by (cases zs (*<*)rule: list.exhaust(*>*)) (auto intro!: exI[of _ zs])
    qed

text \<open>The @{command lift_bnf} command also supports quotient types. Here is an example
that defines the option type as a quotient of the sum type. The proof obligations
generated by @{command lift_bnf} for quotients are different from the ones for typedefs.
You can find additional examples of usages of @{command lift_bnf} for both quotients and subtypes
in the session \emph{HOL-Datatype_Examples}.\<close>

    inductive ignore_Inl :: "'a + 'a \<Rightarrow> 'a + 'a \<Rightarrow> bool" where
      "ignore_Inl (Inl x) (Inl y)"
    | "ignore_Inl (Inr x) (Inr x)"

    (*<*)
    inductive_simps ignore_Inl_simps[simp]:
      "ignore_Inl (Inl x) y"
      "ignore_Inl (Inr x') y"
      "ignore_Inl y (Inl x)"
      "ignore_Inl y (Inr x')"
    (*>*)

    lemma ignore_Inl_equivp:
      "ignore_Inl x x"
      "ignore_Inl x y \<Longrightarrow> ignore_Inl y x"
      "ignore_Inl x y \<Longrightarrow> ignore_Inl y z \<Longrightarrow> ignore_Inl x z"
      by (cases x; cases y; cases z; auto)+

    quotient_type 'a myoption = "'a + 'a" / ignore_Inl
      unfolding equivp_reflp_symp_transp reflp_def symp_def transp_def
      by (blast intro: ignore_Inl_equivp)

    lift_bnf 'a myoption (*<*)[wits: "Inl undefined :: 'a + 'a"](*>*)

    proof -
      fix P :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and Q :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
      assume "P OO Q \<noteq> bot"
      then show "rel_sum P P OO ignore_Inl OO rel_sum Q Q
         \<le> ignore_Inl OO rel_sum (P OO Q) (P OO Q) OO ignore_Inl"
        by (fastforce(*<*) elim!: ignore_Inl.cases simp add: relcompp_apply fun_eq_iff rel_sum.simps(*>*))
    next
      fix S :: "'a set set"
      let ?eq = "{(x, x'). ignore_Inl x x'}"
      let ?in = "\<lambda>A. {x. Basic_BNFs.setl x \<union> Basic_BNFs.setr x \<subseteq> A}"
      assume "S \<noteq> {}" "\<Inter> S \<noteq> {}"
      show "(\<Inter>A\<in>S. ?eq `` ?in A) \<subseteq> ?eq `` ?in (\<Inter> S)"
      proof (intro subsetI)
        fix x
        assume "x \<in> (\<Inter>A\<in>S. ?eq `` ?in A)"
        with \<open>\<Inter> S \<noteq> {}\<close> show "x \<in> ?eq `` ?in (\<Inter> S)"
          by (cases x) (fastforce(*<*) dest!: spec[where x="Inl _"](*>*))+
      qed
    (*<*)next
      fix a :: 'a
      assume "a \<in> (\<Inter>mx\<in>{mx. ignore_Inl (map_sum Inr Inr (Inl undefined)) mx}.
        \<Union> (Basic_BNFs.setr ` (Basic_BNFs.setl mx \<union> Basic_BNFs.setr mx)))"
      then show False
        by (auto simp: setr.simps)(*>*)
    qed


text \<open>
The next example declares a BNF axiomatically. This can be convenient for
reasoning abstractly about an arbitrary BNF. The @{command bnf_axiomatization}
command below introduces a type \<open>('a, 'b, 'c) F\<close>, three set constants,
a map function, a predicator, a relator, and a nonemptiness witness that depends only on
\<^typ>\<open>'a\<close>. The type \<open>'a \<Rightarrow> ('a, 'b, 'c) F\<close> of the witness can be read
as an implication: Given a witness for \<^typ>\<open>'a\<close>, we can construct a witness for
\<open>('a, 'b, 'c) F\<close>. The BNF properties are postulated as axioms.
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
  @{command_def "bnf"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close>
\end{matharray}

\<^rail>\<open>
  @@{command bnf} target? (name ':')? type \<newline>
    'map:' term ('sets:' (term +))? 'bd:' term \<newline>
    ('wits:' (term +))? ('rel:' term)? \<newline>
    ('pred:' term)? @{syntax plugins}?
\<close>

\medskip

\noindent
The @{command bnf} command registers an existing type as a bounded natural
functor (BNF). The type must be equipped with an appropriate map function
(functorial action). In addition, custom set functions, predicators, relators, and
nonemptiness witnesses can be specified; otherwise, default versions are used.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{type} denotes a HOL type, and \synt{term} denotes a HOL term
\<^cite>\<open>"isabelle-isar-ref"\<close>.

The @{syntax plugins} option indicates which plugins should be enabled
(\<open>only\<close>) or disabled (\<open>del\<close>). By default, all plugins are enabled.

%%% TODO: elaborate on proof obligations
\<close>

subsubsection \<open>\keyw{lift_bnf}
  \label{sssec:lift-bnf}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "lift_bnf"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close>
\end{matharray}

\<^rail>\<open>
  @@{command lift_bnf} target? lb_options? \<newline>
    @{syntax tyargs} name wit_terms?  \<newline>
    ('via' thm thm?)? @{syntax map_rel_pred}?
  ;
  @{syntax_def lb_options}: '(' ((@{syntax plugins} | 'no_warn_wits' | 'no_warn_transfer') + ',') ')'
  ;
  @{syntax_def wit_terms}: '[' 'wits' ':' terms ']'
\<close>
\medskip

\noindent
The @{command lift_bnf} command registers as a BNF an existing type (the
\emph{abstract type}) that was defined as a subtype of a BNF (the \emph{raw
type}) using the @{command typedef} command or as a quotient type of a BNF (also, the
\emph{raw type}) using the @{command quotient_type}. To achieve this, it lifts the BNF
structure on the raw type to the abstract type following a \<^term>\<open>type_definition\<close> or a
\<^term>\<open>Quotient\<close> theorem. The theorem is usually inferred from the type, but can
also be explicitly supplied by means of the optional \<open>via\<close> clause. In case of quotients, it
is sometimes also necessary to supply a second theorem of the form \<^term>\<open>reflp eq\<close>,
that expresses the reflexivity (and thus totality) of the equivalence relation. In
addition, custom names for the set functions, the map function, the predicator, and the relator,
as well as nonemptiness witnesses can be specified.

Nonemptiness witnesses are not lifted from the raw type's BNF, as this would be
incomplete. They must be given as terms (on the raw type) and proved to be
witnesses. The command warns about witness types that are present in the raw
type's BNF but not supplied by the user. The warning can be disabled by
specifying the \<open>no_warn_wits\<close> option.
\<close>

subsubsection \<open>\keyw{copy_bnf}
  \label{sssec:copy-bnf}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "copy_bnf"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
  @@{command copy_bnf} target? cb_options? \<newline>
    @{syntax tyargs} name ('via' thm)? @{syntax map_rel_pred}?
  ;
  @{syntax_def cb_options}: '(' ((@{syntax plugins} | 'no_warn_transfer') + ',') ')'

\<close>
\medskip

\noindent
The @{command copy_bnf} command performs the same lifting as @{command lift_bnf}
for type copies (@{command typedef}s with \<^term>\<open>UNIV\<close> as the representing set),
without requiring the user to discharge any proof obligations or provide
nonemptiness witnesses.
\<close>

subsubsection \<open>\keyw{bnf_axiomatization}
  \label{sssec:bnf-axiomatization}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "bnf_axiomatization"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
  @@{command bnf_axiomatization} target? ('(' @{syntax plugins} ')')? \<newline>
    @{syntax tyargs}? name @{syntax wit_types}? \<newline>
    mixfix? @{syntax map_rel_pred}?
  ;
  @{syntax_def wit_types}: '[' 'wits' ':' types ']'
\<close>

\medskip

\noindent
The @{command bnf_axiomatization} command declares a new type and associated constants
(map, set, predicator, relator, and cardinal bound) and asserts the BNF properties for
these constants as axioms.

The syntactic entity \synt{target} can be used to specify a local context,
\synt{name} denotes an identifier, \synt{typefree} denotes fixed type variable
(\<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close>, \ldots), \synt{mixfix} denotes the usual parenthesized
mixfix notation, and \synt{types} denotes a space-separated list of types
\<^cite>\<open>"isabelle-isar-ref"\<close>.

The @{syntax plugins} option indicates which plugins should be enabled
(\<open>only\<close>) or disabled (\<open>del\<close>). By default, all plugins are enabled.

Type arguments are live by default; they can be marked as dead by entering
\<open>dead\<close> in front of the type variable (e.g., \<open>(dead 'a)\<close>)
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
  @{command_def "print_bnfs"} & : & \<open>local_theory \<rightarrow>\<close>
\end{matharray}

\<^rail>\<open>
  @@{command print_bnfs}
\<close>
\<close>


section \<open>Deriving Destructors and Constructor Theorems
  \label{sec:deriving-destructors-and-constructor-theorems}\<close>

text \<open>
The derivation of convenience theorems for types equipped with free constructors,
as performed internally by @{command datatype} and @{command codatatype},
is available as a stand-alone command called @{command free_constructors}.

%  * need for this is rare but may arise if you want e.g. to add destructors to
%    a type not introduced by ...
%
%  * @{command free_constructors}
%    * \<open>plugins\<close>, \<open>discs_sels\<close>
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
  @{command_def "free_constructors"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close>
\end{matharray}

\<^rail>\<open>
  @@{command free_constructors} target? @{syntax dt_options} \<newline>
    name 'for' (@{syntax fc_ctor} + '|') \<newline>
  (@'where' (prop + '|'))?
  ;
  @{syntax_def fc_ctor}: (name ':')? term (name * )
\<close>

\medskip

\noindent
The @{command free_constructors} command generates destructor constants for
freely constructed types as well as properties about constructors and
destructors. It also registers the constants and theorems in a data structure
that is queried by various tools (e.g., \keyw{function}).

The syntactic entity \synt{target} can be used to specify a local context,
\synt{name} denotes an identifier, \synt{prop} denotes a HOL proposition, and
\synt{term} denotes a HOL term \<^cite>\<open>"isabelle-isar-ref"\<close>.

The syntax resembles that of @{command datatype} and @{command codatatype}
definitions (Sections
\ref{ssec:datatype-command-syntax}~and~\ref{ssec:codatatype-command-syntax}).
A constructor is specified by an optional name for the discriminator, the
constructor itself (as a term), and a list of optional names for the selectors.

Section~\ref{ssec:datatype-generated-theorems} lists the generated theorems.
For bootstrapping reasons, the generally useful \<open>[fundef_cong]\<close>
attribute is not set on the generated \<open>case_cong\<close> theorem. It can be
added manually using \keyw{declare}.
\<close>


subsubsection \<open>\keyw{simps_of_case}
  \label{sssec:simps-of-case}\<close>

text \<open>
\begin{matharray}{rcl}
  @{command_def "simps_of_case"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
  @@{command simps_of_case} target? (name ':')? \<newline>
    (thm + ) (@'splits' ':' (thm + ))?
\<close>

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
  @{command_def "case_of_simps"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

\<^rail>\<open>
  @@{command case_of_simps} target? (name ':')? \<newline>
    (thm + )
\<close>

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
\<^cite>\<open>"sternagel-thiemann-2015"\<close>.
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

\item[\<open>t.\<close>\hthm{eq.refl} \<open>[code nbe]\<close>\rm:] ~ \\
@{thm list.eq.refl[no_vars]}

\item[\<open>t.\<close>\hthm{eq.simps} \<open>[code]\<close>\rm:] ~ \\
@{thm list.eq.simps(1)[no_vars]} \\
@{thm list.eq.simps(2)[no_vars]} \\
@{thm list.eq.simps(3)[no_vars]} \\
@{thm list.eq.simps(4)[no_vars]} \\
@{thm list.eq.simps(5)[no_vars]} \\
@{thm list.eq.simps(6)[no_vars]}

\end{description}
\end{indentblock}

In addition, the plugin sets the \<open>[code]\<close> attribute on a number of
properties of freely generated types and of (co)recursive functions, as
documented in Sections \ref{ssec:datatype-generated-theorems},
\ref{ssec:primrec-generated-theorems}, \ref{ssec:codatatype-generated-theorems},
and~\ref{ssec:primcorec-generated-theorems}.
\<close>


subsection \<open>Size
  \label{ssec:size}\<close>

text \<open>
For each datatype \<open>t\<close>, the \hthm{size} plugin generates a generic size
function \<open>t.size_t\<close> as well as a specific instance
\<open>size :: t \<Rightarrow> nat\<close> belonging to the \<open>size\<close> type class. The
\keyw{fun} command relies on \<^const>\<open>size\<close> to prove termination of recursive
functions on datatypes.

The plugin derives the following properties:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{size} \<open>[simp, code]\<close>\rm:] ~ \\
@{thm list.size(1)[no_vars]} \\
@{thm list.size(2)[no_vars]} \\
@{thm list.size(3)[no_vars]} \\
@{thm list.size(4)[no_vars]}

\item[\<open>t.\<close>\hthm{size_gen}\rm:] ~ \\
@{thm list.size_gen(1)[no_vars]} \\
@{thm list.size_gen(2)[no_vars]}

\item[\<open>t.\<close>\hthm{size_gen_o_map}\rm:] ~ \\
@{thm list.size_gen_o_map[no_vars]}

\item[\<open>t.\<close>\hthm{size_neq}\rm:] ~ \\
This property is missing for \<^typ>\<open>'a list\<close>. If the \<^term>\<open>size\<close> function
always evaluates to a non-zero value, this theorem has the form
\<^prop>\<open>\<not> size x = 0\<close>.

\end{description}
\end{indentblock}

The \<open>t.size\<close> and \<open>t.size_t\<close> functions generated for datatypes
defined by nested recursion through a datatype \<open>u\<close> depend on
\<open>u.size_u\<close>.

If the recursion is through a non-datatype \<open>u\<close> with type arguments
\<open>'a\<^sub>1, \<dots>, 'a\<^sub>m\<close>, by default \<open>u\<close> values are given a size of 0. This
can be improved upon by registering a custom size function of type
\<open>('a\<^sub>1 \<Rightarrow> nat) \<Rightarrow> \<dots> \<Rightarrow> ('a\<^sub>m \<Rightarrow> nat) \<Rightarrow> u \<Rightarrow> nat\<close> using
the ML function \<^ML>\<open>BNF_LFP_Size.register_size\<close> or
\<^ML>\<open>BNF_LFP_Size.register_size_global\<close>. See theory
\<^file>\<open>~~/src/HOL/Library/Multiset.thy\<close> for an example.
\<close>


subsection \<open>Transfer
  \label{ssec:transfer}\<close>

text \<open>
For each (co)datatype with live type arguments and each manually registered BNF,
the \hthm{transfer} plugin generates a predicator \<open>t.pred_t\<close> and
properties that guide the Transfer tool.

For types with at least one live type argument and \emph{no dead type
arguments}, the plugin derives the following properties:

\begin{indentblock}
\begin{description}

\item[\<open>t.\<close>\hthm{Domainp_rel} \<open>[relator_domain]\<close>\rm:] ~ \\
@{thm list.Domainp_rel[no_vars]}

\item[\<open>t.\<close>\hthm{left_total_rel} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.left_total_rel[no_vars]}

\item[\<open>t.\<close>\hthm{left_unique_rel} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.left_unique_rel[no_vars]}

\item[\<open>t.\<close>\hthm{right_total_rel} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.right_total_rel[no_vars]}

\item[\<open>t.\<close>\hthm{right_unique_rel} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.right_unique_rel[no_vars]}

\item[\<open>t.\<close>\hthm{bi_total_rel} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.bi_total_rel[no_vars]}

\item[\<open>t.\<close>\hthm{bi_unique_rel} \<open>[transfer_rule]\<close>\rm:] ~ \\
@{thm list.bi_unique_rel[no_vars]}

\end{description}
\end{indentblock}

For (co)datatypes with at least one live type argument, the plugin sets the
\<open>[transfer_rule]\<close> attribute on the following (co)datatypes properties:
\<open>t.case_\<close>\allowbreak \<open>transfer\<close>,
\<open>t.sel_\<close>\allowbreak \<open>transfer\<close>,
\<open>t.ctr_\<close>\allowbreak \<open>transfer\<close>,
\<open>t.disc_\<close>\allowbreak \<open>transfer\<close>,
\<open>t.rec_\<close>\allowbreak \<open>transfer\<close>, and
\<open>t.corec_\<close>\allowbreak \<open>transfer\<close>.
For (co)datatypes that further have \emph{no dead type arguments}, the plugin
sets \<open>[transfer_rule]\<close> on
\<open>t.set_\<close>\allowbreak \<open>transfer\<close>,
\<open>t.map_\<close>\allowbreak \<open>transfer\<close>, and
\<open>t.rel_\<close>\allowbreak \<open>transfer\<close>.

For @{command primrec}, @{command primcorec}, and @{command primcorecursive},
the plugin implements the generation of the \<open>f.transfer\<close> property,
conditioned by the \<open>transfer\<close> option, and sets the
\<open>[transfer_rule]\<close> attribute on these.
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

\item[\<open>t.\<close>\hthm{Quotient} \<open>[quot_map]\<close>\rm:] ~ \\
@{thm list.Quotient[no_vars]}

\end{description}
\end{indentblock}

In addition, the plugin sets the \<open>[relator_eq]\<close> attribute on a
variant of the \<open>t.rel_eq_onp\<close> property, the \<open>[relator_mono]\<close>
attribute on \<open>t.rel_mono\<close>, and the \<open>[relator_distr]\<close> attribute
on \<open>t.rel_compp\<close>.
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
\<open>case\<close>--\<open>of\<close> for datatypes that are defined without
discriminators and selectors.}

\item
\emph{There is no way to use an overloaded constant from a syntactic type
class, such as \<open>0\<close>, as a constructor.}

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
Kun\v{c}ar implemented the \<open>transfer\<close> and \<open>lifting\<close> plugins.
Christian Sternagel and Ren\'e Thiemann ported the \keyw{derive} command
from the \emph{Archive of Formal Proofs} to the new datatypes. Gerwin Klein and
Lars Noschinski implemented the @{command simps_of_case} and @{command
case_of_simps} commands. Florian Haftmann, Christian Urban, and Makarius
Wenzel provided general advice on Isabelle and package writing. Stefan Milius
and Lutz Schröder found an elegant proof that eliminated one of the BNF
proof obligations. Mamoun Filali-Amine, Gerwin Klein, Andreas Lochbihler,
Tobias Nipkow, and Christian Sternagel suggested many textual improvements to
this tutorial.
\<close>

end
