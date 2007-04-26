(* $Id$ *)

(*<*)
theory Codegen
imports Main
uses "../../../antiquote_setup.ML"
begin

ML {*
CodegenSerializer.code_width := 74;
*}

(*>*)

chapter {* Code generation from Isabelle theories *}

section {* Introduction *}

subsection {* Motivation *}

text {*
  Executing formal specifications as programs is a well-established
  topic in the theorem proving community.  With increasing
  application of theorem proving systems in the area of
  software development and verification, its relevance manifests
  for running test cases and rapid prototyping.  In logical
  calculi like constructive type theory,
  a notion of executability is implicit due to the nature
  of the calculus.  In contrast, specifications in Isabelle
  can be highly non-executable.  In order to bridge
  the gap between logic and executable specifications,
  an explicit non-trivial transformation has to be applied:
  code generation.

  This tutorial introduces a generic code generator for the
  Isabelle system \cite{isa-tutorial}.
  Generic in the sense that the
  \qn{target language} for which code shall ultimately be
  generated is not fixed but may be an arbitrary state-of-the-art
  functional programming language (currently, the implementation
  supports SML \cite{SML}, OCaml \cite{OCaml} and Haskell
  \cite{haskell-revised-report}).
  We aim to provide a
  versatile environment
  suitable for software development and verification,
  structuring the process
  of code generation into a small set of orthogonal principles
  while achieving a big coverage of application areas
  with maximum flexibility.

  Conceptually the code generator framework is part
  of Isabelle's @{text Pure} meta logic; the object logic
  @{text HOL} which is an extension of @{text Pure}
  already comes with a reasonable framework setup and thus provides
  a good working horse for raising code-generation-driven
  applications.  So, we assume some familiarity and experience
  with the ingredients of the @{text HOL} \emph{Main} theory
  (see also \cite{isa-tutorial}).
*}


subsection {* Overview *}

text {*
  The code generator aims to be usable with no further ado
  in most cases while allowing for detailed customization.
  This manifests in the structure of this tutorial:
  we start with a generic example \secref{sec:example}
  and introduce code generation concepts \secref{sec:concept}.
  Section
  \secref{sec:basics} explains how to use the framework naively,
  presuming a reasonable default setup.  Then, section
  \secref{sec:advanced} deals with advanced topics,
  introducing further aspects of the code generator framework
  in a motivation-driven manner.  Last, section \secref{sec:ml}
  introduces the framework's internal programming interfaces.

  \begin{warn}
    Ultimately, the code generator which this tutorial deals with
    is supposed to replace the already established code generator
    by Stefan Berghofer \cite{Berghofer-Nipkow:2002}.
    So, for the moment, there are two distinct code generators
    in Isabelle.
    Also note that while the framework itself is largely
    object-logic independent, only @{text HOL} provides a reasonable
    framework setup.    
  \end{warn}
*}


section {* An example: a simple theory of search trees \label{sec:example} *}

text {*
  When writing executable specifications, it is convenient to use
  three existing packages: the datatype package for defining
  datatypes, the function package for (recursive) functions,
  and the class package for overloaded definitions.

  We develope a small theory of search trees; trees are represented
  as a datatype with key type @{typ "'a"} and value type @{typ "'b"}:
*}

datatype ('a, 'b) searchtree = Leaf "'a\<Colon>linorder" 'b
  | Branch "('a, 'b) searchtree" "'a" "('a, 'b) searchtree"

text {*
  \noindent Note that we have constrained the type of keys
  to the class of total orders, @{text linorder}.

  We define @{text find} and @{text update} functions:
*}

fun
  find :: "('a\<Colon>linorder, 'b) searchtree \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "find (Leaf key val) it = (if it = key then Some val else None)"
  | "find (Branch t1 key t2) it = (if it \<le> key then find t1 it else find t2 it)"

fun
  update :: "'a\<Colon>linorder \<times> 'b \<Rightarrow> ('a, 'b) searchtree \<Rightarrow> ('a, 'b) searchtree" where
  "update (it, entry) (Leaf key val) = (
    if it = key then Leaf key entry
      else if it \<le> key
      then Branch (Leaf it entry) it (Leaf key val)
      else Branch (Leaf key val) it (Leaf it entry)
   )"
  | "update (it, entry) (Branch t1 key t2) = (
    if it \<le> key
      then (Branch (update (it, entry) t1) key t2)
      else (Branch t1 key (update (it, entry) t2))
   )"

text {*
  \noindent For testing purpose, we define a small example
  using natural numbers @{typ nat} (which are a @{text linorder})
  as keys and strings values:
*}

fun
  example :: "nat \<Rightarrow> (nat, string) searchtree" where
  "example n = update (n, ''bar'') (Leaf 0 ''foo'')"

text {*
  \noindent Then we generate code
*}

code_gen example (*<*)(SML #)(*>*)(SML "examples/tree.ML")

text {*
  \noindent which looks like:
  \lstsml{Thy/examples/tree.ML}
*}


section {* Code generation concepts and process \label{sec:concept} *}

text {*
  \begin{figure}[h]
  \centering
  \includegraphics[width=0.7\textwidth]{codegen_process}
  \caption{code generator -- processing overview}
  \label{fig:process}
  \end{figure}

  The code generator employs a notion of executability
  for three foundational executable ingredients known
  from functional programming:
  \emph{defining equations}, \emph{datatypes}, and
  \emph{type classes}. A defining equation as a first approximation
  is a theorem of the form @{text "f t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n \<equiv> t"}
  (an equation headed by a constant @{text f} with arguments
  @{text "t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n"} and right hand side @{text t}).
  Code generation aims to turn defining equations
  into a functional program by running through
  a process (see figure \ref{fig:process}):

  \begin{itemize}

    \item Out of the vast collection of theorems proven in a
      \qn{theory}, a reasonable subset modeling
      defining equations is \qn{selected}.

    \item On those selected theorems, certain
      transformations are carried out
      (\qn{preprocessing}).  Their purpose is to turn theorems
      representing non- or badly executable
      specifications into equivalent but executable counterparts.
      The result is a structured collection of \qn{code theorems}.

    \item These \qn{code theorems} then are \qn{translated}
      into an Haskell-like intermediate
      language.

    \item Finally, out of the intermediate language the final
      code in the desired \qn{target language} is \qn{serialized}.

  \end{itemize}

  From these steps, only the two last are carried out
  outside the logic; by keeping this layer as
  thin as possible, the amount of code to trust is
  kept to a minimum.
*}



section {* Basics \label{sec:basics} *}

subsection {* Invoking the code generator *}

text {*
  Thanks to a reasonable setup of the HOL theories, in
  most cases code generation proceeds without further ado:
*}

fun
  fac :: "nat \<Rightarrow> nat" where
    "fac 0 = 1"
  | "fac (Suc n) = Suc n * fac n"

text {*
  \noindent This executable specification is now turned to SML code:
*}

code_gen fac (*<*)(SML #)(*>*)(SML "examples/fac.ML")

text {*
  \noindent  The @{text "\<CODEGEN>"} command takes a space-separated list of
  constants together with \qn{serialization directives}
  in parentheses. These start with a \qn{target language}
  identifier, followed by arguments, their semantics
  depending on the target. In the SML case, a filename
  is given where to write the generated code to.

  Internally, the defining equations for all selected
  constants are taken, including any transitively required
  constants, datatypes and classes, resulting in the following
  code:

  \lstsml{Thy/examples/fac.ML}

  The code generator will complain when a required
  ingredient does not provide a executable counterpart,
  e.g.~generating code
  for constants not yielding
  a defining equation (e.g.~the Hilbert choice
  operation @{text "SOME"}):
*}
(*<*)
setup {* Sign.add_path "foo" *}
(*>*)
definition
  pick_some :: "'a list \<Rightarrow> 'a" where
  "pick_some xs = (SOME x. x \<in> set xs)"
(*<*)
hide const pick_some

setup {* Sign.parent_path *}

definition
  pick_some :: "'a list \<Rightarrow> 'a" where
  "pick_some = hd"
(*>*)
code_gen pick_some (SML "examples/fail_const.ML")

text {* \noindent will fail. *}

subsection {* Theorem selection *}

text {*
  The list of all defining equations in a theory may be inspected
  using the @{text "\<PRINTCODESETUP>"} command:
*}

print_codesetup

text {*
  \noindent which displays a table of constant with corresponding
  defining equations (the additional stuff displayed
  shall not bother us for the moment).

  The typical HOL tools are already set up in a way that
  function definitions introduced by @{text "\<DEFINITION>"},
  @{text "\<FUN>"},
  @{text "\<FUNCTION>"}, @{text "\<PRIMREC>"},
  @{text "\<RECDEF>"} are implicitly propagated
  to this defining equation table. Specific theorems may be
  selected using an attribute: \emph{code func}. As example,
  a weight selector function:
*}

consts
  pick :: "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> 'a"

primrec
  "pick (x#xs) n = (let (k, v) = x in
    if n < k then v else pick xs (n - k))"

text {*
  \noindent We want to eliminate the explicit destruction
  of @{term x} to @{term "(k, v)"}:
*}

lemma [code func]:
  "pick ((k, v)#xs) n = (if n < k then v else pick xs (n - k))"
  by simp

code_gen pick (*<*)(SML #)(*>*)(SML "examples/pick1.ML")

text {*
  \noindent This theorem now is used for generating code:

  \lstsml{Thy/examples/pick1.ML}

  \noindent It might be convenient to remove the pointless original
  equation, using the \emph{nofunc} attribute:
*}

lemmas [code nofunc] = pick.simps 

code_gen pick (*<*)(SML #)(*>*)(SML "examples/pick2.ML")

text {*
  \lstsml{Thy/examples/pick2.ML}

  \noindent Syntactic redundancies are implicitly dropped. For example,
  using a modified version of the @{const fac} function
  as defining equation, the then redundant (since
  syntactically subsumed) original defining equations
  are dropped, resulting in a warning:
*}

lemma [code func]:
  "fac n = (case n of 0 \<Rightarrow> 1 | Suc m \<Rightarrow> n * fac m)"
  by (cases n) simp_all

code_gen fac (*<*)(SML #)(*>*)(SML "examples/fac_case.ML")

text {*
  \lstsml{Thy/examples/fac_case.ML}

  \begin{warn}
    The attributes \emph{code} and \emph{code del}
    associated with the existing code generator also apply to
    the new one: \emph{code} implies \emph{code func},
    and \emph{code del} implies \emph{code nofunc}.
  \end{warn}
*}

subsection {* Type classes *}

text {*
  Type classes enter the game via the Isar class package.
  For a short introduction how to use it, see \cite{isabelle-classes};
  here we just illustrate its impact on code generation.

  In a target language, type classes may be represented
  natively (as in the case of Haskell).  For languages
  like SML, they are implemented using \emph{dictionaries}.
  Our following example specifies a class \qt{null},
  assigning to each of its inhabitants a \qt{null} value:
*}

class null = type +
  fixes null :: 'a

fun
  head :: "'a\<Colon>null list \<Rightarrow> 'a"
where
  "head [] = null"
  | "head (x#xs) = x"

text {*
  We provide some instances for our @{text null}:
*}

instance option :: (type) null
  "null \<equiv> None" ..

instance list :: (type) null
  "null \<equiv> []" ..

text {*
  Constructing a dummy example:
*}

definition
  "dummy = head [Some (Suc 0), None]"

text {*
  Type classes offer a suitable occasion to introduce
  the Haskell serializer.  Its usage is almost the same
  as SML, but, in accordance with conventions
  some Haskell systems enforce, each module ends
  up in a single file. The module hierarchy is reflected in
  the file system, with root given by the user.
*}

code_gen dummy (Haskell "examples/")
  (* NOTE: you may use Haskell only once in this document, otherwise
  you have to work in distinct subdirectories *)

text {*
  \lsthaskell{Thy/examples/Codegen.hs}
  \noindent (we have left out all other modules).

  \medskip

  The whole code in SML with explicit dictionary passing:
*}

code_gen dummy (*<*)(SML #)(*>*)(SML "examples/class.ML")

text {*
  \lstsml{Thy/examples/class.ML}

  \medskip

  \noindent or in OCaml:
*}

code_gen dummy (OCaml "examples/class.ocaml")

text {*
  \lstsml{Thy/examples/class.ocaml}

  \medskip The explicit association of constants
  to classes can be inspected using the @{text "\<PRINTCLASSES>"}
*}


section {* Recipes and advanced topics \label{sec:advanced} *}

text {*
  In this tutorial, we do not attempt to give an exhaustive
  description of the code generator framework; instead,
  we cast a light on advanced topics by introducing
  them together with practically motivated examples.  Concerning
  further reading, see

  \begin{itemize}

  \item the Isabelle/Isar Reference Manual \cite{isabelle-isar-ref}
    for exhaustive syntax diagrams.
  \item or \fixme[ref] which deals with foundational issues
    of the code generator framework.

  \end{itemize}
*}

subsection {* Library theories \label{sec:library} *}

text {*
  The HOL \emph{Main} theory already provides a code generator setup
  which should be suitable for most applications. Common extensions
  and modifications are available by certain theories of the HOL
  library; beside being useful in applications, they may serve
  as a tutorial for customizing the code generator setup.

  \begin{description}

    \item[@{text "Pretty_Int"}] represents HOL integers by big
       integer literals in target languages.
    \item[@{text "Pretty_Char"}] represents HOL characters by 
       character literals in target languages.
    \item[@{text "Pretty_Char_chr"}] like @{text "Pretty_Char_chr"},
       but also offers treatment of character codes; includes
       @{text "Pretty_Int"}.
    \item[@{text "ExecutableSet"}] allows to generate code
       for finite sets using lists.
    \item[@{text "ExecutableRat"}] \label{exec_rat} implements rational
       numbers as triples @{text "(sign, enumerator, denominator)"}.
    \item[@{text "EfficientNat"}] \label{eff_nat} implements natural numbers by integers,
       which in general will result in higher efficency; pattern
       matching with @{const "0\<Colon>nat"} / @{const "Suc"}
       is eliminated;  includes @{text "Pretty_Int"}.
    \item[@{text "MLString"}] provides an additional datatype @{text "mlstring"};
       in the HOL default setup, strings in HOL are mapped to list
       of HOL characters in SML; values of type @{text "mlstring"} are
       mapped to strings in SML.

  \end{description}
*}

subsection {* Preprocessing *}

text {*
  Before selected function theorems are turned into abstract
  code, a chain of definitional transformation steps is carried
  out: \emph{preprocessing}. There are three possibilities
  to customize preprocessing: \emph{inline theorems},
  \emph{inline procedures} and \emph{generic preprocessors}.

  \emph{Inline theorems} are rewriting rules applied to each
  defining equation.  Due to the interpretation of theorems
  of defining equations, rewrites are applied to the right
  hand side and the arguments of the left hand side of an
  equation, but never to the constant heading the left hand side.
  Inline theorems may be declared an undeclared using the
  \emph{code inline} or \emph{code noinline} attribute respectively.
  Some common applications:
*}

text_raw {*
  \begin{itemize}
     \item replacing non-executable constructs by executable ones: \\
*}     

lemma [code inline]:
  "x \<in> set xs \<longleftrightarrow> x mem xs" by (induct xs) simp_all

text_raw {*
     \item eliminating superfluous constants: \\
*}

lemma [code inline]:
  "1 = Suc 0" by simp

text_raw {*
     \item replacing executable but inconvenient constructs: \\
*}

lemma [code inline]:
  "xs = [] \<longleftrightarrow> List.null xs" by (induct xs) simp_all

text_raw {*
  \end{itemize}
*}

text {*
  The current set of inline theorems may be inspected using
  the @{text "\<PRINTCODESETUP>"} command.

  \emph{Inline procedures} are a generalized version of inline
  theorems written in ML -- rewrite rules are generated dependent
  on the function theorems for a certain function.  One
  application is the implicit expanding of @{typ nat} numerals
  to @{const "0\<Colon>nat"} / @{const Suc} representation.  See further
  \secref{sec:ml}

  \emph{Generic preprocessors} provide a most general interface,
  transforming a list of function theorems to another
  list of function theorems, provided that neither the heading
  constant nor its type change.  The @{const "0\<Colon>nat"} / @{const Suc}
  pattern elimination implemented in
  theory @{text "EfficientNat"} (\secref{eff_nat}) uses this
  interface.

  \begin{warn}
    The order in which single preprocessing steps are carried
    out currently is not specified; in particular, preprocessing
    is \emph{no} fix point process.  Keep this in mind when
    setting up the preprocessor.

    Further, the attribute \emph{code unfold}
    associated with the existing code generator also applies to
    the new one: \emph{code unfold} implies \emph{code inline}.
  \end{warn}
*}


subsection {* Concerning operational equality *}

text {*
  Surely you have already noticed how equality is treated
  by the code generator:
*}

fun
  collect_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "collect_duplicates xs ys [] = xs"
  | "collect_duplicates xs ys (z#zs) = (if z \<in> set xs
      then if z \<in> set ys
        then collect_duplicates xs ys zs
        else collect_duplicates xs (z#ys) zs
      else collect_duplicates (z#xs) (z#ys) zs)"

text {*
  The membership test during preprocessing is rewritten,
  resulting in @{const List.memberl}, which itself
  performs an explicit equality check.
*}

code_gen collect_duplicates (*<*)(SML #)(*>*)(SML "examples/collect_duplicates.ML")

text {*
  \lstsml{Thy/examples/collect_duplicates.ML}
*}

text {*
  Obviously, polymorphic equality is implemented the Haskell
  way using a type class.  How is this achieved?  By an
  almost trivial definition in the HOL setup:
*}
(*<*)
setup {* Sign.add_path "foo" *}
consts "op =" :: "'a"
(*>*)
class eq (attach "op =") = type

text {*
  This merely introduces a class @{text eq} with corresponding
  operation @{text "op ="};
  the preprocessing framework does the rest.
  For datatypes, instances of @{text eq} are implicitly derived
  when possible.

  Though this @{text eq} class is designed to get rarely in
  the way, a subtlety
  enters the stage when definitions of overloaded constants
  are dependent on operational equality.  For example, let
  us define a lexicographic ordering on tuples:
*}
(*<*)
hide (open) "class" eq
hide (open) const "op ="
setup {* Sign.parent_path *}
(*>*)
instance * :: (ord, ord) ord
  less_prod_def:
    "p1 < p2 \<equiv> let (x1 \<Colon> 'a\<Colon>ord, y1 \<Colon> 'b\<Colon>ord) = p1; (x2, y2) = p2 in
    x1 < x2 \<or> (x1 = x2 \<and> y1 < y2)"
  less_eq_prod_def:
    "p1 \<le> p2 \<equiv> let (x1 \<Colon> 'a\<Colon>ord, y1 \<Colon> 'b\<Colon>ord) = p1; (x2, y2) = p2 in
    x1 < x2 \<or> (x1 = x2 \<and> y1 \<le> y2)" ..

lemmas [code nofunc] = less_prod_def less_eq_prod_def

lemma ord_prod [code func(*<*), code nofunc(*>*)]:
  "(x1 \<Colon> 'a\<Colon>ord, y1 \<Colon> 'b\<Colon>ord) < (x2, y2) \<longleftrightarrow> x1 < x2 \<or> (x1 = x2 \<and> y1 < y2)"
  "(x1 \<Colon> 'a\<Colon>ord, y1 \<Colon> 'b\<Colon>ord) \<le> (x2, y2) \<longleftrightarrow> x1 < x2 \<or> (x1 = x2 \<and> y1 \<le> y2)"
  unfolding less_prod_def less_eq_prod_def by simp_all

text {*
  Then code generation will fail.  Why?  The definition
  of @{const "op \<le>"} depends on equality on both arguments,
  which are polymorphic and impose an additional @{text eq}
  class constraint, thus violating the type discipline
  for class operations.

  The solution is to add @{text eq} explicitly to the first sort arguments in the
  code theorems:
*}

lemma ord_prod_code [code func]:
  "(x1 \<Colon> 'a\<Colon>{ord, eq}, y1 \<Colon> 'b\<Colon>ord) < (x2, y2) \<longleftrightarrow>
    x1 < x2 \<or> (x1 = x2 \<and> y1 < y2)"
  "(x1 \<Colon> 'a\<Colon>{ord, eq}, y1 \<Colon> 'b\<Colon>ord) \<le> (x2, y2) \<longleftrightarrow>
    x1 < x2 \<or> (x1 = x2 \<and> y1 \<le> y2)"
  unfolding ord_prod by rule+

text {*
  \noindent Then code generation succeeds:
*}

code_gen "op \<le> \<Colon> 'a\<Colon>{eq, ord} \<times> 'b\<Colon>ord \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  (*<*)(SML #)(*>*)(SML "examples/lexicographic.ML")

text {*
  \lstsml{Thy/examples/lexicographic.ML}
*}

text {*
  In general, code theorems for overloaded constants may have more
  restrictive sort constraints than the underlying instance relation
  between class and type constructor as long as the whole system of
  constraints is coregular; code theorems violating coregularity
  are rejected immediately.  Consequently, it might be necessary
  to delete disturbing theorems in the code theorem table,
  as we have done here with the original definitions @{text less_prod_def}
  and @{text less_eq_prod_def}.
*}


subsection {* Programs as sets of theorems *}

text {*
  As told in \secref{sec:concept}, code generation is based
  on a structured collection of code theorems.
  For explorative purpose, this collection
  may be inspected using the @{text "\<CODETHMS>"} command:
*}

code_thms "op mod :: nat \<Rightarrow> nat \<Rightarrow> nat"

text {*
  \noindent prints a table with \emph{all} defining equations
  for @{const "op mod :: nat \<Rightarrow> nat \<Rightarrow> nat"}, including
  \emph{all} defining equations those equations depend
  on recursivly.  @{text "\<CODETHMS>"} provides a convenient
  mechanism to inspect the impact of a preprocessor setup
  on defining equations.
  
  Similarly, the @{text "\<CODEDEPS>"} command shows a graph
  visualizing dependencies between defining equations.
*}


subsection {* Customizing serialization  *}

subsubsection {* Basics *}

text {*
  Consider the following function and its corresponding
  SML code:
*}

fun
  in_interval :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "in_interval (k, l) n \<longleftrightarrow> k \<le> n \<and> n \<le> l"
(*<*)
code_type %tt bool
  (SML)
code_const %tt True and False and "op \<and>" and Not
  (SML and and and)
(*>*)
code_gen in_interval (*<*)(SML #)(*>*)(SML "examples/bool_literal.ML")

text {*
  \lstsml{Thy/examples/bool_literal.ML}

  \noindent Though this is correct code, it is a little bit unsatisfactory:
  boolean values and operators are materialized as distinguished
  entities with have nothing to do with the SML-builtin notion
  of \qt{bool}.  This results in less readable code;
  additionally, eager evaluation may cause programs to
  loop or break which would perfectly terminate when
  the existing SML \qt{bool} would be used.  To map
  the HOL \qt{bool} on SML \qt{bool}, we may use
  \qn{custom serializations}:
*}

code_type %tt bool
  (SML "bool")
code_const %tt True and False and "op \<and>"
  (SML "true" and "false" and "_ andalso _")

text {*
  The @{text "\<CODETYPE>"} commad takes a type constructor
  as arguments together with a list of custom serializations.
  Each custom serialization starts with a target language
  identifier followed by an expression, which during
  code serialization is inserted whenever the type constructor
  would occur.  For constants, @{text "\<CODECONST>"} implements
  the corresponding mechanism.  Each ``@{verbatim "_"}'' in
  a serialization expression is treated as a placeholder
  for the type constructor's (the constant's) arguments.
*}

code_reserved SML
  bool true false

text {*
  To assert that the existing \qt{bool}, \qt{true} and \qt{false}
  is not used for generated code, we use @{text "\<CODERESERVED>"}.

  After this setup, code looks quite more readable:
*}

code_gen in_interval (*<*)(SML #)(*>*)(SML "examples/bool_mlbool.ML")

text {*
  \lstsml{Thy/examples/bool_mlbool.ML}

  \noindent This still is not perfect: the parentheses
  around the \qt{andalso} expression are superfluous.
  Though the serializer
  by no means attempts to imitate the rich Isabelle syntax
  framework, it provides some common idioms, notably
  associative infixes with precedences which may be used here:
*}

code_const %tt "op \<and>"
  (SML infixl 1 "andalso")

code_gen in_interval (*<*)(SML #)(*>*)(SML "examples/bool_infix.ML")

text {*
  \lstsml{Thy/examples/bool_infix.ML}

  \medskip

  Next, we try to map HOL pairs to SML pairs, using the
  infix ``@{verbatim "*"}'' type constructor and parentheses:
*}
(*<*)
code_type *
  (SML)
code_const Pair
  (SML)
(*>*)
code_type %tt *
  (SML infix 2 "*")
code_const %tt Pair
  (SML "!((_),/ (_))")

text {*
  The initial bang ``@{verbatim "!"}'' tells the serializer to never put
  parentheses around the whole expression (they are already present),
  while the parentheses around argument place holders
  tell not to put parentheses around the arguments.
  The slash ``@{verbatim "/"}'' (followed by arbitrary white space)
  inserts a space which may be used as a break if necessary
  during pretty printing.

  These examples give a glimpse what mechanisms
  custom serializations provide; however their usage
  requires careful thinking in order not to introduce
  inconsistencies -- or, in other words:
  custom serializations are completely axiomatic.

  A further noteworthy details is that any special
  character in a custom serialization may be quoted
  using ``@{verbatim "'"}''; thus, in
  ``@{verbatim "fn '_ => _"}'' the first
  ``@{verbatim "_"}'' is a proper underscore while the
  second ``@{verbatim "_"}'' is a placeholder.

  The HOL theories provide further
  examples for custom serializations and form
  a recommended tutorial on how to use them properly.
*}


subsubsection {* Haskell serialization *}

text {*
  For convenience, the default
  HOL setup for Haskell maps the @{text eq} class to
  its counterpart in Haskell, giving custom serializations
  for the class (@{text "\<CODECLASS>"}) and its operation:
*}

code_class %tt eq
  (Haskell "Eq" where "op =" \<equiv> "(==)")

code_const %tt "op ="
  (Haskell infixl 4 "==")

text {*
  A problem now occurs whenever a type which
  is an instance of @{text eq} in HOL is mapped
  on a Haskell-builtin type which is also an instance
  of Haskell @{text Eq}:
*}

typedecl bar

instance bar :: eq ..

code_type %tt bar
  (Haskell "Integer")

text {*
  The code generator would produce
  an additional instance, which of course is rejected.
  To suppress this additional instance, use
  @{text "\<CODEINSTANCE>"}:
*}

code_instance %tt bar :: eq
  (Haskell -)


subsubsection {* Pretty printing *}

text {*
  The serializer provides ML interfaces to set up
  pretty serializations for expressions like lists, numerals
  and characters;  these are
  monolithic stubs and should only be used with the
  theories introduces in \secref{sec:library}.
*}

subsection {* Constructor sets for datatypes *}

text {*
  Conceptually, any datatype is spanned by a set of
  \emph{constructors} of type @{text "\<tau> = \<dots> \<Rightarrow> \<kappa> \<alpha>\<^isub>1 \<dots> \<alpha>\<^isub>n"}
  where @{text "{\<alpha>\<^isub>1, \<dots>, \<alpha>\<^isub>n}"} is excactly the set of \emph{all}
  type variables in @{text "\<tau>"}.  The HOL datatype package
  by default registers any new datatype in the table
  of datatypes, which may be inspected using
  the @{text "\<PRINTCODESETUP>"} command.

  In some cases, it may be convenient to alter or
  extend this table;  as an example, we show
  how to implement finite sets by lists
  using the conversion @{term [source] "set \<Colon> 'a list \<Rightarrow> 'a set"}
  as constructor:
*}

code_datatype set

lemma [code func]: "{} = set []" by simp

lemma [code func]: "insert x (set xs) = set (x#xs)" by simp

lemma [code func]: "x \<in> set xs \<longleftrightarrow> x mem xs" by (induct xs) simp_all

lemma [code func]: "xs \<union> set ys = foldr insert ys xs" by (induct ys) simp_all

lemma [code func]: "\<Union>set xs = foldr (op \<union>) xs {}" by (induct xs) simp_all

code_gen "{}" insert "op \<in>" "op \<union>" "Union" (*<*)(SML #)(*>*)(SML "examples/set_list.ML")

text {*
  \lstsml{Thy/examples/set_list.ML}

  \medskip

  Changing the representation of existing datatypes requires
  some care with respect to pattern matching and such.
*}

subsection {* Cyclic module dependencies *}

text {*
  Sometimes the awkward situation occurs that dependencies
  between definitions introduce cyclic dependencies
  between modules, which in the Haskell world leaves
  you to the mercy of the Haskell implementation you are using,
  while for SML code generation is not possible.

  A solution is to declare module names explicitly.
  Let use assume the three cyclically dependent
  modules are named \emph{A}, \emph{B} and \emph{C}.
  Then, by stating
*}

code_modulename SML
  A ABC
  B ABC
  C ABC

text {*
  we explicitly map all those modules on \emph{ABC},
  resulting in an ad-hoc merge of this three modules
  at serialization time.
*}

subsection {* Incremental code generation *}

text {*
  Code generation is \emph{incremental}: theorems
  and abstract intermediate code are cached and extended on demand.
  The cache may be partially or fully dropped if the underlying
  executable content of the theory changes.
  Implementation of caching is supposed to transparently
  hid away the details from the user.  Anyway, caching
  reaches the surface by using a slightly more general form
  of the @{text "\<CODETHMS>"}, @{text "\<CODEDEPS>"}
  and @{text "\<CODEGEN>"} commands: the list of constants
  may be omitted.  Then, all constants with code theorems
  in the current cache are referred to.
*}

subsection {* Axiomatic extensions *}

text {*
  \begin{warn}
    The extensions introduced in this section, though working
    in practice, are not the cream of the crop, as you
    will notice during reading.  They will
    eventually be replaced by more mature approaches.
  \end{warn}

  Sometimes equalities are taken for granted which are
  not derivable inside the HOL logic but are silently assumed
  to hold for executable code.  For example, we may want
  to identify the famous HOL constant @{const arbitrary}
  of type @{typ "'a option"} with @{const None}.
  By brute force:
*}

axiomatization where
  "arbitrary = None"

text {*
  However this has to be considered harmful since this axiom,
  though probably justifiable for generated code, could
  introduce serious inconsistencies into the logic.

  So, there is a distinguished construct for stating axiomatic
  equalities of constants which apply only for code generation.
  Before introducing this, here is a convenient place to describe
  shortly how to deal with some restrictions the type discipline
  imposes.

  By itself, the constant @{const arbitrary} is a non-overloaded
  polymorphic constant.  So, there is no way to distinguish
  different versions of @{const arbitrary} for different types
  inside the code generator framework.  However, inlining
  theorems together with auxiliary constants provide a solution:
*}

definition
  arbitrary_option :: "'a option" where
  [symmetric, code inline]: "arbitrary_option = arbitrary"

text {*
  By that, we replace any @{const arbitrary} with option type
  by @{const arbitrary_option} in defining equations.

  For technical reasons, we further have to provide a
  synonym for @{const None} which in code generator view
  is a function rather than a term constructor:
*}

definition
  "None' = None"

text {*
  Then finally we are enabled to use @{text "\<CODEAXIOMS>"}:
*}

code_axioms
  arbitrary_option \<equiv> None'

text {*
  A dummy example:
*}

fun
  dummy_option :: "'a list \<Rightarrow> 'a option" where
    "dummy_option (x#xs) = Some x"
  | "dummy_option [] = arbitrary"

code_gen dummy_option (*<*)(SML #)(*>*)(SML "examples/arbitrary.ML")

text {*
  \lstsml{Thy/examples/arbitrary.ML}

  \medskip

  Another axiomatic extension is code generation
  for abstracted types.  For this, the  
  @{text "ExecutableRat"} (see \secref{exec_rat})
  forms a good example.
*}


section {* ML interfaces \label{sec:ml} *}

text {*
  Since the code generator framework not only aims to provide
  a nice Isar interface but also to form a base for
  code-generation-based applications, here a short
  description of the most important ML interfaces.
*}

subsection {* Constants with type discipline: codegen\_consts.ML *}

text {*
  This Pure module manages identification of (probably overloaded)
  constants by unique identifiers.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type CodegenConsts.const: "string * string option"} \\
  @{index_ML CodegenConsts.const_of_cexpr: "theory -> string * typ -> CodegenConsts.const"} \\
 \end{mldecls}

  \begin{description}

  \item @{ML_type CodegenConsts.const} is the identifier type:
     the product of a \emph{string} with a list of \emph{typs}.
     The \emph{string} is the constant name as represented inside Isabelle;
     for overloaded constants, the attached \emph{string option}
     is either @{text SOME} type constructor denoting an instance,
     or @{text NONE} for the polymorphic constant.

  \item @{ML CodegenConsts.const_of_cexpr}~@{text thy}~@{text "(constname, typ)"}
     maps a constant expression @{text "(constname, typ)"}
     to its canonical identifier.

  \end{description}
*}

subsection {* Executable theory content: codegen\_data.ML *}

text {*
  This Pure module implements the core notions of
  executable content of a theory.
*}

subsubsection {* Suspended theorems *}

text %mlref {*
  \begin{mldecls}
  @{index_ML CodegenData.lazy_thms: "(unit -> thm list) -> thm list Susp.T"}
  \end{mldecls}

  \begin{description}

  \item @{ML CodegenData.lazy_thms}~@{text f} turns an abstract
     theorem computation @{text f} into a suspension of theorems.

  \end{description}
*}

subsubsection {* Managing executable content *}

text %mlref {*
  \begin{mldecls}
  @{index_ML CodegenData.add_func: "bool -> thm -> theory -> theory"} \\
  @{index_ML CodegenData.del_func: "thm -> theory -> theory"} \\
  @{index_ML CodegenData.add_funcl: "CodegenConsts.const * thm list Susp.T -> theory -> theory"} \\
  @{index_ML CodegenData.add_inline: "thm -> theory -> theory"} \\
  @{index_ML CodegenData.del_inline: "thm -> theory -> theory"} \\
  @{index_ML CodegenData.add_inline_proc: "string * (theory -> cterm list -> thm list)
    -> theory -> theory"} \\
  @{index_ML CodegenData.del_inline_proc: "string -> theory -> theory"} \\
  @{index_ML CodegenData.add_preproc: "string * (theory -> thm list -> thm list)
    -> theory -> theory"} \\
  @{index_ML CodegenData.del_preproc: "string -> theory -> theory"} \\
  @{index_ML CodegenData.add_datatype: "string * ((string * sort) list * (string * typ list) list)
    -> theory -> theory"} \\
  @{index_ML CodegenData.get_datatype: "theory -> string
    -> (string * sort) list * (string * typ list) list"} \\
  @{index_ML CodegenData.get_datatype_of_constr: "theory -> CodegenConsts.const -> string option"}
  \end{mldecls}

  \begin{description}

  \item @{ML CodegenData.add_func}~@{text "thm"}~@{text "thy"} adds function
     theorem @{text "thm"} to executable content.

  \item @{ML CodegenData.del_func}~@{text "thm"}~@{text "thy"} removes function
     theorem @{text "thm"} from executable content, if present.

  \item @{ML CodegenData.add_funcl}~@{text "(const, lthms)"}~@{text "thy"} adds
     suspended defining equations @{text lthms} for constant
     @{text const} to executable content.

  \item @{ML CodegenData.add_inline}~@{text "thm"}~@{text "thy"} adds
     inlining theorem @{text thm} to executable content.

  \item @{ML CodegenData.del_inline}~@{text "thm"}~@{text "thy"} remove
     inlining theorem @{text thm} from executable content, if present.

  \item @{ML CodegenData.add_inline_proc}~@{text "(name, f)"}~@{text "thy"} adds
     inline procedure @{text f} (named @{text name}) to executable content;
     @{text f} is a computation of rewrite rules dependent on
     the current theory context and the list of all arguments
     and right hand sides of the defining equations belonging
     to a certain function definition.

  \item @{ML CodegenData.del_inline_proc}~@{text "name"}~@{text "thy"} removes
     inline procedure named @{text name} from executable content.

  \item @{ML CodegenData.add_preproc}~@{text "(name, f)"}~@{text "thy"} adds
     generic preprocessor @{text f} (named @{text name}) to executable content;
     @{text f} is a transformation of the defining equations belonging
     to a certain function definition, depending on the
     current theory context.

  \item @{ML CodegenData.del_preproc}~@{text "name"}~@{text "thy"} removes
     generic preprcoessor named @{text name} from executable content.

  \item @{ML CodegenData.add_datatype}~@{text "(name, spec)"}~@{text "thy"} adds
     a datatype to executable content, with type constructor
     @{text name} and specification @{text spec}; @{text spec} is
     a pair consisting of a list of type variable with sort
     constraints and a list of constructors with name
     and types of arguments.

  \item @{ML CodegenData.get_datatype_of_constr}~@{text "thy"}~@{text "const"}
     returns type constructor corresponding to
     constructor @{text const}; returns @{text NONE}
     if @{text const} is no constructor.

  \end{description}
*}

subsection {* Auxiliary *}

text %mlref {*
  \begin{mldecls}
  @{index_ML CodegenConsts.const_ord: "CodegenConsts.const * CodegenConsts.const -> order"} \\
  @{index_ML CodegenConsts.eq_const: "CodegenConsts.const * CodegenConsts.const -> bool"} \\
  @{index_ML CodegenConsts.read_const: "theory -> string -> CodegenConsts.const"} \\
  @{index_ML_structure CodegenConsts.Consttab} \\
  @{index_ML CodegenFunc.head_func: "thm -> CodegenConsts.const * typ"} \\
  @{index_ML CodegenFunc.rewrite_func: "thm list -> thm -> thm"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML CodegenConsts.const_ord},~@{ML CodegenConsts.eq_const}
     provide order and equality on constant identifiers.

  \item @{ML_struct CodegenConsts.Consttab}
     provides table structures with constant identifiers as keys.

  \item @{ML CodegenConsts.read_const}~@{text thy}~@{text s}
     reads a constant as a concrete term expression @{text s}.

  \item @{ML CodegenFunc.head_func}~@{text thm}
     extracts the constant and its type from a defining equation @{text thm}.

  \item @{ML CodegenFunc.rewrite_func}~@{text rews}~@{text thm}
     rewrites a defining equation @{text thm} with a set of rewrite
     rules @{text rews}; only arguments and right hand side are rewritten,
     not the head of the defining equation.

  \end{description}

*}

subsection {* Implementing code generator applications *}

text {*
  Implementing code generator applications on top
  of the framework set out so far usually not only
  involves using those primitive interfaces
  but also storing code-dependent data and various
  other things.

  \begin{warn}
    Some interfaces discussed here have not reached
    a final state yet.
    Changes likely to occur in future.
  \end{warn}
*}

subsubsection {* Data depending on the theory's executable content *}

text {*
  Due to incrementality of code generation, changes in the
  theory's executable content have to be propagated in a
  certain fashion.  Additionally, such changes may occur
  not only during theory extension but also during theory
  merge, which is a little bit nasty from an implementation
  point of view.  The framework provides a solution
  to this technical challenge by providing a functorial
  data slot @{ML_functor CodeDataFun}; on instantiation
  of this functor, the following types and operations
  are required:

  \medskip
  \begin{tabular}{l}
  @{text "val name: string"} \\
  @{text "type T"} \\
  @{text "val empty: T"} \\
  @{text "val merge: Pretty.pp \<rightarrow> T * T \<rightarrow> T"} \\
  @{text "val purge: theory option \<rightarrow> CodegenConsts.const list option \<rightarrow> T \<rightarrow> T"}
  \end{tabular}

  \begin{description}

  \item @{text name} is a system-wide unique name identifying the data.

  \item @{text T} the type of data to store.

  \item @{text empty} initial (empty) data.

  \item @{text merge} merging two data slots.

  \item @{text purge}~@{text thy}~@{text consts} propagates changes in executable content;
    if possible, the current theory context is handed over
    as argument @{text thy} (if there is no current theory context (e.g.~during
    theory merge, @{ML NONE}); @{text consts} indicates the kind
    of change: @{ML NONE} stands for a fundamental change
    which invalidates any existing code, @{text "SOME consts"}
    hints that executable content for constants @{text consts}
    has changed.

  \end{description}

  An instance of @{ML_functor CodeDataFun} provides the following
  interface:

  \medskip
  \begin{tabular}{l}
  @{text "init: theory \<rightarrow> theory"} \\
  @{text "get: theory \<rightarrow> T"} \\
  @{text "change: theory \<rightarrow> (T \<rightarrow> T) \<rightarrow> T"} \\
  @{text "change_yield: theory \<rightarrow> (T \<rightarrow> 'a * T) \<rightarrow> 'a * T"}
  \end{tabular}

  \begin{description}

  \item @{text init} initialization during theory setup.

  \item @{text get} retrieval of the current data.

  \item @{text change} update of current data (cached!)
    by giving a continuation.

  \item @{text change_yield} update with side result.

  \end{description}
*}

subsubsection {* Building implementable systems fo defining equations *}

text {*
  Out of the executable content of a theory, a normalized
  defining equation systems may be constructed containing
  function definitions for constants.  The system is cached
  until its underlying executable content changes.

  Defining equations are retrieved by instantiation
  of the functor @{ML_functor CodegenFuncgrRetrieval}
  which takes two arguments:

  \medskip
  \begin{tabular}{l}
  @{text "val name: string"} \\
  @{text "val rewrites: theory \<rightarrow> thm list"}
  \end{tabular}

  \begin{description}

  \item @{text name} is a system-wide unique name identifying
    this particular system of defining equations.

  \item @{text rewrites} specifies a set of theory-dependent
    rewrite rules which are added to the preprocessor setup;
    if no additional preprocessing is required, pass
    a function returning an empty list.

  \end{description}

  An instance of @{ML_functor CodegenFuncgrRetrieval} in essence
  provides the following interface:

  \medskip
  \begin{tabular}{l}
  @{text "make: theory \<rightarrow> CodegenConsts.const list \<rightarrow> CodegenFuncgr.T"} \\
  \end{tabular}

  \begin{description}

  \item @{text make}~@{text thy}~@{text consts} returns
    a system of defining equations which is guaranteed
    to contain all defining equations for constants @{text consts}
    including all defining equations any defining equation
    for any constant in @{text consts} depends on.

  \end{description}

  Systems of defining equations are graphs accesible by the
  following operations:
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type CodegenFuncgr.T} \\
  @{index_ML CodegenFuncgr.funcs: "CodegenFuncgr.T -> CodegenConsts.const -> thm list"} \\
  @{index_ML CodegenFuncgr.typ: "CodegenFuncgr.T -> CodegenConsts.const -> typ"} \\
  @{index_ML CodegenFuncgr.deps: "CodegenFuncgr.T
    -> CodegenConsts.const list -> CodegenConsts.const list list"} \\
  @{index_ML CodegenFuncgr.all: "CodegenFuncgr.T -> CodegenConsts.const list"}
  \end{mldecls}

  \begin{description}

  \item @{ML_type CodegenFuncgr.T} represents
    a normalized defining equation system.

  \item @{ML CodegenFuncgr.funcs}~@{text funcgr}~@{text const}
    retrieves defining equiations for constant @{text const}.

  \item @{ML CodegenFuncgr.typ}~@{text funcgr}~@{text const}
    retrieves function type for constant @{text const}.

  \item @{ML CodegenFuncgr.deps}~@{text funcgr}~@{text consts}
    returns the transitive closure of dependencies for
    constants @{text consts} as a partitioning where each partition
    corresponds to a strongly connected component of
    dependencies and any partition does \emph{not}
    depend on partitions further left.

  \item @{ML CodegenFuncgr.all}~@{text funcgr}
    returns all currently represented constants.

  \end{description}
*}

subsubsection {* Datatype hooks *}

text {*
  Isabelle/HOL's datatype package provides a mechanism to
  extend theories depending on datatype declarations:
  \emph{datatype hooks}.  For example, when declaring a new
  datatype, a hook proves defining equations for equality on
  that datatype (if possible).
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type DatatypeHooks.hook: "string list -> theory -> theory"} \\
  @{index_ML DatatypeHooks.add: "DatatypeHooks.hook -> theory -> theory"}
  \end{mldecls}

  \begin{description}

  \item @{ML_type DatatypeHooks.hook} specifies the interface
     of \emph{datatype hooks}: a theory update
     depending on the list of newly introduced
     datatype names.

  \item @{ML DatatypeHooks.add} adds a hook to the
     chain of all hooks.

  \end{description}
*}

subsubsection {* Trivial typedefs -- type copies *}

text {*
  Sometimes packages will introduce new types
  as \emph{marked type copies} similar to Haskell's
  @{text newtype} declaration (e.g. the HOL record package)
  \emph{without} tinkering with the overhead of datatypes.
  Technically, these type copies are trivial forms of typedefs.
  Since these type copies in code generation view are nothing
  else than datatypes, they have been given a own package
  in order to faciliate code generation:
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type TypecopyPackage.info} \\
  @{index_ML TypecopyPackage.add_typecopy: "
    bstring * string list -> typ -> (bstring * bstring) option
    -> theory -> (string * TypecopyPackage.info) * theory"} \\
  @{index_ML TypecopyPackage.get_typecopy_info: "theory
    -> string -> TypecopyPackage.info option"} \\
  @{index_ML TypecopyPackage.get_spec: "theory -> string
    -> (string * sort) list * (string * typ list) list"} \\
  @{index_ML_type TypecopyPackage.hook: "string * TypecopyPackage.info -> theory -> theory"} \\
  @{index_ML TypecopyPackage.add_hook:
     "TypecopyPackage.hook -> theory -> theory"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type TypecopyPackage.info} a record containing
     the specification and further data of a type copy.

  \item @{ML TypecopyPackage.add_typecopy} defines a new
     type copy.

  \item @{ML TypecopyPackage.get_typecopy_info} retrieves
     data of an existing type copy.

  \item @{ML TypecopyPackage.get_spec} retrieves datatype-like
     specification of a type copy.

  \item @{ML_type TypecopyPackage.hook},~@{ML TypecopyPackage.add_hook}
     provide a hook mechanism corresponding to the hook mechanism
     on datatypes.

  \end{description}
*}

subsubsection {* Unifying type copies and datatypes *}

text {*
  Since datatypes and type copies are mapped to the same concept (datatypes)
  by code generation, the view on both is unified \qt{code types}:
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type DatatypeCodegen.hook: "(string * (bool * ((string * sort) list
    * (string * typ list) list))) list
    -> theory -> theory"} \\
  @{index_ML DatatypeCodegen.add_codetypes_hook_bootstrap: "
      DatatypeCodegen.hook -> theory -> theory"}
  \end{mldecls}
*}

text {*
  \begin{description}

  \item @{ML_type DatatypeCodegen.hook} specifies the code type hook
     interface: a theory transformation depending on a list of
     mutual recursive code types; each entry in the list
     has the structure @{text "(name, (is_data, (vars, cons)))"}
     where @{text name} is the name of the code type, @{text is_data}
     is true iff @{text name} is a datatype rather then a type copy,
     and @{text "(vars, cons)"} is the specification of the code type.

  \item @{ML DatatypeCodegen.add_codetypes_hook_bootstrap} adds a code
     type hook;  the hook is immediately processed for all already
     existing datatypes, in blocks of mutual recursive datatypes,
     where all datatypes a block depends on are processed before
     the block.

  \end{description}

  \emph{Happy proving, happy hacking!}
*}

end
