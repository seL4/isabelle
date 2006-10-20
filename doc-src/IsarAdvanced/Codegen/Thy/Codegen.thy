
(* $Id$ *)

theory Codegen
imports Main
begin

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
  of the calculus.  In contrast, specifications in Isabelle/HOL
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
  supports SML \cite{web:sml} and Haskell \cite{web:haskell}).
  We aim to provide a
  versatile environment
  suitable for software development and verification,
  structuring the process
  of code generation into a small set of orthogonal principles
  while achieving a big coverage of application areas
  with maximum flexibility.
*}


subsection {* Overview *}

text {*
  The code generator aims to be usable with no further ado
  in most cases while allowing for detailed customization.
  This manifests in the structure of this tutorial: this introduction
  continous with a short introduction of concepts.  Section
  \secref{sec:basics} explains how to use the framework naivly,
  presuming a reasonable default setup.  Then, section
  \secref{sec:advanced} deals with advanced topics,
  introducing further aspects of the code generator framework
  in a motivation-driven manner.  Last, section \secref{sec:ml}
  introduces the framework's internal programming interfaces.

  \begin{warn}
    Ultimately, the code generator which this tutorial deals with
    is supposed to replace the already established code generator
    by Stefan Berghofer \cite{Berghofer-Nipkow:2002}.
    So, for the momennt, there are two distinct code generators
    in Isabelle.
    Also note that while the framework itself is largely
    object-logic independent, only HOL provides a reasonable
    framework setup.    
  \end{warn}
*}


subsection {* Code generation process *}

text {*
  The code generator employs a notion of executability
  for three foundational executable ingredients known
  from functional programming:
  \emph{function equations}, \emph{datatypes}, and
  \emph{type classes}. A function equation as a first approximation
  is a theorem of the form @{text "f t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n \<equiv> t"}
  (an equation headed by a constant @{text f} with arguments
  @{text "t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n"} and right hand side @{text t}.
  Code generation aims to turn function equations
  into a functional program by running through
  a process (see figure \ref{fig:process}):

  \begin{itemize}

    \item Out of the vast collection of theorems proven in a
      \qn{theory}, a reasonable subset modeling
      function equations is \qn{selected}.

    \item On those selected theorems, certain
      transformations are carried out
      (\qn{preprocessing}).  Their purpose is to turn theorems
      representing non- or badly executable
      specifications into equivalent but executable counterparts.
      The result is a structured collection of \qn{code theorems}.

    \item These \qn{code theorems} then are extracted
      into an Haskell-like intermediate
      language.

    \item Finally, out of the intermediate language the final
      code in the desired \qn{target language} is \qn{serialized}.

  \end{itemize}

  \begin{figure}[h]
  \centering
  \includegraphics[width=0.3\textwidth]{codegen_process}
  \caption{code generator -- processing overview}
  \label{fig:process}
  \end{figure}

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

consts
  fac :: "nat \<Rightarrow> nat"

primrec
  "fac 0 = 1"
  "fac (Suc n) = Suc n * fac n"

text {*
  This executable specification is now turned to SML code:
*}

code_gen fac (SML "examples/fac.ML")

text {*
  The \isasymCODEGEN command takes a space-seperated list of
  constants together with \qn{serialization directives}
  in parentheses. These start with a \qn{target language}
  identifer, followed by arguments, their semantics
  depending on the target. In the SML case, a filename
  is given where to write the generated code to.

  Internally, the function equations for all selected
  constants are taken, including any tranitivly required
  constants, datatypes and classes, resulting in the following
  code:

  \lstsml{Thy/examples/fac.ML}

  The code generator will complain when a required
  ingredient does not provide a executable counterpart.
  This is the case if an involved type is not a datatype:
*}

(*<*)
setup {* Sign.add_path "foo" *}
(*>*)

typedecl 'a foo

definition
  bar :: "'a foo \<Rightarrow> 'a \<Rightarrow> 'a"
  "bar x y = y"

(*<*)
hide type foo
hide const bar

setup {* Sign.parent_path *}

datatype 'a foo = Foo

definition
  bar :: "'a foo \<Rightarrow> 'a \<Rightarrow> 'a"
  "bar x y = y"
(*>*)

code_gen bar (SML "examples/fail_type.ML")

text {*
  \noindent will result in an error. Likewise, generating code
  for constants not yielding
  a function equation will fail, e.g.~the Hilbert choice
  operation @{text "SOME"}:
*}

(*<*)
setup {* Sign.add_path "foo" *}
(*>*)

definition
  pick_some :: "'a list \<Rightarrow> 'a"
  "pick_some xs = (SOME x. x \<in> set xs)"

(*<*)
hide const pick_some

setup {* Sign.parent_path *}

definition
  pick_some :: "'a list \<Rightarrow> 'a"
  "pick_some = hd"
(*>*)

code_gen pick_some (SML "examples/fail_const.ML")

subsection {* Theorem selection *}

text {*
  The list of all function equations in a theory may be inspected
  using the \isasymPRINTCODETHMS command:
*}

print_codethms

text {*
  \noindent which displays a table of constant with corresponding
  function equations (the additional stuff displayed
  shall not bother us for the moment). If this table does
  not provide at least one function
  equation, the table of primititve definitions is searched
  whether it provides one.

  The typical HOL tools are already set up in a way that
  function definitions introduced by \isasymFUN, \isasymFUNCTION,
  \isasymPRIMREC, \isasymRECDEF are implicitly propagated
  to this function equation table. Specific theorems may be
  selected using an attribute: \emph{code func}. As example,
  a weight selector function:
*}

consts
  pick :: "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> 'a"

primrec
  "pick (x#xs) n = (let (k, v) = x in
    if n < k then v else pick xs (n - k))"

text {*
  We want to eliminate the explicit destruction
  of @{term x} to @{term "(k, v)"}:
*}

lemma [code func]:
  "pick ((k, v)#xs) n = (if n < k then v else pick xs (n - k))"
  by simp

code_gen pick (SML "examples/pick1.ML")

text {*
  This theorem is now added to the function equation table:

  \lstsml{Thy/examples/pick1.ML}

  It might be convenient to remove the pointless original
  equation, using the \emph{nofunc} attribute:
*}

lemmas [code nofunc] = pick.simps 

code_gen pick (SML "examples/pick2.ML")

text {*
  \lstsml{Thy/examples/pick2.ML}

  Syntactic redundancies are implicitly dropped. For example,
  using a modified version of the @{const fac} function
  as function equation, the then redundant (since
  syntactically subsumed) original function equations
  are dropped, resulting in a warning:
*}

lemma [code func]:
  "fac n = (case n of 0 \<Rightarrow> 1 | Suc m \<Rightarrow> n * fac m)"
  by (cases n) simp_all

code_gen fac (SML "examples/fac_case.ML")

text {*
  \lstsml{Thy/examples/fac_case.ML}

  \begin{warn}
    Some statements in this section have to be treated with some
    caution. First, since the HOL function package is still
    under development, its setup with respect to code generation
    may differ from what is presumed here.
    Further, the attributes \emph{code} and \emph{code del}
    associated with the existing code generator also apply to
    the new one: \emph{code} implies \emph{code func},
    and \emph{code del} implies \emph{code nofunc}.
  \end{warn}
*}

subsection {* Type classes *}

text {*
  Type classes enter the game via the Isar class package.
  For a short introduction how to use it, see \cite{isabelle-classes};
  here we just illustrate its relation on code generation.

  In a target language, type classes may be represented
  nativly (as in the case of Haskell). For languages
  like SML, they are implemented using \emph{dictionaries}.
  Our following example specified a class \qt{null},
  assigning to each of its inhabitants a \qt{null} value:
*}

class null =
  fixes null :: 'a

consts
  head :: "'a\<Colon>null list \<Rightarrow> 'a"

primrec
  "head [] = null"
  "head (x#xs) = x"

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
  Type classes offer a suitable occassion to introduce
  the Haskell serializer.  Its usage is almost the same
  as SML, but, in accordance with conventions
  some Haskell systems enforce, each module ends
  up in a single file. The module hierarchy is reflected in
  the file system, with root given by the user.
*}

ML {* set Toplevel.debug *}
code_gen dummy (Haskell "examples/")
  (* NOTE: you may use Haskell only once in this document *)

text {*
  \lsthaskell{Thy/examples/Codegen.hs}

  (we have left out all other modules).

  The whole code in SML with explicit dictionary passing:
*}

code_gen dummy (SML "examples/class.ML")

text {*
  \lstsml{Thy/examples/class.ML}
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
  of the \isasymCODEGEN: either the list of constants or the
  list of serialization expressions may be dropped.  If no
  serialization expressions are given, only abstract code
  is generated and cached; if no constants are given, the
  current cache is serialized.

  For explorative reasons, an extended version of the
  \isasymCODEGEN command may prove useful:
*}

print_codethms ()

text {*
  \noindent print all cached function equations (i.e.~\emph{after}
  any applied transformation. Inside the brackets a
  list of constants may be given; their function
  euqations are added to the cache if not already present.
*}



section {* Recipes and advanced topics \label{sec:advanced} *}

(* no reference, IsarRef, but see paper *)

subsection {* Library theories *}

subsection {* Preprocessing *}

(* preprocessing, print_codethms () *)

subsection {* Customizing serialization  *}

(* code_reserved *)
(* existing libraries, understanding the type game, reflexive equations, code inline code_constsubst, code_abstype*)

section {* ML interfaces \label{sec:ml} *}

(* under developement *)

subsection {* codegen\_data.ML *}

subsection {* Implementing code generator applications *}

(* hooks *)

end
