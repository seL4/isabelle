theory Introduction
imports Setup
begin

section {* Introduction and Overview *}

text {*
  This tutorial introduces a generic code generator for the
  @{text Isabelle} system.
  Generic in the sense that the
  \qn{target language} for which code shall ultimately be
  generated is not fixed but may be an arbitrary state-of-the-art
  functional programming language (currently, the implementation
  supports @{text SML} \cite{SML}, @{text OCaml} \cite{OCaml} and @{text Haskell}
  \cite{haskell-revised-report}).

  Conceptually the code generator framework is part
  of Isabelle's @{theory Pure} meta logic framework; the logic
  @{theory HOL} which is an extension of @{theory Pure}
  already comes with a reasonable framework setup and thus provides
  a good working horse for raising code-generation-driven
  applications.  So, we assume some familiarity and experience
  with the ingredients of the @{theory HOL} distribution theories.
  (see also \cite{isa-tutorial}).

  The code generator aims to be usable with no further ado
  in most cases while allowing for detailed customisation.
  This manifests in the structure of this tutorial: after a short
  conceptual introduction with an example (\secref{sec:intro}),
  we discuss the generic customisation facilities (\secref{sec:program}).
  A further section (\secref{sec:adaptation}) is dedicated to the matter of
  \qn{adaptation} to specific target language environments.  After some
  further issues (\secref{sec:further}) we conclude with an overview
  of some ML programming interfaces (\secref{sec:ml}).

  \begin{warn}
    Ultimately, the code generator which this tutorial deals with
    is supposed to replace the existing code generator
    by Stefan Berghofer \cite{Berghofer-Nipkow:2002}.
    So, for the moment, there are two distinct code generators
    in Isabelle.  In case of ambiguity, we will refer to the framework
    described here as @{text "generic code generator"}, to the
    other as @{text "SML code generator"}.
    Also note that while the framework itself is
    object-logic independent, only @{theory HOL} provides a reasonable
    framework setup.    
  \end{warn}

*}

subsection {* Code generation via shallow embedding \label{sec:intro} *}

text {*
  The key concept for understanding @{text Isabelle}'s code generation is
  \emph{shallow embedding}, i.e.~logical entities like constants, types and
  classes are identified with corresponding concepts in the target language.

  Inside @{theory HOL}, the @{command datatype} and
  @{command definition}/@{command primrec}/@{command fun} declarations form
  the core of a functional programming language.  The default code generator setup
  allows to turn those into functional programs immediately.
  This means that \qt{naive} code generation can proceed without further ado.
  For example, here a simple \qt{implementation} of amortised queues:
*}

datatype %quote 'a queue = AQueue "'a list" "'a list"

definition %quote empty :: "'a queue" where
  "empty = AQueue [] []"

primrec %quote enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x (AQueue xs ys) = AQueue (x # xs) ys"

fun %quote dequeue :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
    "dequeue (AQueue [] []) = (None, AQueue [] [])"
  | "dequeue (AQueue xs (y # ys)) = (Some y, AQueue xs ys)"
  | "dequeue (AQueue xs []) =
      (case rev xs of y # ys \<Rightarrow> (Some y, AQueue [] ys))"

text {* \noindent Then we can generate code e.g.~for @{text SML} as follows: *}

export_code %quote empty dequeue enqueue in SML
  module_name Example file "examples/example.ML"

text {* \noindent resulting in the following code: *}

text %quote {*@{code_stmts empty enqueue dequeue (SML)}*}

text {*
  \noindent The @{command export_code} command takes a space-separated list of
  constants for which code shall be generated;  anything else needed for those
  is added implicitly.  Then follows a target language identifier
  (@{text SML}, @{text OCaml} or @{text Haskell}) and a freely chosen module name.
  A file name denotes the destination to store the generated code.  Note that
  the semantics of the destination depends on the target language:  for
  @{text SML} and @{text OCaml} it denotes a \emph{file}, for @{text Haskell}
  it denotes a \emph{directory} where a file named as the module name
  (with extension @{text ".hs"}) is written:
*}

export_code %quote empty dequeue enqueue in Haskell
  module_name Example file "examples/"

text {*
  \noindent This is how the corresponding code in @{text Haskell} looks like:
*}

text %quote {*@{code_stmts empty enqueue dequeue (Haskell)}*}

text {*
  \noindent This demonstrates the basic usage of the @{command export_code} command;
  for more details see \secref{sec:further}.
*}

subsection {* Code generator architecture \label{sec:concept} *}

text {*
  What you have seen so far should be already enough in a lot of cases.  If you
  are content with this, you can quit reading here.  Anyway, in order to customise
  and adapt the code generator, it is inevitable to gain some understanding
  how it works.

  \begin{figure}[h]
    \includegraphics{architecture}
    \caption{Code generator architecture}
    \label{fig:arch}
  \end{figure}

  The code generator employs a notion of executability
  for three foundational executable ingredients known
  from functional programming:
  \emph{code equations}, \emph{datatypes}, and
  \emph{type classes}.  A code equation as a first approximation
  is a theorem of the form @{text "f t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n \<equiv> t"}
  (an equation headed by a constant @{text f} with arguments
  @{text "t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n"} and right hand side @{text t}).
  Code generation aims to turn code equations
  into a functional program.  This is achieved by three major
  components which operate sequentially, i.e. the result of one is
  the input
  of the next in the chain,  see figure \ref{fig:arch}:

  \begin{itemize}

    \item Starting point is a collection of raw code equations in a
      theory; due to proof irrelevance it is not relevant where they
      stem from but typically they are either descendant of specification
      tools or explicit proofs by the user.
      
    \item Before these raw code equations are continued
      with, they can be subjected to theorem transformations.  This
      \qn{preprocessor} is an interface which allows to apply the full
      expressiveness of ML-based theorem transformations to code
      generation.  The result of the preprocessing step is a
      structured collection of code equations.

    \item These code equations are \qn{translated} to a program in an
      abstract intermediate language.  Think of it as a kind
      of \qt{Mini-Haskell} with four \qn{statements}: @{text data}
      (for datatypes), @{text fun} (stemming from code equations),
      also @{text class} and @{text inst} (for type classes).

    \item Finally, the abstract program is \qn{serialised} into concrete
      source code of a target language.
      This step only produces concrete syntax but does not change the
      program in essence; all conceptual transformations occur in the
      translation step.

  \end{itemize}

  \noindent From these steps, only the two last are carried out outside the logic;  by
  keeping this layer as thin as possible, the amount of code to trust is
  kept to a minimum.
*}

end
