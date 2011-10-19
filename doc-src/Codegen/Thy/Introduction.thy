theory Introduction
imports Setup
begin

section {* Introduction *}

text {*
  This tutorial introduces the code generator facilities of @{text
  "Isabelle/HOL"}.  It allows to turn (a certain class of) HOL
  specifications into corresponding executable code in the programming
  languages @{text SML} \cite{SML}, @{text OCaml} \cite{OCaml},
  @{text Haskell} \cite{haskell-revised-report} and @{text Scala}
  \cite{scala-overview-tech-report}.

  To profit from this tutorial, some familiarity and experience with
  @{theory HOL} \cite{isa-tutorial} and its basic theories is assumed.
*}


subsection {* Code generation principle: shallow embedding \label{sec:principle} *}

text {*
  The key concept for understanding Isabelle's code generation is
  \emph{shallow embedding}: logical entities like constants, types and
  classes are identified with corresponding entities in the target
  language.  In particular, the carrier of a generated program's
  semantics are \emph{equational theorems} from the logic.  If we view
  a generated program as an implementation of a higher-order rewrite
  system, then every rewrite step performed by the program can be
  simulated in the logic, which guarantees partial correctness
  \cite{Haftmann-Nipkow:2010:code}.
*}


subsection {* A quick start with the Isabelle/HOL toolbox \label{sec:queue_example} *}

text {*
  In a HOL theory, the @{command_def datatype} and @{command_def
  definition}/@{command_def primrec}/@{command_def fun} declarations
  form the core of a functional programming language.  By default
  equational theorems stemming from those are used for generated code,
  therefore \qt{naive} code generation can proceed without further
  ado.

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
      (case rev xs of y # ys \<Rightarrow> (Some y, AQueue [] ys))" (*<*)

lemma %invisible dequeue_nonempty_Nil [simp]:
  "xs \<noteq> [] \<Longrightarrow> dequeue (AQueue xs []) = (case rev xs of y # ys \<Rightarrow> (Some y, AQueue [] ys))"
  by (cases xs) (simp_all split: list.splits) (*>*)

text {* \noindent Then we can generate code e.g.~for @{text SML} as follows: *}

export_code %quote empty dequeue enqueue in SML
  module_name Example file "examples/example.ML"

text {* \noindent resulting in the following code: *}

text %quotetypewriter {*
  @{code_stmts empty enqueue dequeue (SML)}
*}

text {*
  \noindent The @{command_def export_code} command takes a
  space-separated list of constants for which code shall be generated;
  anything else needed for those is added implicitly.  Then follows a
  target language identifier and a freely chosen module name.  A file
  name denotes the destination to store the generated code.  Note that
  the semantics of the destination depends on the target language: for
  @{text SML}, @{text OCaml} and @{text Scala} it denotes a \emph{file},
  for @{text Haskell} it denotes a \emph{directory} where a file named as the
  module name (with extension @{text ".hs"}) is written:
*}

export_code %quote empty dequeue enqueue in Haskell
  module_name Example file "examples/"

text {*
  \noindent This is the corresponding code:
*}

text %quotetypewriter {*
  @{code_stmts empty enqueue dequeue (Haskell)}
*}

text {*
  \noindent For more details about @{command export_code} see
  \secref{sec:further}.
*}


subsection {* Type classes *}

text {*
  Code can also be generated from type classes in a Haskell-like
  manner.  For illustration here an example from abstract algebra:
*}

class %quote semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class %quote monoid = semigroup +
  fixes neutral :: 'a ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"
    and neutr: "x \<otimes> \<one> = x"

instantiation %quote nat :: monoid
begin

primrec %quote mult_nat where
    "0 \<otimes> n = (0\<Colon>nat)"
  | "Suc m \<otimes> n = n + m \<otimes> n"

definition %quote neutral_nat where
  "\<one> = Suc 0"

lemma %quote add_mult_distrib:
  fixes n m q :: nat
  shows "(n + m) \<otimes> q = n \<otimes> q + m \<otimes> q"
  by (induct n) simp_all

instance %quote proof
  fix m n q :: nat
  show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
    by (induct m) (simp_all add: add_mult_distrib)
  show "\<one> \<otimes> n = n"
    by (simp add: neutral_nat_def)
  show "m \<otimes> \<one> = m"
    by (induct m) (simp_all add: neutral_nat_def)
qed

end %quote

text {*
  \noindent We define the natural operation of the natural numbers
  on monoids:
*}

primrec %quote (in monoid) pow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
    "pow 0 a = \<one>"
  | "pow (Suc n) a = a \<otimes> pow n a"

text {*
  \noindent This we use to define the discrete exponentiation
  function:
*}

definition %quote bexp :: "nat \<Rightarrow> nat" where
  "bexp n = pow n (Suc (Suc 0))"

text {*
  \noindent The corresponding code in Haskell uses that language's
  native classes:
*}

text %quotetypewriter {*
  @{code_stmts bexp (Haskell)}
*}

text {*
  \noindent This is a convenient place to show how explicit dictionary
  construction manifests in generated code -- the same example in
  @{text SML}:
*}

text %quotetypewriter {*
  @{code_stmts bexp (SML)}
*}

text {*
  \noindent Note the parameters with trailing underscore (@{verbatim
  "A_"}), which are the dictionary parameters.
*}


subsection {* How to continue from here *}

text {*
  What you have seen so far should be already enough in a lot of
  cases.  If you are content with this, you can quit reading here.

  Anyway, to understand situations where problems occur or to increase
  the scope of code generation beyond default, it is necessary to gain
  some understanding how the code generator actually works:

  \begin{itemize}

    \item The foundations of the code generator are described in
      \secref{sec:foundations}.

    \item In particular \secref{sec:utterly_wrong} gives hints how to
      debug situations where code generation does not succeed as
      expected.

    \item The scope and quality of generated code can be increased
      dramatically by applying refinement techniques, which are
      introduced in \secref{sec:refinement}.

    \item Inductive predicates can be turned executable using an
      extension of the code generator \secref{sec:inductive}.

    \item If you want to utilize code generation to obtain fast
      evaluators e.g.~for decision procedures, have a look at
      \secref{sec:evaluation}.

    \item You may want to skim over the more technical sections
      \secref{sec:adaptation} and \secref{sec:further}.

    \item The target language Scala \cite{scala-overview-tech-report}
      comes with some specialities discussed in \secref{sec:scala}.

    \item For exhaustive syntax diagrams etc. you should visit the
      Isabelle/Isar Reference Manual \cite{isabelle-isar-ref}.

  \end{itemize}

  \bigskip

  \begin{center}\fbox{\fbox{\begin{minipage}{8cm}

    \begin{center}\textit{Happy proving, happy hacking!}\end{center}

  \end{minipage}}}\end{center}
*}

end
