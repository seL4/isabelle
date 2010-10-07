theory "ML"
imports Base
begin

chapter {* Isabelle/ML *}

text {* Isabelle/ML is best understood as a certain culture based on
  Standard ML.  Thus it is not a new programming language, but a
  certain way to use SML at an advanced level within the Isabelle
  environment.  This covers a variety of aspects that are geared
  towards an efficient and robust platform for applications of formal
  logic with fully foundational proof construction --- according to
  the well-known \emph{LCF principle}.  There are specific library
  modules and infrastructure to address the needs for such difficult
  tasks.  For example, the raw parallel programming model of Poly/ML
  is presented as considerably more abstract concept of \emph{future
  values}, which is then used to augment the inference kernel, proof
  interpreter, and theory loader accordingly.

  The main aspects of Isabelle/ML are introduced below.  These
  first-hand explanations should help to understand how proper
  Isabelle/ML is to be read and written, and to get access to the
  wealth of experience that is expressed in the source text and its
  history of changes.\footnote{See
  \url{http://isabelle.in.tum.de/repos/isabelle} for the full
  Mercurial history.  There are symbolic tags to refer to official
  Isabelle releases, as opposed to arbitrary \emph{tip} versions that
  merely reflect snapshots that are never really up-to-date.}  *}


section {* SML embedded into Isabelle/Isar *}

text {* ML and Isabelle/Isar are intertwined via an open-ended
  bootstrap process that provides more and more programming facilities
  and logical content in an alternating manner.  Bootstrapping starts
  from the raw environment of existing implementations of Standard ML
  (most notably Poly/ML but also SML/NJ).  Isabelle/Pure marks the
  point where the original ML toplevel is superseded by the Isar
  toplevel that maintains a uniform environment for arbitrary ML
  values (see also \secref{sec:context}).  This formal context holds
  logical entities as well as ML compiler bindings, among many other
  things.

  Object-logics, such as Isabelle/HOL, are built within the
  Isabelle/ML/Isar environment of Pure by introducing suitable
  theories with associated ML text (either inlined or as separate
  files).

  Implementing tools within the Isabelle framework means to work with
  ML within the Isar context in the same manner: raw Standard ML is
  normally never encountered again.
*}

section {* Isar ML commands *}

text {* The primary Isar source language provides various facilities
  to open a ``window'' to the underlying ML compiler.  Especially see
  @{command_ref "use"} and @{command_ref "ML"} in
  \cite{isabelle-isar-ref} --- both commands are exactly the same,
  only the source text is provided via a file vs.\ inlined,
  respectively.  *}

text %mlex {* The following artificial example demonstrates basic ML
  programming within the implicit Isar theory context, without
  referring to logical entities yet.
*}

ML {*
  fun factorial 0 = 1
    | factorial n = n * factorial (n - 1)
*}

text {* \noindent The ML binding of @{ML factorial} is really managed
  by the Isabelle environment, i.e.\ that function is not yet
  accessible in the preceding paragraph, nor in a different theory
  that is independent from the current one in the import hierarchy.

  Removing the above ML declaration from the source text will remove
  any trace of this definition as expected.  The Isabelle/ML toplevel
  environment is managed in a \emph{stateless} way: unlike the raw ML
  toplevel, there are no global side-effects involved.

  \bigskip The next example shows how to embed ML into Isar proofs.
  Instead of @{command_ref "ML"} for theory text, we use @{command_ref
  "ML_prf"}: its effect on the ML environment is local to the whole
  proof body, while ignoring its internal block structure.  *}

example_proof
  ML_prf {* val a = 1 *}
  { -- {* proof block ignored by ML environment *}
    ML_prf {* val b = a + 1 *}
  } -- {* proof block ignored by ML environment *}
  ML_prf {* val c = b + 1 *}
qed

text {* \noindent By side-stepping the normal Isar scoping rules,
  embedded ML code can refer to the different contexts explicitly, and
  manipulate corresponding entities, e.g.\ export a fact from a
  block context.

  \bigskip The diagnostic ML commands @{command_ref ML_val} and
  @{command_ref ML_command} do not affect the underlying context, and
  can be used anywhere, e.g.\ to produce long strings of digits as
  follows: *}

ML_val {* factorial 100 *}
ML_command {* writeln (string_of_int (factorial 100)) *}

example_proof
  ML_val {* factorial 100 *}
  ML_command {* writeln (string_of_int (factorial 100)) *}
qed

text {* \noindent Note that @{command ML_val} and @{command
  ML_command} only differ in the output (or lack thereof) of ML
  toplevel results. *}


section {* Compile-time context *}

text FIXME


section {* Antiquotations *}

text FIXME


end