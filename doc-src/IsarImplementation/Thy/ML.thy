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

text {* ML and Isar are intertwined via an open-ended bootstrap
  process that provides more and more programming facilities and
  logical content in an alternating manner.  Bootstrapping starts from
  the raw environment of existing implementations of Standard ML
  (mainly Poly/ML, but also SML/NJ).

  Isabelle/Pure marks the point where the original ML toplevel is
  superseded by the Isar toplevel that maintains a uniform environment
  for arbitrary ML values (see also \secref{sec:context}).  This
  formal context holds logical entities as well as ML compiler
  bindings, among many other things.  Raw Standard ML is never
  encountered again after the initial bootstrap of Isabelle/Pure.

  Object-logics such as Isabelle/HOL are built within the
  Isabelle/ML/Isar environment of Pure by introducing suitable
  theories with associated ML text, either inlined or as separate
  files.  Thus Isabelle/HOL is defined as a regular user-space
  application within the Isabelle framework.  Further add-on tools can
  be implemented in ML within the Isar context in the same manner: ML
  is part of the regular user-space repertoire of Isabelle.
*}


subsection {* Isar ML commands *}

text {* The primary Isar source language provides various facilities
  to open a ``window'' to the underlying ML compiler.  Especially see
  @{command_ref "use"} and @{command_ref "ML"}, which work exactly the
  same way, only the source text is provided via a file vs.\ inlined,
  respectively.  Apart from embedding ML into the main theory
  definition like that, there are many more commands that refer to ML
  source, such as @{command_ref setup} or @{command_ref declaration}.
  An example of even more fine-grained embedding of ML into Isar is
  the proof method @{method_ref tactic}, which refines the pending goal state
  via a given expression of type @{ML_type tactic}.
*}

text %mlex {* The following artificial example demonstrates some ML
  toplevel declarations within the implicit Isar theory context.  This
  is regular functional programming without referring to logical
  entities yet.
*}

ML {*
  fun factorial 0 = 1
    | factorial n = n * factorial (n - 1)
*}

text {* \noindent Here the ML environment is really managed by
  Isabelle, i.e.\ the @{ML factorial} function is not yet accessible
  in the preceding paragraph, nor in a different theory that is
  independent from the current one in the import hierarchy.

  Removing the above ML declaration from the source text will remove
  any trace of this definition as expected.  The Isabelle/ML toplevel
  environment is managed in a \emph{stateless} way: unlike the raw ML
  toplevel or similar command loops of Computer Algebra systems, there
  are no global side-effects involved here.\footnote{Such a stateless
  compilation environment is also a prerequisite for robust parallel
  compilation within independent nodes of the implicit theory
  development graph.}

  \bigskip The next example shows how to embed ML into Isar proofs.
  Instead of @{command_ref "ML"} for theory mode, we use @{command_ref
  "ML_prf"} for proof mode.  As illustrated below, its effect on the
  ML environment is local to the whole proof body, while ignoring its
  internal block structure.
*}

example_proof
  ML_prf {* val a = 1 *}
  { -- {* Isar block structure ignored by ML environment *}
    ML_prf {* val b = a + 1 *}
  } -- {* Isar block structure ignored by ML environment *}
  ML_prf {* val c = b + 1 *}
qed

text {* \noindent By side-stepping the normal scoping rules for Isar
  proof blocks, embedded ML code can refer to the different contexts
  explicitly, and manipulate corresponding entities, e.g.\ export a
  fact from a block context.

  \bigskip Two further ML commands are useful in certain situations:
  @{command_ref ML_val} and @{command_ref ML_command} are both
  \emph{diagnostic} in the sense that there is no effect on the
  underlying environment, and can thus used anywhere (even outside a
  theory).  The examples below produce long strings of digits by
  invoking @{ML factorial}: @{command ML_val} already takes care of
  printing the ML toplevel result, but @{command ML_command} is silent
  so we produce an explicit output message.
*}

ML_val {* factorial 100 *}
ML_command {* writeln (string_of_int (factorial 100)) *}

example_proof
  ML_val {* factorial 100 *}  (* FIXME check/fix indentation *)
  ML_command {* writeln (string_of_int (factorial 100)) *}
qed


subsection {* Compile-time context *}

text {* Whenever the ML compiler is invoked within Isabelle/Isar, the
  formal context is passed as a thread-local reference variable.  Thus
  ML code may access the theory context during compilation, by reading
  or writing the (local) theory under construction.  Note that such
  direct access to the compile-time context is rare; in practice it is
  typically via some derived ML functions.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML ML_Context.the_generic_context: "unit -> Context.generic"} \\
  @{index_ML "Context.>> ": "(Context.generic -> Context.generic) -> unit"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML "ML_Context.the_generic_context ()"} refers to the theory
  context of the ML toplevel --- at compile time.  ML code needs to
  take care to refer to @{ML "ML_Context.the_generic_context ()"}
  correctly.  Recall that evaluation of a function body is delayed
  until actual run-time.

  \item @{ML "Context.>>"}~@{text f} applies context transformation
  @{text f} to the implicit context of the ML toplevel.

  \end{description}

  It is very important to note that the above functions are really
  restricted to the compile time, even though the ML compiler is
  invoked at run-time.  The majority of ML code either uses static
  antiquotations (\secref{sec:ML-antiq}) or refers to the theory or
  proof context at run-time, by explicit functional abstraction.
*}


subsection {* Antiquotations \label{sec:ML-antiq} *}

text {* A very important consequence of embedding SML into Isar is the
  concept of \emph{ML antiquotation}: the standard token language of
  ML is augmented by special syntactic entities of the following form:

  \begin{rail}
  antiquote: atsign lbrace nameref args rbrace | lbracesym | rbracesym
  ;
  \end{rail}

  \noindent Here the syntax categories @{syntax nameref} and @{syntax
  args} are defined in \cite{isabelle-isar-ref}; attributes and proof
  methods use similar syntax.

  \medskip A regular antiquotation @{text "@{name args}"} processes
  its arguments by the usual means of the Isar source language, and
  produces corresponding ML source text, either as literal
  \emph{inline} text (e.g. @{text "@{term t}"}) or abstract
  \emph{value} (e.g. @{text "@{thm th}"}).  This pre-compilation
  scheme allows to refer to formal entities in a robust manner, with
  proper static scoping and with some degree of logical checking of
  small portions of the code.

  Special antiquotations like @{text "@{let \<dots>}"} or @{text "@{note
  \<dots>}"} augment the compilation context without generating code.  The
  non-ASCII braces @{text "\<lbrace>"} and @{text "\<rbrace>"} allow to delimit the
  effect by introducing local blocks within the pre-compilation
  environment.
*}

end