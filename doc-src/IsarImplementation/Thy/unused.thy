
section {* Sessions and document preparation *}

section {* Structured output *}

subsection {* Pretty printing *}

text FIXME

subsection {* Output channels *}

text FIXME

subsection {* Print modes \label{sec:print-mode} *}

text FIXME

text {*


  \medskip The general concept supports block-structured reasoning
  nicely, with arbitrary mechanisms for introducing local assumptions.
  The common reasoning pattern is as follows:

  \medskip
  \begin{tabular}{l}
  @{text "add_assms e\<^isub>1 A\<^isub>1"} \\
  @{text "\<dots>"} \\
  @{text "add_assms e\<^isub>n A\<^isub>n"} \\
  @{text "export"} \\
  \end{tabular}
  \medskip

  \noindent The final @{text "export"} will turn any fact @{text
  "A\<^isub>1, \<dots>, A\<^isub>n \<turnstile> B"} into some @{text "\<turnstile> B'"}, by
  applying the export rules @{text "e\<^isub>1, \<dots>, e\<^isub>n"}
  inside-out.
  

  A \emph{fixed variable} acts like a local constant in the current
  context, representing some simple type @{text "\<alpha>"}, or some value
  @{text "x: \<tau>"} (for a fixed type expression @{text "\<tau>"}).  A
  \emph{schematic variable} acts like a placeholder for arbitrary
  elements, similar to outermost quantification.  The division between
  fixed and schematic variables tells which abstract entities are
  inside and outside the current context.


  @{index_ML Variable.trade: "Proof.context -> (thm list -> thm list) -> thm list -> thm list"} \\



  \item @{ML Variable.trade} composes @{ML Variable.import} and @{ML
  Variable.export}, i.e.\ it provides a view on facts with all
  variables being fixed in the current context.


  In practice, super-contexts emerge either by merging existing ones,
  or by adding explicit declarations.  For example, new theories are
  usually derived by importing existing theories from the library
  @{text "\<Theta> = \<Theta>\<^sub>1 + \<dots> + \<Theta>\<^isub>n"}, or 



  The Isar toplevel works differently for interactive developments
  vs.\ batch processing of theory sources.  For example, diagnostic
  commands produce a warning batch mode, because they are considered
  alien to the final theory document being produced eventually.
  Moreover, full @{text undo} with intermediate checkpoints to protect
  against destroying theories accidentally are limited to interactive
  mode.  In batch mode there is only a single strictly linear stream
  of potentially desctructive theory transformations.

  \item @{ML Toplevel.empty} is an empty transition; the Isar command
  dispatcher internally applies @{ML Toplevel.name} (for the command)
  name and @{ML Toplevel.position} for the source position.

*}

