
text {*

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

