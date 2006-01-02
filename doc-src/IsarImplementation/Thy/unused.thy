
text {*
  The Isar toplevel works differently for interactive developments
  vs.\ batch processing of theory sources.  For example, diagnostic
  commands produce a warning batch mode, because they are considered
  alien to the final theory document being produced eventually.
  Moreover, full @{text undo} with intermediate checkpoints to protect
  against destroying theories accidentally are limited to interactive
  mode.  In batch mode there is only a single strictly linear stream
  of potentially desctructive theory transformations.
*}

  \item @{ML Toplevel.empty} is an empty transition; the Isar command
  dispatcher internally applies @{ML Toplevel.name} (for the command)
  name and @{ML Toplevel.position} for the source position.

