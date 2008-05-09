(* $Id$ *)

theory Spec
imports Main
begin

chapter {* Specifications *}

section {* Defining theories \label{sec:begin-thy} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "header"} & : & \isarkeep{toplevel} \\
    @{command_def "theory"} & : & \isartrans{toplevel}{theory} \\
    @{command_def "end"} & : & \isartrans{theory}{toplevel} \\
  \end{matharray}

  Isabelle/Isar theories are defined via theory, which contain both
  specifications and proofs; occasionally definitional mechanisms also
  require some explicit proof.

  The first ``real'' command of any theory has to be @{command
  "theory"}, which starts a new theory based on the merge of existing
  ones.  Just preceding the @{command "theory"} keyword, there may be
  an optional @{command "header"} declaration, which is relevant to
  document preparation only; it acts very much like a special
  pre-theory markup command (cf.\ \secref{sec:markup-thy} and
  \secref{sec:markup-thy}).  The @{command "end"} command concludes a
  theory development; it has to be the very last command of any theory
  file loaded in batch-mode.

  \begin{rail}
    'header' text
    ;
    'theory' name 'imports' (name +) uses? 'begin'
    ;

    uses: 'uses' ((name | parname) +);
  \end{rail}

  \begin{descr}

  \item [@{command "header"}~@{text "text"}] provides plain text
  markup just preceding the formal beginning of a theory.  In actual
  document preparation the corresponding {\LaTeX} macro @{verbatim
  "\\isamarkupheader"} may be redefined to produce chapter or section
  headings.  See also \secref{sec:markup-thy} and
  \secref{sec:markup-prf} for further markup commands.
  
  \item [@{command "theory"}~@{text "A \<IMPORTS> B\<^sub>1 \<dots>
  B\<^sub>n \<BEGIN>"}] starts a new theory @{text A} based on the
  merge of existing theories @{text "B\<^sub>1 \<dots> B\<^sub>n"}.
  
  Due to inclusion of several ancestors, the overall theory structure
  emerging in an Isabelle session forms a directed acyclic graph
  (DAG).  Isabelle's theory loader ensures that the sources
  contributing to the development graph are always up-to-date.
  Changed files are automatically reloaded when processing theory
  headers.
  
  The optional @{keyword_def "uses"} specification declares additional
  dependencies on extra files (usually ML sources).  Files will be
  loaded immediately (as ML), unless the name is put in parentheses,
  which merely documents the dependency to be resolved later in the
  text (typically via explicit @{command_ref "use"} in the body text,
  see \secref{sec:ML}).
  
  \item [@{command "end"}] concludes the current theory definition or
  context switch.

  \end{descr}
*}

end
